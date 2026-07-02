//! The one-shot solver interface and the P1 pipeline dispatcher (DES-012).
//!
//! Callers (loom, synth) build a conjunction of asserted [`BoolTerm`]s and call
//! [`Solver::check`]. The result is one of:
//!
//! - [`CheckResult::Unsat`] — the assertions are unsatisfiable, carrying an
//!   (eventually machine-checkable) [`Certificate`]. For an equivalence query
//!   this is the "equivalence holds" verdict.
//! - [`CheckResult::Sat`] — the assertions are satisfiable, carrying a
//!   counterexample [`Model`] that has been **self-checked** by re-evaluating
//!   it against every assertion with the concrete evaluator.
//! - [`CheckResult::Unknown`] — the solver could not decide, would not stand
//!   behind its answer, or the query uses a disabled operation.
//!
//! # Soundness contract for callers
//!
//! `Unknown` MUST be treated **conservatively**: loom/synth must NOT apply the
//! optimization / accept the codegen when they receive `Unknown`. Only a
//! checked `Unsat` certificate authorizes a transformation.
//!
//! # P1 pipeline status
//!
//! `check` runs blast → AIG → Tseitin CNF → CDCL. On SAT it returns a
//! self-checked model. On UNSAT the engine's verdict is **believed but not
//! yet checked** (ROADMAP P1), so the production path returns `Unknown` —
//! never an unchecked `Unsat` (AGENTS.md rule 1). The raw engine verdict is
//! exposed crate-internally for the differential oracle only. P2 wires LRAT
//! emission + the verified checker, at which point `Unsat` becomes reachable.
//!
//! # The op-enablement gate (P1 kill criterion)
//!
//! Every operation's blasting rule ships oracle-verified (UV-005..UV-009).
//! If the differential oracle ever finds a disagreement, that op is added to
//! [`DISABLED_OPS`] and every query containing it returns `Unknown` until
//! the rule is fixed — the solver reverts to conservative, never guesses.

use crate::aig::{Aig, Lit, Word, word_input};
use crate::blast::{arith, bitwise, muldiv, shift, structural};
use crate::cnf::tseitin;
use crate::eval::{self, Env, EvalError};
use crate::sat::{SatResult, SatSolver};
use crate::term::{BoolTerm, BvTerm};
use std::collections::HashMap;

/// A machine-checkable UNSAT certificate.
///
/// The solver (untrusted) emits an LRAT proof; the formally-verified checker
/// (the only trusted component) validates it. Empty until phase P2 wires up
/// LRAT emission — see `ROADMAP.md`.
#[derive(Clone, Debug, Default)]
pub struct Certificate {
    /// The LRAT proof bytes. Empty until P2.
    pub lrat: Vec<u8>,
}

/// A satisfying assignment (counterexample) for a SAT query.
///
/// Each entry binds a variable name to the concrete bitvector value (as a
/// `u128`, zero-extended for widths below 128) that witnesses satisfiability.
#[derive(Clone, Debug, Default)]
pub struct Model {
    /// Variable-name → value assignments.
    pub assignments: Vec<(String, u128)>,
}

/// The verdict of a one-shot `check`.
#[derive(Clone, Debug)]
pub enum CheckResult {
    /// Unsatisfiable, with a certificate the verified checker validated.
    /// Unreachable until P2 (see module docs).
    Unsat(Certificate),
    /// Satisfiable, with a self-checked counterexample model.
    Sat(Model),
    /// Undecided.
    ///
    /// Callers MUST treat this conservatively: do NOT optimize / do NOT accept
    /// the transformation. See the module-level soundness contract.
    Unknown,
}

/// The engine's raw belief, before the soundness gate. Crate-internal: only
/// the differential oracle may look at this (an unchecked `Unsat` must never
/// reach a caller).
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum RawVerdict {
    Sat(Env),
    Unsat,
    Unknown,
}

/// Operations currently disabled by the P1 kill criterion (oracle
/// disagreement ⇒ the op reverts to `Unknown` until its rule is fixed).
/// Op names use the SMT-LIB mnemonics from `OpKind`.
const DISABLED_OPS: &[OpKind] = &[];

/// Every operation in the closed fragment, for the enablement gate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum OpKind {
    Add,
    Sub,
    Mul,
    Udiv,
    And,
    Or,
    Xor,
    Shl,
    Lshr,
    Ashr,
    Rotr,
    Extract,
    Concat,
    ZeroExt,
    SignExt,
    Eq,
    Ne,
    Ult,
    Ule,
    Ugt,
    Uge,
    Slt,
    Sle,
    Sgt,
    Sge,
    BoolNot,
    BoolAnd,
    BoolOr,
}

fn bv_op(term: &BvTerm) -> Option<OpKind> {
    Some(match term {
        BvTerm::Const { .. } | BvTerm::Var { .. } => return None,
        BvTerm::Add(..) => OpKind::Add,
        BvTerm::Sub(..) => OpKind::Sub,
        BvTerm::Mul(..) => OpKind::Mul,
        BvTerm::Udiv(..) => OpKind::Udiv,
        BvTerm::And(..) => OpKind::And,
        BvTerm::Or(..) => OpKind::Or,
        BvTerm::Xor(..) => OpKind::Xor,
        BvTerm::Shl(..) => OpKind::Shl,
        BvTerm::Lshr(..) => OpKind::Lshr,
        BvTerm::Ashr(..) => OpKind::Ashr,
        BvTerm::Rotr(..) => OpKind::Rotr,
        BvTerm::Extract { .. } => OpKind::Extract,
        BvTerm::Concat(..) => OpKind::Concat,
        BvTerm::ZeroExt { .. } => OpKind::ZeroExt,
        BvTerm::SignExt { .. } => OpKind::SignExt,
    })
}

fn bv_uses_disabled(term: &BvTerm) -> bool {
    if bv_op(term).is_some_and(|op| DISABLED_OPS.contains(&op)) {
        return true;
    }
    match term {
        BvTerm::Const { .. } | BvTerm::Var { .. } => false,
        BvTerm::Add(a, b)
        | BvTerm::Sub(a, b)
        | BvTerm::Mul(a, b)
        | BvTerm::Udiv(a, b)
        | BvTerm::And(a, b)
        | BvTerm::Or(a, b)
        | BvTerm::Xor(a, b)
        | BvTerm::Shl(a, b)
        | BvTerm::Lshr(a, b)
        | BvTerm::Ashr(a, b)
        | BvTerm::Rotr(a, b)
        | BvTerm::Concat(a, b) => bv_uses_disabled(a) || bv_uses_disabled(b),
        BvTerm::Extract { arg, .. } | BvTerm::ZeroExt { arg, .. } | BvTerm::SignExt { arg, .. } => {
            bv_uses_disabled(arg)
        }
    }
}

fn bool_uses_disabled(term: &BoolTerm) -> bool {
    let (op, kids_disabled) = match term {
        BoolTerm::Eq(a, b) => (OpKind::Eq, bv_uses_disabled(a) || bv_uses_disabled(b)),
        BoolTerm::Ne(a, b) => (OpKind::Ne, bv_uses_disabled(a) || bv_uses_disabled(b)),
        BoolTerm::Ult(a, b) => (OpKind::Ult, bv_uses_disabled(a) || bv_uses_disabled(b)),
        BoolTerm::Ule(a, b) => (OpKind::Ule, bv_uses_disabled(a) || bv_uses_disabled(b)),
        BoolTerm::Ugt(a, b) => (OpKind::Ugt, bv_uses_disabled(a) || bv_uses_disabled(b)),
        BoolTerm::Uge(a, b) => (OpKind::Uge, bv_uses_disabled(a) || bv_uses_disabled(b)),
        BoolTerm::Slt(a, b) => (OpKind::Slt, bv_uses_disabled(a) || bv_uses_disabled(b)),
        BoolTerm::Sle(a, b) => (OpKind::Sle, bv_uses_disabled(a) || bv_uses_disabled(b)),
        BoolTerm::Sgt(a, b) => (OpKind::Sgt, bv_uses_disabled(a) || bv_uses_disabled(b)),
        BoolTerm::Sge(a, b) => (OpKind::Sge, bv_uses_disabled(a) || bv_uses_disabled(b)),
        BoolTerm::Not(t) => (OpKind::BoolNot, bool_uses_disabled(t)),
        BoolTerm::And(a, b) => (
            OpKind::BoolAnd,
            bool_uses_disabled(a) || bool_uses_disabled(b),
        ),
        BoolTerm::Or(a, b) => (
            OpKind::BoolOr,
            bool_uses_disabled(a) || bool_uses_disabled(b),
        ),
    };
    DISABLED_OPS.contains(&op) || kids_disabled
}

/// Blasting context: variable words are shared across assertions by name.
struct Blaster {
    aig: Aig,
    vars: HashMap<String, Word>,
    /// Input-creation order, for model decoding.
    var_order: Vec<(String, u32)>,
}

impl Blaster {
    fn new() -> Self {
        Blaster {
            aig: Aig::new(),
            vars: HashMap::new(),
            var_order: Vec::new(),
        }
    }

    fn var_word(&mut self, name: &str, width: u32) -> Word {
        if let Some(w) = self.vars.get(name) {
            return w.clone();
        }
        let w = word_input(&mut self.aig, width);
        self.vars.insert(name.to_string(), w.clone());
        self.var_order.push((name.to_string(), width));
        w
    }

    fn blast_bv(&mut self, term: &BvTerm) -> Result<Word, EvalError> {
        // Sort-check once at the top of each recursion step; this also
        // rejects width mismatches before any rule sees them.
        let width = eval::bv_sort(term)?.width;
        Ok(match term {
            BvTerm::Const { value, .. } => crate::aig::word_const(*value, width),
            BvTerm::Var { name, .. } => self.var_word(name, width),
            BvTerm::Add(a, b) => {
                let (wa, wb) = (self.blast_bv(a)?, self.blast_bv(b)?);
                arith::blast_add(&mut self.aig, &wa, &wb)
            }
            BvTerm::Sub(a, b) => {
                let (wa, wb) = (self.blast_bv(a)?, self.blast_bv(b)?);
                arith::blast_sub(&mut self.aig, &wa, &wb)
            }
            BvTerm::Mul(a, b) => {
                let (wa, wb) = (self.blast_bv(a)?, self.blast_bv(b)?);
                muldiv::blast_mul(&mut self.aig, &wa, &wb)
            }
            BvTerm::Udiv(a, b) => {
                let (wa, wb) = (self.blast_bv(a)?, self.blast_bv(b)?);
                muldiv::blast_udiv(&mut self.aig, &wa, &wb)
            }
            BvTerm::And(a, b) => {
                let (wa, wb) = (self.blast_bv(a)?, self.blast_bv(b)?);
                bitwise::blast_and(&mut self.aig, &wa, &wb)
            }
            BvTerm::Or(a, b) => {
                let (wa, wb) = (self.blast_bv(a)?, self.blast_bv(b)?);
                bitwise::blast_or(&mut self.aig, &wa, &wb)
            }
            BvTerm::Xor(a, b) => {
                let (wa, wb) = (self.blast_bv(a)?, self.blast_bv(b)?);
                bitwise::blast_xor(&mut self.aig, &wa, &wb)
            }
            BvTerm::Shl(a, b) => {
                let (wa, wb) = (self.blast_bv(a)?, self.blast_bv(b)?);
                shift::blast_shl(&mut self.aig, &wa, &wb)
            }
            BvTerm::Lshr(a, b) => {
                let (wa, wb) = (self.blast_bv(a)?, self.blast_bv(b)?);
                shift::blast_lshr(&mut self.aig, &wa, &wb)
            }
            BvTerm::Ashr(a, b) => {
                let (wa, wb) = (self.blast_bv(a)?, self.blast_bv(b)?);
                shift::blast_ashr(&mut self.aig, &wa, &wb)
            }
            BvTerm::Rotr(a, b) => {
                let (wa, wb) = (self.blast_bv(a)?, self.blast_bv(b)?);
                shift::blast_rotr(&mut self.aig, &wa, &wb)
            }
            BvTerm::Extract { hi, lo, arg } => {
                let w = self.blast_bv(arg)?;
                structural::blast_extract(&w, *hi, *lo)
            }
            BvTerm::Concat(a, b) => {
                let (wa, wb) = (self.blast_bv(a)?, self.blast_bv(b)?);
                structural::blast_concat(&wa, &wb)
            }
            BvTerm::ZeroExt { by, arg } => {
                let w = self.blast_bv(arg)?;
                structural::blast_zero_ext(&w, *by)
            }
            BvTerm::SignExt { by, arg } => {
                let w = self.blast_bv(arg)?;
                structural::blast_sign_ext(&w, *by)
            }
        })
    }

    fn blast_bool(&mut self, term: &BoolTerm) -> Result<Lit, EvalError> {
        Ok(match term {
            BoolTerm::Eq(a, b) => {
                let (wa, wb) = (self.blast_bv(a)?, self.blast_bv(b)?);
                bitwise::blast_eq(&mut self.aig, &wa, &wb)
            }
            BoolTerm::Ne(a, b) => {
                let (wa, wb) = (self.blast_bv(a)?, self.blast_bv(b)?);
                bitwise::blast_ne(&mut self.aig, &wa, &wb)
            }
            BoolTerm::Ult(a, b) => {
                let (wa, wb) = (self.blast_bv(a)?, self.blast_bv(b)?);
                arith::blast_ult(&mut self.aig, &wa, &wb)
            }
            BoolTerm::Ule(a, b) => {
                let (wa, wb) = (self.blast_bv(a)?, self.blast_bv(b)?);
                arith::blast_ule(&mut self.aig, &wa, &wb)
            }
            BoolTerm::Ugt(a, b) => {
                let (wa, wb) = (self.blast_bv(a)?, self.blast_bv(b)?);
                arith::blast_ugt(&mut self.aig, &wa, &wb)
            }
            BoolTerm::Uge(a, b) => {
                let (wa, wb) = (self.blast_bv(a)?, self.blast_bv(b)?);
                arith::blast_uge(&mut self.aig, &wa, &wb)
            }
            BoolTerm::Slt(a, b) => {
                let (wa, wb) = (self.blast_bv(a)?, self.blast_bv(b)?);
                arith::blast_slt(&mut self.aig, &wa, &wb)
            }
            BoolTerm::Sle(a, b) => {
                let (wa, wb) = (self.blast_bv(a)?, self.blast_bv(b)?);
                arith::blast_sle(&mut self.aig, &wa, &wb)
            }
            BoolTerm::Sgt(a, b) => {
                let (wa, wb) = (self.blast_bv(a)?, self.blast_bv(b)?);
                arith::blast_sgt(&mut self.aig, &wa, &wb)
            }
            BoolTerm::Sge(a, b) => {
                let (wa, wb) = (self.blast_bv(a)?, self.blast_bv(b)?);
                arith::blast_sge(&mut self.aig, &wa, &wb)
            }
            BoolTerm::Not(t) => self.blast_bool(t)?.not(),
            BoolTerm::And(a, b) => {
                let (la, lb) = (self.blast_bool(a)?, self.blast_bool(b)?);
                self.aig.and(la, lb)
            }
            BoolTerm::Or(a, b) => {
                let (la, lb) = (self.blast_bool(a)?, self.blast_bool(b)?);
                self.aig.or(la, lb)
            }
        })
    }
}

/// A one-shot QF_BV solver over the closed loom #246 fragment.
///
/// Build up assertions with [`Solver::assert`], then call [`Solver::check`].
/// The solver is single-use in spirit (no incremental push/pop) matching the
/// scope in `README.md`.
#[derive(Clone, Debug, Default)]
pub struct Solver {
    assertions: Vec<BoolTerm>,
}

impl Solver {
    /// Create an empty solver with no assertions.
    pub fn new() -> Self {
        Self {
            assertions: Vec::new(),
        }
    }

    /// Add a boolean assertion to the conjunction to be checked.
    pub fn assert(&mut self, term: BoolTerm) {
        self.assertions.push(term);
    }

    /// Number of assertions accumulated so far.
    pub fn num_assertions(&self) -> usize {
        self.assertions.len()
    }

    /// Check that every assertion is well-sorted, reporting the first
    /// violation with a distinct error (TR-010). `check` treats ill-sorted
    /// input as `Unknown`; this gives callers the actionable diagnosis.
    pub fn validate(&self) -> Result<(), EvalError> {
        for a in &self.assertions {
            validate_bool(a)?;
        }
        Ok(())
    }

    /// Decide satisfiability of the conjunction of all asserted terms.
    ///
    /// Pipeline: blast → AIG → Tseitin CNF → CDCL. `Sat` carries a model
    /// that has been re-evaluated against every assertion (self-check);
    /// engine-UNSAT returns `Unknown` until the P2 verified checker lands —
    /// an `Unsat` this crate cannot certify is never reported.
    pub fn check(&self) -> CheckResult {
        match self.check_raw() {
            RawVerdict::Sat(env) => CheckResult::Sat(Model {
                assignments: {
                    let mut a: Vec<(String, u128)> = env.into_iter().collect();
                    a.sort();
                    a
                },
            }),
            // P1: believed, not checked — conservative Unknown (see docs).
            RawVerdict::Unsat => CheckResult::Unknown,
            RawVerdict::Unknown => CheckResult::Unknown,
        }
    }

    /// The engine's raw verdict — crate-internal, differential oracle only.
    pub(crate) fn check_raw(&self) -> RawVerdict {
        if self.assertions.is_empty() {
            // An empty conjunction is trivially satisfiable by the empty model.
            return RawVerdict::Sat(Env::new());
        }
        if self.assertions.iter().any(bool_uses_disabled) {
            return RawVerdict::Unknown;
        }
        // Ill-sorted input never reaches a blast rule: conservative Unknown
        // (callers get the diagnosis from `validate`).
        if self.validate().is_err() {
            return RawVerdict::Unknown;
        }
        let mut blaster = Blaster::new();
        let mut roots = Vec::with_capacity(self.assertions.len());
        for a in &self.assertions {
            match blaster.blast_bool(a) {
                Ok(lit) => roots.push(lit),
                // Ill-sorted input: conservative. `validate()` diagnoses.
                Err(_) => return RawVerdict::Unknown,
            }
        }
        let (cnf, map) = tseitin(&blaster.aig, &roots);
        match SatSolver::new().solve(&cnf) {
            SatResult::Unsat => RawVerdict::Unsat,
            SatResult::Sat(assignment) => {
                // Decode: each variable's word reads its input literals'
                // CNF variables out of the assignment.
                let mut env = Env::new();
                for (name, _width) in &blaster.var_order {
                    let word = &blaster.vars[name];
                    let mut value = 0u128;
                    for (i, lit) in word.iter().enumerate() {
                        let cnf_lit = map.cnf_lit(*lit);
                        let v = assignment[(cnf_lit.unsigned_abs() - 1) as usize];
                        let bit = if cnf_lit > 0 { v } else { !v };
                        value |= (bit as u128) << i;
                    }
                    env.insert(name.clone(), value);
                }
                // Self-check: the model must make every assertion true under
                // the concrete evaluator. A failure means an ordeal bug; we
                // return Unknown rather than a wrong Sat.
                let ok = self
                    .assertions
                    .iter()
                    .all(|a| eval::eval_bool(a, &env) == Ok(true));
                if ok {
                    RawVerdict::Sat(env)
                } else {
                    debug_assert!(false, "SAT model failed self-check — ordeal bug");
                    RawVerdict::Unknown
                }
            }
        }
    }
}

/// Sort-check a boolean term without needing variable bindings.
fn validate_bool(term: &BoolTerm) -> Result<(), EvalError> {
    let pair = |a: &BvTerm, b: &BvTerm| -> Result<(), EvalError> {
        let (wa, wb) = (eval::bv_sort(a)?.width, eval::bv_sort(b)?.width);
        if wa == wb {
            Ok(())
        } else {
            Err(EvalError::WidthMismatch {
                left: wa,
                right: wb,
            })
        }
    };
    match term {
        BoolTerm::Eq(a, b)
        | BoolTerm::Ne(a, b)
        | BoolTerm::Ult(a, b)
        | BoolTerm::Ule(a, b)
        | BoolTerm::Ugt(a, b)
        | BoolTerm::Uge(a, b)
        | BoolTerm::Slt(a, b)
        | BoolTerm::Sle(a, b)
        | BoolTerm::Sgt(a, b)
        | BoolTerm::Sge(a, b) => pair(a, b),
        BoolTerm::Not(t) => validate_bool(t),
        BoolTerm::And(a, b) | BoolTerm::Or(a, b) => {
            validate_bool(a)?;
            validate_bool(b)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::{BvTerm, Sort};

    fn var(name: &str, w: u32) -> BvTerm {
        BvTerm::Var {
            name: name.into(),
            sort: Sort::new(w),
        }
    }
    fn c(value: u128, w: u32) -> BvTerm {
        BvTerm::Const {
            value,
            sort: Sort::new(w),
        }
    }
    fn b(t: BvTerm) -> Box<BvTerm> {
        Box::new(t)
    }

    #[test]
    fn empty_solver_is_trivially_sat() {
        match Solver::new().check() {
            CheckResult::Sat(m) => assert!(m.assignments.is_empty()),
            other => panic!("empty conjunction must be Sat, got {other:?}"),
        }
    }

    #[test]
    fn unsat_stays_unknown_until_p2_certificates() {
        // x == x+1 is UNSAT; P1 must NOT report an unchecked Unsat.
        let x = var("x", 32);
        let x1 = BvTerm::Add(b(x.clone()), b(c(1, 32)));
        let mut s = Solver::new();
        s.assert(BoolTerm::Eq(b(x), b(x1)));
        match s.check() {
            CheckResult::Unknown => {}
            other => panic!("engine-UNSAT must surface as Unknown in P1, got {other:?}"),
        }
        // ...but the raw engine verdict (oracle-only) does see the Unsat.
        assert_eq!(s.check_raw(), RawVerdict::Unsat);
    }

    #[test]
    fn sat_returns_self_checked_model() {
        // x + 1 == 5 over 8 bits: model must bind x = 4.
        let x = var("x", 8);
        let mut s = Solver::new();
        s.assert(BoolTerm::Eq(b(BvTerm::Add(b(x), b(c(1, 8)))), b(c(5, 8))));
        match s.check() {
            CheckResult::Sat(m) => assert_eq!(m.assignments, vec![("x".into(), 4u128)]),
            other => panic!("expected Sat with x=4, got {other:?}"),
        }
    }

    #[test]
    fn sat_with_multiple_vars_and_assertions() {
        // x < y, y < 3, over 8 bits unsigned: only x=0/1, y=1/2 shapes.
        let (x, y) = (var("x", 8), var("y", 8));
        let mut s = Solver::new();
        s.assert(BoolTerm::Ult(b(x.clone()), b(y.clone())));
        s.assert(BoolTerm::Ult(b(y), b(c(3, 8))));
        match s.check() {
            CheckResult::Sat(m) => {
                let get = |n: &str| m.assignments.iter().find(|(k, _)| k == n).unwrap().1;
                assert!(get("x") < get("y") && get("y") < 3);
            }
            other => panic!("expected Sat, got {other:?}"),
        }
    }

    #[test]
    fn ill_sorted_query_is_unknown_and_validate_diagnoses() {
        let mut s = Solver::new();
        s.assert(BoolTerm::Eq(b(c(1, 8)), b(c(1, 32))));
        assert!(matches!(s.check(), CheckResult::Unknown));
        assert_eq!(
            s.validate(),
            Err(EvalError::WidthMismatch { left: 8, right: 32 })
        );
    }

    #[test]
    fn full_pipeline_on_every_op_family() {
        // One query touching every family: ((x*3) >> 1) ^ (y udiv 2) == 7,
        // rotr(x,1) uge y, sign_ext/extract/concat in the mix.
        let (x, y) = (var("x", 8), var("y", 8));
        let mut s = Solver::new();
        let lhs = BvTerm::Xor(
            b(BvTerm::Lshr(
                b(BvTerm::Mul(b(x.clone()), b(c(3, 8)))),
                b(c(1, 8)),
            )),
            b(BvTerm::Udiv(b(y.clone()), b(c(2, 8)))),
        );
        s.assert(BoolTerm::Eq(b(lhs), b(c(7, 8))));
        s.assert(BoolTerm::Uge(
            b(BvTerm::Rotr(b(x.clone()), b(c(1, 8)))),
            b(y.clone()),
        ));
        s.assert(BoolTerm::Eq(
            b(BvTerm::Extract {
                hi: 11,
                lo: 4,
                arg: b(BvTerm::Concat(
                    b(BvTerm::SignExt { by: 8, arg: b(x) }),
                    b(y),
                )),
            }),
            b(c(0xFF, 8)),
        ));
        // Whatever the verdict, it must be sound: Sat ⇒ self-checked model
        // (the self-check runs inside check_raw), Unsat ⇒ Unknown in P1.
        match s.check() {
            CheckResult::Sat(m) => assert_eq!(m.assignments.len(), 2),
            CheckResult::Unknown => {}
            CheckResult::Unsat(_) => panic!("no unchecked Unsat in P1"),
        }
    }
}
