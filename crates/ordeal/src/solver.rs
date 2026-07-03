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
//! # Pipeline status (P2: certificate-checked)
//!
//! `check` runs blast → AIG → Tseitin CNF → CDCL. On SAT it returns a
//! self-checked model. On UNSAT the LRAT certificate emitted from the CDCL
//! proof trace is validated by the `ordeal-lrat` checker **before** `Unsat`
//! is returned — an `Unsat` the checker did not accept degrades to `Unknown`
//! (AGENTS.md rule 1: no unchecked `Unsat`, ever). The raw engine verdict is
//! exposed crate-internally for the differential oracle only.
//!
//! Trust status: the checker is small, dependency-free, and mutation-tested;
//! its formal soundness proof (Rust → Lean 4 via Aeneas, TR-013) is the
//! remaining P2 obligation and is tracked in rivet as FEAT-002.
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
/// The solver (untrusted) emits an LRAT proof; the `ordeal-lrat` checker
/// (the only trusted component) validated exactly these bytes before this
/// value was constructed. Callers can independently re-run
/// `ordeal_lrat::check` on them.
#[derive(Clone, Debug, Default)]
pub struct Certificate {
    /// The checker-validated textual LRAT proof bytes.
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
    /// Unsatisfiable, with the LRAT certificate the checker validated.
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
/// the differential oracle (and tests) may look at this — an `Unsat` whose
/// certificate was not checker-validated must never reach a caller.
#[cfg(any(test, feature = "oracle"))]
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
    Ite,
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
        BvTerm::Ite { .. } => OpKind::Ite,
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
        BvTerm::Ite { cond, then_, else_ } => {
            bool_uses_disabled(cond) || bv_uses_disabled(then_) || bv_uses_disabled(else_)
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
            BvTerm::Ite { cond, then_, else_ } => {
                let c = self.blast_bool(cond)?;
                let (wt, we) = (self.blast_bv(then_)?, self.blast_bv(else_)?);
                bitwise::blast_ite(&mut self.aig, c, &wt, &we)
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

    /// One-shot decision for an **extended (array/UF sliver) query**.
    ///
    /// The sliver is eliminated into the closed QF_BV core by
    /// [`crate::sliver::lower`] — eager read-over-write for `Array(BV32→BV8)`
    /// select/store over concrete offsets, Ackermannization for
    /// uninterpreted `pure_call` congruence — and the resulting pure
    /// assertions are decided by the normal [`Solver::check`] pipeline.
    ///
    /// An **out-of-sliver** query (symbolic index, bad array sort, or an
    /// inconsistent call signature — any [`crate::sliver::SliverError`])
    /// returns [`CheckResult::Unknown`]: conservative by construction, never
    /// a guess. Soundness is unchanged from `check` — no array/UF construct
    /// ever reaches the bit-blaster; only the lowered core does.
    pub fn check_sliver(assertions: &[crate::sliver::ExtBoolTerm]) -> CheckResult {
        match crate::sliver::lower(assertions) {
            Ok(core) => {
                let mut solver = Solver::new();
                for a in core {
                    solver.assert(a);
                }
                solver.check()
            }
            // Out-of-sliver: conservative Unknown (callers must not optimize).
            Err(_) => CheckResult::Unknown,
        }
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
    /// that has been re-evaluated against every assertion (self-check).
    /// On engine-UNSAT the LRAT certificate emitted from the proof trace is
    /// validated by the `ordeal-lrat` checker before `Unsat` is returned —
    /// an `Unsat` the checker did not accept is never reported (it degrades
    /// to `Unknown`, which is always sound).
    pub fn check(&self) -> CheckResult {
        match self.solve_pipeline() {
            Pipeline::Sat(env) => CheckResult::Sat(Model {
                assignments: {
                    let mut a: Vec<(String, u128)> = env.into_iter().collect();
                    a.sort();
                    a
                },
            }),
            Pipeline::Unsat {
                certificate: Some(lrat),
            } => CheckResult::Unsat(Certificate { lrat }),
            // The checker rejected our own certificate: an ordeal bug, but a
            // sound outcome — degrade to Unknown rather than assert UNSAT.
            Pipeline::Unsat { certificate: None } | Pipeline::Unknown => CheckResult::Unknown,
        }
    }

    /// The engine's raw verdict — crate-internal, differential oracle only.
    #[cfg(any(test, feature = "oracle"))]
    pub(crate) fn check_raw(&self) -> RawVerdict {
        match self.solve_pipeline() {
            Pipeline::Sat(env) => RawVerdict::Sat(env),
            Pipeline::Unsat { .. } => RawVerdict::Unsat,
            Pipeline::Unknown => RawVerdict::Unknown,
        }
    }

    /// Run the full pipeline once, producing the internal outcome.
    fn solve_pipeline(&self) -> Pipeline {
        if self.assertions.is_empty() {
            // An empty conjunction is trivially satisfiable by the empty model.
            return Pipeline::Sat(Env::new());
        }
        if self.assertions.iter().any(bool_uses_disabled) {
            return Pipeline::Unknown;
        }
        // Ill-sorted input never reaches a blast rule: conservative Unknown
        // (callers get the diagnosis from `validate`).
        if self.validate().is_err() {
            return Pipeline::Unknown;
        }
        let mut blaster = Blaster::new();
        let mut roots = Vec::with_capacity(self.assertions.len());
        for a in &self.assertions {
            match blaster.blast_bool(a) {
                Ok(lit) => roots.push(lit),
                // Ill-sorted input: conservative. `validate()` diagnoses.
                Err(_) => return Pipeline::Unknown,
            }
        }
        let (cnf, map) = tseitin(&blaster.aig, &roots);
        let mut sat_solver = SatSolver::new();
        match sat_solver.solve(&cnf) {
            SatResult::Unsat => {
                // Emit the LRAT certificate from the proof trace and have the
                // trusted checker validate it BEFORE asserting UNSAT.
                let cert = crate::lrat::emit_lrat(cnf.clauses.len(), sat_solver.proof_trace());
                match ordeal_lrat::check(&cnf.clauses, &cert) {
                    Ok(()) => Pipeline::Unsat {
                        certificate: Some(cert.into_bytes()),
                    },
                    Err(_) => {
                        debug_assert!(false, "checker rejected our certificate — ordeal bug");
                        Pipeline::Unsat { certificate: None }
                    }
                }
            }
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
                    Pipeline::Sat(env)
                } else {
                    debug_assert!(false, "SAT model failed self-check — ordeal bug");
                    Pipeline::Unknown
                }
            }
        }
    }
}

/// Internal pipeline outcome: like [`RawVerdict`] but carrying the
/// checker-validated certificate on UNSAT (None = checker rejected it).
enum Pipeline {
    Sat(Env),
    Unsat { certificate: Option<Vec<u8>> },
    Unknown,
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
    fn unsat_carries_a_checker_validated_certificate() {
        // x == x+1 is UNSAT; P2 returns Unsat only with a validated LRAT.
        let x = var("x", 32);
        let x1 = BvTerm::Add(b(x.clone()), b(c(1, 32)));
        let mut s = Solver::new();
        s.assert(BoolTerm::Eq(b(x), b(x1)));
        match s.check() {
            CheckResult::Unsat(cert) => {
                assert!(!cert.lrat.is_empty(), "certificate must be present");
                // The bytes must be a well-formed LRAT text (the checker
                // already validated them against the CNF inside check()).
                let text = String::from_utf8(cert.lrat).expect("LRAT is text");
                assert!(text.lines().last().is_some_and(|l| l.contains(" 0")));
            }
            other => panic!("expected certificate-checked Unsat, got {other:?}"),
        }
        // The raw engine verdict (oracle-only) agrees.
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
        // (the self-check runs inside the pipeline), Unsat ⇒ validated LRAT.
        match s.check() {
            CheckResult::Sat(m) => assert_eq!(m.assignments.len(), 2),
            CheckResult::Unknown => {}
            CheckResult::Unsat(cert) => {
                assert!(!cert.lrat.is_empty(), "Unsat must carry the certificate")
            }
        }
    }

    #[test]
    fn check_sliver_entry_lowers_and_decides() {
        use crate::sliver::{ArrayTerm, ExtBoolTerm, ExtBvTerm};
        // select(store(a, 5, v), 5) == v  is valid for any v ⇒ the query
        // asserting it *false* (via Ne) is UNSAT... but we assert the
        // equality holds, which is SAT. Keep it simple: read back a stored
        // concrete value must equal it.
        let bv32 = Sort::new(32);
        let bv8 = Sort::new(8);
        let idx = ExtBvTerm::Core(BvTerm::Const {
            value: 5,
            sort: bv32,
        });
        let stored = ExtBvTerm::Core(BvTerm::Var {
            name: "v".into(),
            sort: bv8,
        });
        let arr = ArrayTerm::Store {
            array: Box::new(ArrayTerm::Var { name: "a".into() }),
            index: Box::new(idx.clone()),
            value: Box::new(stored.clone()),
        };
        let read = ExtBvTerm::Select {
            array: Box::new(arr),
            index: Box::new(idx),
        };
        // read == v : satisfiable (in fact valid).
        let q = ExtBoolTerm::Eq(read, stored);
        match Solver::check_sliver(&[q]) {
            CheckResult::Sat(_) | CheckResult::Unknown => {}
            CheckResult::Unsat(_) => panic!("read-over-write of a stored value is not UNSAT"),
        }
    }

    #[test]
    fn check_sliver_out_of_sliver_is_unknown() {
        use crate::sliver::{ArrayTerm, ExtBoolTerm, ExtBvTerm};
        // Symbolic (variable) index: out of the sliver ⇒ conservative Unknown.
        let bv32 = Sort::new(32);
        let bv8 = Sort::new(8);
        let sym = ExtBvTerm::Core(BvTerm::Var {
            name: "i".into(),
            sort: bv32,
        });
        let read = ExtBvTerm::Select {
            array: Box::new(ArrayTerm::Var { name: "a".into() }),
            index: Box::new(sym),
        };
        let q = ExtBoolTerm::Eq(
            read,
            ExtBvTerm::Core(BvTerm::Const {
                value: 0,
                sort: bv8,
            }),
        );
        assert!(matches!(Solver::check_sliver(&[q]), CheckResult::Unknown));
    }
}
