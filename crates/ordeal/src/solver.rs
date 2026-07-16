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

/// A machine-checkable UNSAT certificate — a **self-contained, portable proof
/// object**.
///
/// The solver (untrusted) emits an LRAT proof; the `ordeal-lrat` checker
/// (the only trusted component) validated exactly these bytes against
/// [`cnf`](Certificate::cnf) before this value was constructed. Because the
/// certificate carries *both halves* — the DIMACS CNF and the LRAT refutation —
/// a consumer can re-establish the UNSAT verdict **with zero trust in ordeal**
/// by calling [`recheck`](Certificate::recheck) (or running `ordeal_lrat::check`
/// directly). That independent re-check is the whole point: an UNSAT is
/// believable because *you* can validate the proof, not because the solver says
/// so. This is what a translation validator (synth) needs to turn a proof-less
/// solver verdict into checkable evidence.
#[derive(Clone, Debug, Default)]
pub struct Certificate {
    /// The checker-validated textual LRAT proof bytes.
    pub lrat: Vec<u8>,
    /// The exact DIMACS CNF clause set the LRAT proof refutes — the other half
    /// of the checkable pair. Together with [`lrat`](Certificate::lrat) it is a
    /// complete, independently-verifiable proof of unsatisfiability.
    pub cnf: Vec<Vec<i32>>,
}

/// Why an independent [`Certificate::recheck`] could not confirm the proof.
#[derive(Debug)]
pub enum CertificateError {
    /// The LRAT bytes were not valid UTF-8 (only possible for a hand-built
    /// certificate; ones ordeal emits are always text).
    NotText,
    /// The trusted `ordeal-lrat` checker rejected the LRAT proof against the
    /// carried CNF.
    Rejected(ordeal_lrat::CheckError),
}

impl std::fmt::Display for CertificateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CertificateError::NotText => write!(f, "LRAT certificate is not valid UTF-8"),
            CertificateError::Rejected(e) => write!(f, "checker rejected certificate: {e:?}"),
        }
    }
}

impl std::error::Error for CertificateError {}

impl Certificate {
    /// The LRAT proof as text, if the bytes are valid UTF-8 (ordeal-emitted
    /// certificates always are).
    pub fn lrat_text(&self) -> Option<&str> {
        std::str::from_utf8(&self.lrat).ok()
    }

    /// Independently re-validate this certificate with the trusted `ordeal-lrat`
    /// checker — the *same* check ordeal ran internally before returning
    /// `Unsat`, reproducible by any consumer with no faith in the (untrusted)
    /// solver. `Ok(())` ⟺ the LRAT proof refutes [`cnf`](Certificate::cnf), so
    /// the conjunction really is unsatisfiable.
    pub fn recheck(&self) -> Result<(), CertificateError> {
        let text = self.lrat_text().ok_or(CertificateError::NotText)?;
        ordeal_lrat::check(&self.cnf, text).map_err(CertificateError::Rejected)
    }
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
    Urem,
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
        BvTerm::Urem(..) => OpKind::Urem,
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
        | BvTerm::Urem(a, b)
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
            BvTerm::Urem(a, b) => {
                let (wa, wb) = (self.blast_bv(a)?, self.blast_bv(b)?);
                muldiv::blast_urem(&mut self.aig, &wa, &wb)
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
        Self::verdict(self.solve_pipeline(None))
    }

    /// Decide satisfiability under a conflict budget (DES-019 / TR-016).
    ///
    /// Runs the identical pipeline as [`Solver::check`] — blast → AIG →
    /// Tseitin CNF → bounded CDCL — but caps the SAT core at `max_conflicts`
    /// search conflicts. On budget exhaustion the core reaches no verdict and
    /// this returns [`CheckResult::Unknown`]; on any decided verdict it
    /// behaves exactly like `check` (self-checked model on SAT, and on
    /// engine-UNSAT the LRAT certificate is validated by `ordeal-lrat` before
    /// `Unsat` is returned, degrading to `Unknown` on rejection).
    ///
    /// The budget bounds only completeness: the certificate gate and the
    /// model self-check are untouched, so an exhausted budget yields `Unknown`
    /// and never a wrong or unchecked verdict.
    pub fn check_with_limit(&self, max_conflicts: u64) -> CheckResult {
        Self::verdict(self.solve_pipeline(Some(max_conflicts)))
    }

    /// Prove two same-width bitvector terms **equivalent** — the standard
    /// equivalence-as-UNSAT encoding, for callers (e.g. spar layout codegen,
    /// issue #38) that want a one-call `a ≡ b` oracle rather than assembling
    /// the `Ne` goal by hand.
    ///
    /// It asserts the terms *differ* and decides the result:
    ///
    /// - [`CheckResult::Unsat`] ⟹ `a` and `b` are **equal for every input**;
    ///   the carried LRAT certificate was validated by `ordeal-lrat` before
    ///   return, so this is a *checked* proof, not solver faith.
    /// - [`CheckResult::Sat`] ⟹ the terms are **not** equivalent, and the
    ///   model is a counterexample: an assignment to the free variables on
    ///   which the two terms evaluate differently.
    /// - [`CheckResult::Unknown`] ⟹ conservative — **no** equivalence claim.
    ///   A width mismatch (ill-sorted `Ne`) also lands here, exactly as
    ///   [`Solver::check`] treats ill-sorted input; call [`Solver::validate`]
    ///   first if you want the width error surfaced explicitly.
    ///
    /// Only a `Unsat` authorizes treating the layouts as interchangeable;
    /// `Unknown`/`Sat` do not. Build the `BvTerm` graph programmatically for
    /// machine-generated queries — no SMT-LIB2 text round-trip on the hot path.
    pub fn prove_equiv(a: BvTerm, b: BvTerm) -> CheckResult {
        let mut solver = Solver::new();
        solver.assert(BoolTerm::Ne(Box::new(a), Box::new(b)));
        solver.check()
    }

    /// Map an internal pipeline outcome to the caller-facing verdict, applying
    /// the soundness gate uniformly for `check` and `check_with_limit`.
    fn verdict(outcome: Pipeline) -> CheckResult {
        match outcome {
            Pipeline::Sat(env) => CheckResult::Sat(Model {
                assignments: {
                    let mut a: Vec<(String, u128)> = env.into_iter().collect();
                    a.sort();
                    a
                },
            }),
            Pipeline::Unsat {
                certificate: Some(lrat),
                cnf,
            } => CheckResult::Unsat(Certificate { lrat, cnf }),
            // The checker rejected our own certificate: an ordeal bug, but a
            // sound outcome — degrade to Unknown rather than assert UNSAT.
            Pipeline::Unsat {
                certificate: None, ..
            }
            | Pipeline::Unknown => CheckResult::Unknown,
        }
    }

    /// The engine's raw verdict — crate-internal, differential oracle only.
    #[cfg(any(test, feature = "oracle"))]
    pub(crate) fn check_raw(&self) -> RawVerdict {
        match self.solve_pipeline(None) {
            Pipeline::Sat(env) => RawVerdict::Sat(env),
            Pipeline::Unsat { .. } => RawVerdict::Unsat,
            Pipeline::Unknown => RawVerdict::Unknown,
        }
    }

    /// Run the full pipeline once, producing the internal outcome. `budget`
    /// bounds the CDCL core's search conflicts (`None` is unbounded); an
    /// exhausted budget surfaces as [`Pipeline::Unknown`].
    fn solve_pipeline(&self, budget: Option<u64>) -> Pipeline {
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
            // Untrusted canonicalization above the AIG (issue #35 / TR-009):
            // commutative-operand ordering + const-folding so equal-but-
            // structurally-different terms share a node. Soundness is unaffected
            // — Unsat stays LRAT-checked, and the SAT model self-check below
            // re-evaluates against the ORIGINAL assertions.
            let a = crate::canon::canonicalize_bool(a);
            match blaster.blast_bool(&a) {
                Ok(lit) => roots.push(lit),
                // Ill-sorted input: conservative. `validate()` diagnoses.
                Err(_) => return Pipeline::Unknown,
            }
        }
        let (cnf, map) = tseitin(&blaster.aig, &roots);
        let mut sat_solver = SatSolver::new();
        let verdict = match budget {
            // Bounded solve: budget exhaustion ⇒ no verdict ⇒ conservative
            // Unknown (soundness contract preserved).
            Some(max) => match sat_solver.solve_with_budget(&cnf, max) {
                Some(v) => v,
                None => return Pipeline::Unknown,
            },
            None => sat_solver.solve(&cnf),
        };
        match verdict {
            SatResult::Unsat => {
                // Emit the LRAT certificate from the proof trace and have the
                // trusted checker validate it BEFORE asserting UNSAT.
                let cert = crate::lrat::emit_lrat(cnf.clauses.len(), sat_solver.proof_trace());
                match ordeal_lrat::check(&cnf.clauses, &cert) {
                    Ok(()) => Pipeline::Unsat {
                        certificate: Some(cert.into_bytes()),
                        // Carry the refuted CNF so the caller's Certificate is a
                        // self-contained, independently re-checkable proof.
                        cnf: cnf.clauses,
                    },
                    Err(_) => {
                        debug_assert!(false, "checker rejected our certificate — ordeal bug");
                        Pipeline::Unsat {
                            certificate: None,
                            cnf: Vec::new(),
                        }
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
    Unsat {
        certificate: Option<Vec<u8>>,
        /// The refuted DIMACS CNF, carried to the caller's [`Certificate`] so
        /// the proof is independently re-checkable.
        cnf: Vec<Vec<i32>>,
    },
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
    fn certificate_is_independently_recheckable() {
        // The trust story for consumers (synth translation validation): an
        // UNSAT certificate is a portable proof object a caller can re-validate
        // with the trusted checker, needing zero faith in the solver.
        // Equivalence: x*2 ≡ x<<1 (a strength-reduction a codegen rule emits).
        let x = || var("x", 32);
        match Solver::prove_equiv(
            BvTerm::Mul(b(x()), b(c(2, 32))),
            BvTerm::Shl(b(x()), b(c(1, 32))),
        ) {
            CheckResult::Unsat(cert) => {
                assert!(!cert.cnf.is_empty(), "certificate must carry the CNF");
                // Independent re-check with the trusted checker succeeds.
                cert.recheck()
                    .expect("consumer re-check must confirm UNSAT");
                // And it genuinely depends on the carried CNF (recheck is not a
                // no-op): the same LRAT proof no longer validates once the
                // clauses it refutes are gone.
                let mut tampered = cert.clone();
                tampered.cnf.clear();
                assert!(
                    tampered.recheck().is_err(),
                    "re-check must fail when the refuted CNF is removed"
                );
            }
            other => panic!("x*2 ≡ x<<1 must be certificate-checked Unsat, got {other:?}"),
        }
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
    fn prove_equiv_layout_field_extract_roundtrips() {
        // spar #38 layout oracle: a packed record's low field survives
        // pack+extract. Extracting the low 8 bits of concat(hi32, flags8)
        // recovers flags8 — a bit-exact layout equivalence, proven UNSAT.
        let flags = var("flags", 8);
        let hi = var("hi", 32);
        // concat puts `hi` in the high bits, `flags` in the low 8 (40-bit).
        let packed = BvTerm::Concat(b(hi), b(flags.clone()));
        let low8 = BvTerm::Extract {
            hi: 7,
            lo: 0,
            arg: b(packed),
        };
        match Solver::prove_equiv(low8, flags) {
            CheckResult::Unsat(cert) => assert!(!cert.lrat.is_empty()),
            other => panic!("layouts must be proven equivalent, got {other:?}"),
        }
    }

    #[test]
    fn prove_equiv_distinct_layouts_give_counterexample() {
        // Two distinct 32-bit terms are not equivalent: Sat with a witness.
        match Solver::prove_equiv(var("a", 32), var("b", 32)) {
            CheckResult::Sat(_) => {}
            other => panic!("distinct terms are not equivalent, got {other:?}"),
        }
    }

    #[test]
    fn prove_equiv_width_mismatch_is_conservative_unknown() {
        // A width mismatch is ill-sorted (`Ne` of 32 vs 8 bits); like `check`,
        // it degrades to a conservative `Unknown` — never a false equivalence.
        match Solver::prove_equiv(var("a", 32), var("b", 8)) {
            CheckResult::Unknown => {}
            other => panic!("width mismatch must be Unknown, got {other:?}"),
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

    // --- UV-018: resource-bounded check (conflict budget → Unknown) ---

    #[test]
    fn bounded_check_matches_check_within_budget() {
        // A trivially-decidable SAT query with a generous budget matches
        // check() bit-for-bit.
        let x = var("x", 8);
        let mut s = Solver::new();
        s.assert(BoolTerm::Eq(b(BvTerm::Add(b(x), b(c(1, 8)))), b(c(5, 8))));
        match s.check_with_limit(1_000_000) {
            CheckResult::Sat(m) => assert_eq!(m.assignments, vec![("x".into(), 4u128)]),
            other => panic!("expected Sat with x=4 within budget, got {other:?}"),
        }
        assert!(matches!(s.check(), CheckResult::Sat(_)));

        // A trivially-decidable UNSAT query still yields a checked certificate
        // under a generous budget (x == x+1 needs only a few conflicts).
        let y = var("y", 32);
        let y1 = BvTerm::Add(b(y.clone()), b(c(1, 32)));
        let mut u = Solver::new();
        u.assert(BoolTerm::Eq(b(y), b(y1)));
        match u.check_with_limit(1_000_000) {
            CheckResult::Unsat(cert) => assert!(!cert.lrat.is_empty()),
            other => panic!("expected certificate-checked Unsat, got {other:?}"),
        }
    }

    #[test]
    fn zero_budget_forces_unknown() {
        // A genuinely hard multiplier-equivalence (distributivity) that
        // canonicalization does NOT trivialize: reaching UNSAT needs search
        // conflicts, so a zero budget must yield Unknown — never Unsat, never a
        // hang. Budget 0 abandons at the first search conflict, returning
        // immediately.
        let s = hard_mul_equivalence();
        assert!(matches!(s.check_with_limit(0), CheckResult::Unknown));
    }

    /// The #29 A5 shape: mul is commutative, so `a*b != b*a` is UNSAT. Since
    /// v0.8.0 (issue #35) commutative-operand canonicalization collapses this to
    /// `Ne(t,t)` and the AIG folds it to false, so it is now decided by root
    /// propagation — instantly, at any budget (was: did not finish in 590s).
    fn a5_mul_commutativity() -> Solver {
        let (a, b_) = (var("a", 32), var("b", 32));
        let mut s = Solver::new();
        s.assert(BoolTerm::Ne(
            b(BvTerm::Mul(b(a.clone()), b(b_.clone()))),
            b(BvTerm::Mul(b(b_), b(a))),
        ));
        s
    }

    /// A hard multiplier-equivalence that survives canonicalization: modular
    /// distributivity `a*(b+c) == a*b + a*c` is UNSAT for the `Ne`, but the two
    /// sides are structurally different multiplier expressions (not a mere
    /// commutation or constant fold), so deciding it needs real CDCL search.
    /// Used to exercise the conflict-budget semantics.
    fn hard_mul_equivalence() -> Solver {
        let (a, bb, cc) = (var("a", 32), var("b", 32), var("c", 32));
        let lhs = BvTerm::Mul(b(a.clone()), b(BvTerm::Add(b(bb.clone()), b(cc.clone()))));
        let rhs = BvTerm::Add(
            b(BvTerm::Mul(b(a.clone()), b(bb))),
            b(BvTerm::Mul(b(a), b(cc))),
        );
        let mut s = Solver::new();
        s.assert(BoolTerm::Ne(b(lhs), b(rhs)));
        s
    }

    #[test]
    fn a5_mul_commutativity_now_root_decided_at_any_budget() {
        // The v0.4.0 conflict-budget stopgap is no longer needed for A5:
        // canonicalization makes it root-decidable, so even a ZERO budget
        // (which abandons before any search conflict) still returns a checked
        // UNSAT — the shape is refuted by propagation, not search.
        match a5_mul_commutativity().check_with_limit(0) {
            CheckResult::Unsat(cert) => {
                cert.recheck()
                    .expect("root-decided A5 certificate must re-check");
            }
            other => panic!("canonicalized A5 must be root-decided UNSAT, got {other:?}"),
        }
    }

    #[test]
    fn a5_mul_commutativity_decides_unsat_after_canonicalization() {
        // The v0.8.0 kill criterion (issue #35): with commutative-operand
        // canonicalization, Ne(Mul(a,b), Mul(b,a)) collapses to Ne(t,t) which
        // the AIG folds to false, so the UNBOUNDED check now decides UNSAT
        // essentially instantly — the shape that did not finish in 590 s.
        let s = a5_mul_commutativity();
        let start = std::time::Instant::now();
        let verdict = s.check();
        let elapsed = start.elapsed();
        match verdict {
            CheckResult::Unsat(cert) => {
                cert.recheck()
                    .expect("A5 certificate must independently re-check");
            }
            other => panic!("A5 must now decide UNSAT unbounded, got {other:?}"),
        }
        assert!(
            elapsed < std::time::Duration::from_secs(5),
            "canonicalized A5 must decide fast, took {elapsed:?}"
        );
    }

    #[test]
    fn bounded_check_is_deterministic() {
        // Same query + same budget ⇒ same verdict (the CDCL core is
        // deterministic on the decided path and at the budget boundary). The
        // hard distributivity query stays Unknown at budget 100.
        let a = hard_mul_equivalence().check_with_limit(100);
        let b_ = hard_mul_equivalence().check_with_limit(100);
        assert!(matches!(a, CheckResult::Unknown));
        assert!(matches!(b_, CheckResult::Unknown));

        // And a within-budget verdict is stable too.
        let x = var("x", 8);
        let mut s = Solver::new();
        s.assert(BoolTerm::Eq(b(BvTerm::Add(b(x), b(c(1, 8)))), b(c(5, 8))));
        let (m1, m2) = (s.check_with_limit(10_000), s.check_with_limit(10_000));
        match (m1, m2) {
            (CheckResult::Sat(a), CheckResult::Sat(b)) => {
                assert_eq!(a.assignments, b.assignments);
            }
            other => panic!("expected stable Sat, got {other:?}"),
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
