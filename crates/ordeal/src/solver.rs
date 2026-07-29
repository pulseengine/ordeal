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
use crate::cnf::{CnfFormula, TseitinMap, tseitin};
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
    /// Prove two **extended** (sliver) terms equivalent — the sliver twin of
    /// [`Solver::prove_equiv`] (TR-029, issue #71), for consumers whose
    /// operands live in the extended language (`select`/`store`/`pure_call`)
    /// rather than the closed core.
    ///
    /// Asserts `Ne(a, b)`, lowers through the sliver (read-over-write
    /// elimination + array/UF congruence), and decides:
    /// [`CheckResult::Unsat`] ⟹ equal for every input, array contents, and
    /// uninterpreted-function interpretation — certificate re-checkable;
    /// [`CheckResult::Sat`] ⟹ a counterexample; [`CheckResult::Unknown`] ⟹
    /// conservative (incl. out-of-sliver input).
    pub fn prove_equiv_sliver(
        a: crate::sliver::ExtBvTerm,
        b: crate::sliver::ExtBvTerm,
    ) -> CheckResult {
        Self::check_sliver(&[crate::sliver::ExtBoolTerm::Ne(a, b)])
    }

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
        Self::verdict(self.solve_pipeline(Bound::None))
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
        Self::verdict(self.solve_pipeline(Bound::Conflicts(max_conflicts)))
    }

    /// Decide under a **wall-clock deadline** (TR-029, issue #71): the
    /// consumer-facing twin of [`Solver::check_with_limit`], for validators
    /// that drive a per-check *millisecond* budget — which a conflict count
    /// does not map to — and degrade a slow solve to a fast, safe revert.
    ///
    /// Semantics are identical to [`Solver::check`] except that once
    /// `timeout_ms` elapses the search is abandoned and the result is
    /// [`CheckResult::Unknown`] — never a wrong or unchecked verdict, per the
    /// module-level soundness contract. `timeout_ms == 0` admits only queries
    /// decided before the first search conflict (like a zero conflict
    /// budget). Blasting/canonicalization time is not bounded — the deadline
    /// governs the SAT search, which dominates on hard queries.
    pub fn check_with_deadline(&self, timeout_ms: u64) -> CheckResult {
        let deadline = std::time::Instant::now() + std::time::Duration::from_millis(timeout_ms);
        Self::verdict(self.solve_pipeline(Bound::Deadline(deadline)))
    }

    /// Prove a boolean **goal valid** — true for *every* assignment to its free
    /// variables — via the standard validity-as-UNSAT encoding (assert the
    /// negation, refute it). This is the general primitive behind
    /// [`Solver::prove_equiv`] and the `trap` module's gates, exposed for
    /// callers that need to prove an arbitrary QF_BV predicate rather than a
    /// bare term equivalence (relay codec/CRC laws, scry transfer soundness,
    /// sigil overflow rejection, meld offset-fold guards; issue #66).
    ///
    /// - [`CheckResult::Unsat`] ⟹ the goal holds for **every** input; the
    ///   carried LRAT certificate was validated by `ordeal-lrat` before return,
    ///   so a consumer can `cert.recheck()` and re-establish validity with zero
    ///   trust in the solver.
    /// - [`CheckResult::Sat`] ⟹ the goal is **not** valid, and the model is a
    ///   **counterexample**: a concrete input on which the goal is false.
    /// - [`CheckResult::Unknown`] ⟹ conservative — **no** validity claim
    ///   (out-of-fragment, ill-sorted, or resource-bounded). Never optimize on
    ///   it.
    ///
    /// Only a `Unsat` authorizes relying on the goal. The dual is exact:
    /// `prove_equiv(a, b)` is `prove_valid(Eq(a, b))`, and a `prove_valid`
    /// counterexample is the witness a translation validator reports.
    pub fn prove_valid(goal: BoolTerm) -> CheckResult {
        let mut solver = Solver::new();
        solver.assert(BoolTerm::Not(Box::new(goal)));
        solver.check()
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

    /// Decide a **propositional** CNF directly — the certified SAT core
    /// exposed *below* the bit-blaster (TR-026, issue #67). This is the
    /// front-end rivet's feature-model / variant consistency needs
    /// (rivet#128): a Boolean consistency query whose `Unsat` is a portable,
    /// re-checkable certificate, without going through a QF_BV encoding.
    ///
    /// Same soundness gate as [`Solver::check`]: on `Unsat` the LRAT proof is
    /// emitted from the CDCL trace and **validated by `ordeal-lrat` before**
    /// the verdict is returned, so a returned [`Certificate`] is
    /// `recheck()`-able with zero trust in the solver.
    ///
    /// - [`CheckResult::Unsat`] ⟹ the clause set is unsatisfiable (the
    ///   feature model is inconsistent), with a checked certificate over
    ///   *exactly* `formula.clauses`.
    /// - [`CheckResult::Sat`] ⟹ satisfiable; the model binds `"v1".."vN"` to
    ///   `0`/`1` (a consistent configuration). The assignment is self-checked
    ///   against the formula before return, exactly as [`Solver::check`] does.
    /// - [`CheckResult::Unknown`] ⟹ conservative — only if the checker
    ///   rejects ordeal's own certificate (an ordeal bug, never a wrong
    ///   verdict).
    ///
    /// Variables are `1..=formula.num_vars`; a literal `±v` refers to variable
    /// `v`. No bit-blaster, no term graph — the caller supplies clauses.
    pub fn check_cnf(formula: &crate::cnf::CnfFormula) -> CheckResult {
        let mut sat_solver = SatSolver::new();
        match sat_solver.solve(formula) {
            SatResult::Unsat => {
                let cert =
                    crate::lrat::emit_lrat_trimmed(formula.clauses.len(), sat_solver.proof_trace());
                match ordeal_lrat::check(&formula.clauses, &cert) {
                    Ok(()) => CheckResult::Unsat(Certificate {
                        lrat: cert.into_bytes(),
                        cnf: formula.clauses.clone(),
                    }),
                    Err(_) => {
                        debug_assert!(false, "checker rejected our certificate — ordeal bug");
                        CheckResult::Unknown
                    }
                }
            }
            SatResult::Sat(assignment) => {
                // Self-check the model against the formula, mirroring the
                // guarantee `check` makes for BV models.
                debug_assert!(
                    formula.eval(&assignment),
                    "SAT model must satisfy the formula — ordeal bug"
                );
                let assignments = assignment
                    .iter()
                    .enumerate()
                    .map(|(i, &b)| (format!("v{}", i + 1), b as u128))
                    .collect();
                CheckResult::Sat(Model { assignments })
            }
        }
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
        match self.solve_pipeline(Bound::None) {
            Pipeline::Sat(env) => RawVerdict::Sat(env),
            Pipeline::Unsat { .. } => RawVerdict::Unsat,
            Pipeline::Unknown => RawVerdict::Unknown,
        }
    }

    /// Run the full pipeline once, producing the internal outcome. `budget`
    /// bounds the CDCL core's search conflicts (`None` is unbounded); an
    /// exhausted budget surfaces as [`Pipeline::Unknown`].
    fn solve_pipeline(&self, bound: Bound) -> Pipeline {
        if self.assertions.is_empty() {
            // An empty conjunction is trivially satisfiable by the empty model.
            return Pipeline::Sat(Env::new());
        }
        let Some((blaster, cnf, map)) = self.lower() else {
            return Pipeline::Unknown;
        };
        let mut sat_solver = SatSolver::new();
        let verdict = match bound {
            // Bounded solve: exhaustion ⇒ no verdict ⇒ conservative Unknown
            // (soundness contract preserved) — identically for a conflict
            // budget and a wall-clock deadline.
            Bound::Conflicts(max) => match sat_solver.solve_with_budget(&cnf, max) {
                Some(v) => v,
                None => return Pipeline::Unknown,
            },
            Bound::Deadline(d) => match sat_solver.solve_with_deadline(&cnf, d) {
                Some(v) => v,
                None => return Pipeline::Unknown,
            },
            Bound::None => sat_solver.solve(&cnf),
        };
        match verdict {
            SatResult::Unsat => {
                // Emit the LRAT certificate from the proof trace and have the
                // trusted checker validate it BEFORE asserting UNSAT.
                let cert =
                    crate::lrat::emit_lrat_trimmed(cnf.clauses.len(), sat_solver.proof_trace());
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
            SatResult::Sat(assignment) => self.decode_and_check(&blaster, &map, &assignment),
        }
    }

    /// The pipeline's front half — validation, canonicalization, blasting,
    /// Tseitin — shared by every backend. `None` means conservative Unknown
    /// (disabled ops or ill-sorted input; `validate()` diagnoses).
    fn lower(&self) -> Option<(Blaster, CnfFormula, TseitinMap)> {
        if self.assertions.iter().any(bool_uses_disabled) {
            return None;
        }
        // Ill-sorted input never reaches a blast rule: conservative Unknown.
        if self.validate().is_err() {
            return None;
        }
        let mut blaster = Blaster::new();
        let mut roots = Vec::with_capacity(self.assertions.len());
        for a in &self.assertions {
            // Untrusted canonicalization above the AIG (issue #35 / TR-009):
            // commutative-operand ordering + const-folding so equal-but-
            // structurally-different terms share a node. Soundness is unaffected
            // — Unsat stays LRAT-checked, and the SAT model self-check
            // re-evaluates against the ORIGINAL assertions.
            let a = crate::canon::canonicalize_bool(a);
            match blaster.blast_bool(&a) {
                Ok(lit) => roots.push(lit),
                Err(_) => return None,
            }
        }
        let (cnf, map) = tseitin(&blaster.aig, &roots);
        Some((blaster, cnf, map))
    }

    /// Decode a SAT assignment into a model and self-check it against the
    /// ORIGINAL assertions — shared by every backend. A failing self-check
    /// means an ordeal bug; the outcome degrades to Unknown, never a wrong
    /// Sat.
    fn decode_and_check(
        &self,
        blaster: &Blaster,
        map: &TseitinMap,
        assignment: &[bool],
    ) -> Pipeline {
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

    /// Decide with the optional CaDiCaL accelerator (TR-004's "benchmark
    /// yardstick" role) — identical pipeline and identical soundness gates,
    /// only the SAT engine differs: `sat_cadical::solve` returns Unsat solely
    /// with an LRAT proof the verified checker already accepted, and Sat
    /// models pass the same evaluator self-check as [`Solver::check`].
    ///
    /// Hidden from docs on purpose: the production entry point is `check` on
    /// the pure-Rust core (TR-004 — CaDiCaL is never load-bearing). This
    /// exists for the benchmark lanes and parity tests.
    #[doc(hidden)]
    #[cfg(all(feature = "cadical", not(target_family = "wasm")))]
    pub fn check_with_cadical(&self) -> CheckResult {
        Self::verdict(self.solve_pipeline_cadical())
    }

    #[cfg(all(feature = "cadical", not(target_family = "wasm")))]
    fn solve_pipeline_cadical(&self) -> Pipeline {
        use crate::sat_cadical::{self, CadicalVerdict};
        if self.assertions.is_empty() {
            return Pipeline::Sat(Env::new());
        }
        let Some((blaster, cnf, map)) = self.lower() else {
            return Pipeline::Unknown;
        };
        match sat_cadical::solve(&cnf) {
            // `solve` already fed the proof to `ordeal_lrat::check`; carry the
            // validated pair so the caller's Certificate re-checks offline.
            Ok(CadicalVerdict::Unsat { lrat }) => Pipeline::Unsat {
                certificate: Some(lrat.into_bytes()),
                cnf: cnf.clauses,
            },
            Ok(CadicalVerdict::Sat(assignment)) => {
                self.decode_and_check(&blaster, &map, &assignment)
            }
            // Every CaDiCaL error is conservative no-verdict.
            Err(_) => Pipeline::Unknown,
        }
    }
}

/// Internal pipeline outcome: like [`RawVerdict`] but carrying the
/// checker-validated certificate on UNSAT (None = checker rejected it).
/// How a solve is bounded (crate-internal): unbounded, a conflict budget
/// (DES-019), or a wall-clock deadline (TR-029). Exhaustion of either bound
/// surfaces uniformly as a conservative `Unknown`.
enum Bound {
    None,
    Conflicts(u64),
    Deadline(std::time::Instant),
}

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

    /// The consumer-facing parallelism guarantee (docs/consuming-ordeal.md
    /// "Parallelize across queries"): every API type is Send + Sync, so
    /// callers may fan independent queries out over a thread pool. A
    /// compile-time assertion — if a future field (Rc, RefCell, raw ptr)
    /// breaks it, this stops building rather than silently regressing the
    /// documented contract.
    #[test]
    fn api_types_are_send_and_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<Solver>();
        assert_send_sync::<BvTerm>();
        assert_send_sync::<crate::term::BoolTerm>();
        assert_send_sync::<CheckResult>();
        assert_send_sync::<Certificate>();
        assert_send_sync::<Model>();
        assert_send_sync::<CertificateError>();
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

    // ── TR-024: the public prove_valid primitive (issue #66) ─────────────

    /// A valid goal proves UNSAT with a re-checkable certificate. `x | 0 == x`
    /// holds for every 32-bit `x`.
    #[test]
    fn prove_valid_tautology_is_unsat_and_rechecks() {
        let x = var("x", 32);
        let goal = BoolTerm::Eq(
            b(BvTerm::Or(
                b(x.clone()),
                b(BvTerm::Const {
                    value: 0,
                    sort: crate::term::Sort::new(32),
                }),
            )),
            b(x),
        );
        match Solver::prove_valid(goal) {
            CheckResult::Unsat(cert) => cert.recheck().expect("valid goal's cert must re-check"),
            other => panic!("x | 0 == x must be valid, got {other:?}"),
        }
    }

    /// An invalid goal is `Sat` with a counterexample — the witness a
    /// translation validator reports.
    #[test]
    fn prove_valid_falsifiable_goal_yields_a_counterexample() {
        // `x + 1 == x` is false for every x; certainly not valid.
        let x = var("x", 32);
        let goal = BoolTerm::Eq(
            b(BvTerm::Add(
                b(x.clone()),
                b(BvTerm::Const {
                    value: 1,
                    sort: crate::term::Sort::new(32),
                }),
            )),
            b(x),
        );
        match Solver::prove_valid(goal) {
            CheckResult::Sat(_) => {}
            other => panic!("x + 1 == x must be falsifiable, got {other:?}"),
        }
    }

    /// The documented dual is exact: `prove_equiv(a, b)` == `prove_valid(Eq a b)`
    /// on the same query, both verdicts and (for UNSAT) both re-checkable.
    #[test]
    fn prove_valid_is_the_dual_of_prove_equiv() {
        let mk = || {
            let hi = var("hi", 32);
            let flags = var("flags", 8);
            let packed = BvTerm::Concat(b(hi), b(flags.clone()));
            let low8 = BvTerm::Extract {
                hi: 7,
                lo: 0,
                arg: b(packed),
            };
            (low8, flags)
        };
        let (a, bt) = mk();
        let via_equiv = Solver::prove_equiv(a, bt);
        let (a2, b2) = mk();
        let via_valid = Solver::prove_valid(BoolTerm::Eq(b(a2), b(b2)));
        assert!(
            matches!(via_equiv, CheckResult::Unsat(_))
                && matches!(via_valid, CheckResult::Unsat(_)),
            "prove_equiv and prove_valid(Eq) must agree: {via_equiv:?} vs {via_valid:?}"
        );
    }

    /// meld#338 REGRESSION GUARD (issue #66): meld's `fuse` truncated a
    /// `global.get`-first extended-const expr, folding `base + N` down to
    /// `base` and corrupting PIE data/element offsets. meld FIXED this
    /// (closed 2026-07-15); this is the check that would have caught it and
    /// now guards against its return. `base + N == base` must NOT be valid.
    #[test]
    fn meld_offset_fold_regression_guard() {
        let base = var("base", 32);
        let n = BvTerm::Const {
            value: 16,
            sort: crate::term::Sort::new(32),
        };
        let folded = BoolTerm::Eq(b(BvTerm::Add(b(base.clone()), b(n))), b(base));
        match Solver::prove_valid(folded) {
            // Sat ⟹ the fold is unsound (there is a `base` making base+16 ≠ base);
            // that counterexample is exactly what flags the miscompile.
            CheckResult::Sat(model) => {
                assert!(
                    model.assignments.iter().any(|(name, _)| name == "base"),
                    "counterexample must bind `base`"
                );
            }
            other => panic!("base + 16 == base must be falsifiable, got {other:?}"),
        }
    }

    // ── TR-026: propositional SAT front-end (issue #67, rivet#128) ───────

    /// An inconsistent feature model → UNSAT with a re-checkable certificate.
    /// Shape: a feature `a` both required (`a`) and excluded (`¬a`) — the
    /// simplest inconsistency rivet's variant checker must catch.
    #[test]
    fn check_cnf_inconsistent_model_is_unsat_and_rechecks() {
        let f = crate::cnf::CnfFormula {
            num_vars: 1,
            clauses: vec![vec![1], vec![-1]],
        };
        match Solver::check_cnf(&f) {
            CheckResult::Unsat(cert) => cert
                .recheck()
                .expect("propositional UNSAT must carry a re-checkable certificate"),
            other => panic!("a ∧ ¬a must be UNSAT, got {other:?}"),
        }
    }

    /// A consistent feature model → SAT with a configuration the model
    /// satisfies. Shape: `a → b` (¬a ∨ b) plus `a` required, so `b` is forced.
    #[test]
    fn check_cnf_consistent_model_yields_a_configuration() {
        let f = crate::cnf::CnfFormula {
            num_vars: 2,
            clauses: vec![vec![-1, 2], vec![1]],
        };
        match Solver::check_cnf(&f) {
            CheckResult::Sat(model) => {
                let get = |n: &str| {
                    model
                        .assignments
                        .iter()
                        .find(|(k, _)| k == n)
                        .map(|(_, v)| *v)
                };
                assert_eq!(get("v1"), Some(1), "a is required");
                assert_eq!(get("v2"), Some(1), "a → b forces b");
            }
            other => panic!("consistent model must be SAT, got {other:?}"),
        }
    }

    /// The certificate is over EXACTLY the caller's clauses — a consumer can
    /// re-check it against the formula it submitted, not a bit-blasted proxy.
    #[test]
    fn check_cnf_certificate_matches_the_submitted_clauses() {
        // Pigeonhole-ish tiny UNSAT: (x∨y) ∧ ¬x ∧ ¬y.
        let f = crate::cnf::CnfFormula {
            num_vars: 2,
            clauses: vec![vec![1, 2], vec![-1], vec![-2]],
        };
        match Solver::check_cnf(&f) {
            CheckResult::Unsat(cert) => {
                assert_eq!(
                    cert.cnf, f.clauses,
                    "certificate must carry the submitted CNF"
                );
                cert.recheck().expect("must re-check against those clauses");
            }
            other => panic!("expected UNSAT, got {other:?}"),
        }
    }

    /// The propositional path agrees with the bit-blaster path on a query
    /// expressible both ways: a single boolean variable `p`, asserted as
    /// `p ∧ ¬p`, is UNSAT whether encoded as CNF or as a BV1 equality.
    #[test]
    fn check_cnf_agrees_with_the_bitblaster_on_a_shared_query() {
        // CNF form: p ∧ ¬p.
        let via_cnf = Solver::check_cnf(&crate::cnf::CnfFormula {
            num_vars: 1,
            clauses: vec![vec![1], vec![-1]],
        });
        // BV form: (p == 1) ∧ (p == 0) over a 1-bit p.
        let p = var("p", 1);
        let one = BvTerm::Const {
            value: 1,
            sort: crate::term::Sort::new(1),
        };
        let zero = BvTerm::Const {
            value: 0,
            sort: crate::term::Sort::new(1),
        };
        let mut s = Solver::new();
        s.assert(BoolTerm::Eq(b(p.clone()), b(one)));
        s.assert(BoolTerm::Eq(b(p), b(zero)));
        let via_bv = s.check();
        assert!(
            matches!(via_cnf, CheckResult::Unsat(_)) && matches!(via_bv, CheckResult::Unsat(_)),
            "propositional and bit-blaster paths must agree: {via_cnf:?} vs {via_bv:?}"
        );
    }

    /// A feature-model-shaped consistency query (the rivet variant use case,
    /// #67): features core(1), tls(2), nomalloc(3); constraints "core
    /// required", "tls requires malloc" (¬tls ∨ ¬nomalloc). Selecting BOTH tls
    /// and nomalloc is inconsistent → UNSAT with a certificate a tool can
    /// re-check, turning "this config is invalid" into audit-grade evidence
    /// rather than an internal solver's say-so.
    #[test]
    fn check_cnf_feature_model_conflict_is_certified_unsat() {
        let f = crate::cnf::CnfFormula {
            num_vars: 3,
            clauses: vec![
                vec![1],      // core required
                vec![-2, -3], // tls → ¬nomalloc  (mutual exclusion)
                vec![2],      // tls selected
                vec![3],      // nomalloc selected  → conflict
            ],
        };
        match Solver::check_cnf(&f) {
            CheckResult::Unsat(cert) => cert.recheck().expect("conflict cert must re-check"),
            other => panic!("tls ∧ nomalloc must be inconsistent, got {other:?}"),
        }
        // Drop the conflicting selection and it is consistent (SAT).
        let ok = crate::cnf::CnfFormula {
            num_vars: 3,
            clauses: vec![vec![1], vec![-2, -3], vec![2]],
        };
        assert!(
            matches!(Solver::check_cnf(&ok), CheckResult::Sat(_)),
            "core+tls without nomalloc must be a valid configuration"
        );
    }

    // ── TR-029: wall-clock deadline + sliver prove_equiv (issue #71) ─────

    /// A hard query under a ~zero deadline abandons to Unknown — the safe
    /// revert loom's validator wants — never a wrong verdict.
    #[test]
    fn deadline_exhaustion_is_conservative_unknown() {
        let s = hard_mul_equivalence();
        match s.check_with_deadline(0) {
            CheckResult::Unknown => {}
            // A fast machine may legitimately decide before the first
            // conflict-site check; any DECIDED verdict must then be correct
            // (this query is UNSAT), never wrong.
            CheckResult::Unsat(cert) => cert.recheck().expect("decided-in-time cert must check"),
            CheckResult::Sat(m) => panic!("deadline must never yield a wrong verdict: {m:?}"),
        }
    }

    /// An easy query decides well inside a generous deadline, identically to
    /// plain check.
    #[test]
    fn deadline_generous_decides_normally() {
        let mut s = Solver::new();
        let x = var("x", 32);
        s.assert(BoolTerm::Ne(b(x.clone()), b(x)));
        match s.check_with_deadline(60_000) {
            CheckResult::Unsat(cert) => cert.recheck().expect("cert must re-check"),
            other => panic!("x != x must be UNSAT, got {other:?}"),
        }
    }

    /// Root-decided queries never hit the deadline site: A5 decides at a
    /// zero-millisecond deadline exactly as at a zero conflict budget.
    #[test]
    fn deadline_zero_still_root_decides() {
        match a5_mul_commutativity().check_with_deadline(0) {
            CheckResult::Unsat(cert) => cert.recheck().expect("root-decided cert must check"),
            other => panic!("canonicalized A5 must root-decide under any deadline, got {other:?}"),
        }
    }

    /// prove_equiv_sliver: the read-over-write law as a one-call equivalence
    /// over EXTENDED terms — Unsat with a re-checkable certificate.
    #[test]
    fn prove_equiv_sliver_read_over_write() {
        let (i, v) = (sym_bv32("i"), sym_bv8("v"));
        let read = sel(st(base("m"), i.clone(), v.clone()), i);
        match Solver::prove_equiv_sliver(read, v) {
            CheckResult::Unsat(cert) => cert.recheck().expect("cert must re-check"),
            other => panic!("select(store(m,i,v),i) ≡ v must prove, got {other:?}"),
        }
    }

    /// ...and it is not vacuous: two independent base reads are NOT
    /// equivalent (Sat with a witness).
    #[test]
    fn prove_equiv_sliver_distinct_reads_differ() {
        let r1 = sel(base("m"), sym_bv32("i"));
        let r2 = sel(base("m"), sym_bv32("j"));
        match Solver::prove_equiv_sliver(r1, r2) {
            CheckResult::Sat(_) => {}
            other => panic!("m[i] ≢ m[j] in general, got {other:?}"),
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
        // A symbolic index is IN the sliver as of TR-028, so the witness for
        // "out of sliver ⇒ conservative Unknown" is now a bad array sort: an
        // 8-bit index is not the BV32 the fixed BV32→BV8 sort demands.
        let bv8 = Sort::new(8);
        let bad_index = ExtBvTerm::Core(BvTerm::Var {
            name: "i".into(),
            sort: bv8,
        });
        let read = ExtBvTerm::Select {
            array: Box::new(ArrayTerm::Var { name: "a".into() }),
            index: Box::new(bad_index),
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

    // ── TR-028 semantics: symbolic read-over-write, end-to-end ───────────
    //
    // These check the ENCODING IS RIGHT, not merely that it lowers. Each
    // `Unsat` is certificate-checked by construction (check_sliver runs the
    // full pipeline), so a wrong encoding cannot pass by asserting itself.

    fn sym_bv32(name: &str) -> crate::sliver::ExtBvTerm {
        crate::sliver::ExtBvTerm::Core(BvTerm::Var {
            name: name.into(),
            sort: Sort::new(32),
        })
    }
    fn sym_bv8(name: &str) -> crate::sliver::ExtBvTerm {
        crate::sliver::ExtBvTerm::Core(BvTerm::Var {
            name: name.into(),
            sort: Sort::new(8),
        })
    }
    fn sel(a: crate::sliver::ArrayTerm, i: crate::sliver::ExtBvTerm) -> crate::sliver::ExtBvTerm {
        crate::sliver::ExtBvTerm::Select {
            array: Box::new(a),
            index: Box::new(i),
        }
    }
    fn st(
        a: crate::sliver::ArrayTerm,
        i: crate::sliver::ExtBvTerm,
        v: crate::sliver::ExtBvTerm,
    ) -> crate::sliver::ArrayTerm {
        crate::sliver::ArrayTerm::Store {
            array: Box::new(a),
            index: Box::new(i),
            value: Box::new(v),
        }
    }
    fn base(n: &str) -> crate::sliver::ArrayTerm {
        crate::sliver::ArrayTerm::Var { name: n.into() }
    }

    /// `select(store(a, i, v), i) = v` for a SYMBOLIC `i` — the defining law
    /// of read-over-write. Refuting it must be UNSAT with a checked cert.
    #[test]
    fn symbolic_read_over_write_same_index_is_valid() {
        use crate::sliver::ExtBoolTerm;
        let (i, v) = (sym_bv32("i"), sym_bv8("v"));
        let read = sel(st(base("a"), i.clone(), v.clone()), i);
        match Solver::check_sliver(&[ExtBoolTerm::Not(Box::new(ExtBoolTerm::Eq(read, v)))]) {
            CheckResult::Unsat(_) => {}
            other => panic!("select(store(a,i,v),i) must equal v; got {other:?}"),
        }
    }

    /// With `i ≠ j`, the store is invisible to the read: it must reduce to
    /// `select(a, j)`. This is the non-aliasing half of the law.
    #[test]
    fn symbolic_read_over_write_distinct_index_sees_through() {
        use crate::sliver::ExtBoolTerm;
        let (i, j, v) = (sym_bv32("i"), sym_bv32("j"), sym_bv8("v"));
        let read = sel(st(base("a"), i.clone(), v), j.clone());
        let underlying = sel(base("a"), j.clone());
        // i != j  ∧  read != select(a, j)   →   UNSAT
        let q = vec![
            ExtBoolTerm::Not(Box::new(ExtBoolTerm::Eq(i, j))),
            ExtBoolTerm::Not(Box::new(ExtBoolTerm::Eq(read, underlying))),
        ];
        match Solver::check_sliver(&q) {
            CheckResult::Unsat(_) => {}
            other => panic!("with i != j the store must be transparent; got {other:?}"),
        }
    }

    /// The oracle is NOT vacuous: without `i ≠ j` the store may well be
    /// visible, so the same equality must be falsifiable (SAT). If this ever
    /// returned UNSAT the encoding would be silently assuming non-aliasing.
    #[test]
    fn symbolic_read_over_write_does_not_assume_non_aliasing() {
        use crate::sliver::ExtBoolTerm;
        let (i, j, v) = (sym_bv32("i"), sym_bv32("j"), sym_bv8("v"));
        let read = sel(st(base("a"), i, v), j.clone());
        let underlying = sel(base("a"), j);
        match Solver::check_sliver(&[ExtBoolTerm::Not(Box::new(ExtBoolTerm::Eq(
            read, underlying,
        )))]) {
            CheckResult::Sat(_) => {}
            other => panic!("aliasing must stay possible without i != j; got {other:?}"),
        }
    }

    /// THE congruence test — the soundness core of symbolic indexing.
    ///
    /// `i = 5 → a[i] = a[5]`. Without array congruence the symbolic read
    /// `a[i]` and the concrete read `a[5]` are unrelated variables, and the
    /// solver would happily satisfy `i = 5 ∧ a[i] ≠ a[5]` — a spurious model
    /// that would let a consumer "prove" a false equivalence. Mutation-check:
    /// delete the `array_congruence` call in `lower_traced` and this test
    /// fails with Sat.
    #[test]
    fn symbolic_and_concrete_reads_are_congruent() {
        use crate::sliver::ExtBoolTerm;
        let i = sym_bv32("i");
        let five = crate::sliver::ExtBvTerm::Core(BvTerm::Const {
            value: 5,
            sort: Sort::new(32),
        });
        let q = vec![
            ExtBoolTerm::Eq(i.clone(), five.clone()),
            ExtBoolTerm::Not(Box::new(ExtBoolTerm::Eq(
                sel(base("a"), i),
                sel(base("a"), five),
            ))),
        ];
        match Solver::check_sliver(&q) {
            CheckResult::Unsat(_) => {}
            other => panic!("i = 5 must force a[i] = a[5] (missing congruence?); got {other:?}"),
        }
    }

    /// loom's actual shape (#70): a two-byte little-endian store/load chain
    /// over a SYMBOLIC base address. Must round-trip, and must DECIDE —
    /// this is precisely the query that used to revert to Unknown and take
    /// every memory-touching loom function with it.
    #[test]
    fn loom_multibyte_le_chain_over_symbolic_base_round_trips() {
        use crate::sliver::{ExtBoolTerm, ExtOp};
        let addr = sym_bv32("addr");
        let (b0, b1) = (sym_bv8("b0"), sym_bv8("b1"));
        let addr1 = crate::sliver::ExtBvTerm::Op(Box::new(ExtOp::Add(
            addr.clone(),
            crate::sliver::ExtBvTerm::Core(BvTerm::Const {
                value: 1,
                sort: Sort::new(32),
            }),
        )));
        // store b0 @ addr, b1 @ addr+1, then read both back.
        let mem = st(
            st(base("mem"), addr.clone(), b0.clone()),
            addr1.clone(),
            b1.clone(),
        );
        let q = vec![ExtBoolTerm::Not(Box::new(ExtBoolTerm::And(
            Box::new(ExtBoolTerm::Eq(sel(mem.clone(), addr1), b1)),
            Box::new(ExtBoolTerm::Eq(sel(mem, addr), b0)),
        )))];
        match Solver::check_sliver(&q) {
            CheckResult::Unsat(_) => {}
            other => panic!("loom's LE chain over a symbolic base must round-trip; got {other:?}"),
        }
    }
}

/// VER-008 — three-way SAT-backend parity: own pure-Rust CDCL core vs the
/// optional CaDiCaL accelerator vs the Z3 differential oracle, on the same
/// generated corpus the own-vs-Z3 differential uses. Lives here (not in
/// `sat_cadical`) because reproducing the pipeline's CNF for CaDiCaL needs
/// the private `Blaster`.
#[cfg(all(
    test,
    feature = "cadical",
    feature = "oracle",
    not(target_family = "wasm")
))]
mod cadical_parity_tests {
    use super::*;
    use crate::oracle::{OracleVerdict, gen_corpus, z3_check};
    use crate::sat_cadical::{self, CadicalVerdict};

    // rivet: verifies VER-008
    #[test]
    fn three_way_backend_parity_on_corpus() {
        let corpus = gen_corpus(0x5EED_0008, 150);
        let (mut agree_sat, mut agree_unsat, mut skipped) = (0u32, 0u32, 0u32);
        for (i, assertions) in corpus.iter().enumerate() {
            // Own core: the full production pipeline (Unsat is checker-gated),
            // deadline-bounded — a generated query can be genuinely hard
            // (the #97/#101 cross-circuit lesson), and parity over the
            // decided set is what this test claims.
            let mut solver = Solver::new();
            for a in assertions {
                solver.assert(a.clone());
            }
            let own = solver.check_with_deadline(10_000);
            if matches!(own, CheckResult::Unknown) {
                skipped += 1;
                continue;
            }

            // CaDiCaL: the identical CNF the pipeline solves, rebuilt through
            // the same canonicalize → blast → Tseitin steps.
            let mut blaster = Blaster::new();
            let mut roots = Vec::new();
            let mut blast_ok = true;
            for a in assertions {
                match blaster.blast_bool(&crate::canon::canonicalize_bool(a)) {
                    Ok(lit) => roots.push(lit),
                    Err(_) => blast_ok = false,
                }
            }
            assert!(blast_ok, "corpus query {i} failed to blast");
            let (cnf, _map) = tseitin(&blaster.aig, &roots);
            let cadical = match sat_cadical::solve_with_conflict_limit(&cnf, 200_000) {
                Ok(v) => v,
                Err(sat_cadical::CadicalError::Inconclusive) => {
                    skipped += 1;
                    continue;
                }
                Err(e) => panic!("CaDiCaL error on query {i}: {e:?}"),
            };

            // Z3: term-level differential oracle (Unknown never disagrees).
            let z3 = z3_check(assertions);

            match (&own, &cadical) {
                (CheckResult::Sat(_), CadicalVerdict::Sat(_)) => agree_sat += 1,
                (CheckResult::Unsat(_), CadicalVerdict::Unsat { .. }) => agree_unsat += 1,
                (own, cadical) => {
                    panic!("own vs CaDiCaL disagree on query {i}: own={own:?} cadical={cadical:?}")
                }
            }
            match (&own, &z3) {
                (CheckResult::Sat(_), OracleVerdict::Unsat)
                | (CheckResult::Unsat(_), OracleVerdict::Sat(_)) => {
                    panic!("own vs Z3 disagree on query {i}")
                }
                _ => {}
            }
        }
        // Parity over a one-sided or mostly-skipped corpus would be vacuous.
        assert!(
            agree_sat > 0 && agree_unsat > 0,
            "one-sided corpus: {agree_sat} sat / {agree_unsat} unsat ({skipped} skipped)"
        );
        assert!(
            skipped < 15,
            "too many undecided queries for the parity to mean anything: {skipped}/150"
        );
    }
}
