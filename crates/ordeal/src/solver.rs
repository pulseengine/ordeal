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
//! # Pipeline status (certificate-checked, term-checked since TR-070)
//!
//! Every entry point runs one pipeline (`solve_core`): blast → AIG →
//! Tseitin CNF → CDCL, then the trusted gate. The gate hands the trusted
//! `ordeal-lrat` crate the assertions flattened as asked, the DAG the
//! solver lowered them to, and the proof or the model; `Unsat` is returned
//! only once `check_term_dag` has related the term to the DAG and
//! `check_query` has re-encoded the DAG and checked the LRAT certificate
//! against the CNF it produced; `Sat` only once `check_term_dag`,
//! `check_query_model` and `check_input_value` have accepted the model
//! (after the untrusted evaluator's self-check, kept as defence in depth).
//! Anything rejected degrades to `Unknown` (AGENTS.md rule 1: no unchecked
//! `Unsat`, ever). What the gate leaves trusted: the 1:1 flattening of the
//! assertions (`dag::flatten`), the variable names, the sliver lowering and
//! the front ends (`docs/formal-verification.md`). The raw engine verdict
//! is exposed crate-internally for the differential oracle only.
//!
//! Trust status: the checker is small and dependency-free, and is tested
//! against mutated *certificates* (no code-mutation tool runs over it); its
//! formal soundness proof (Rust → Lean 4 via Aeneas, TR-013 / FEAT-002)
//! is **discharged** — sorry-free and CI-gated against the model regenerated
//! from `kernel.rs` before every proof build (TR-034).
//!
//! # The op-enablement gate (P1 kill criterion)
//!
//! Every operation's blasting rule ships oracle-verified (UV-005..UV-009).
//! If the differential oracle ever finds a disagreement, that op is added to
//! [`DISABLED_OPS`] and every query containing it returns `Unknown` until
//! the rule is fixed — the solver reverts to conservative, never guesses.

use crate::aig::AigOptions;
use crate::blast_kernel as k;
use crate::cnf::CnfFormula;
use crate::dag::{DagBuilder, no_hints, strash_hints};
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
    // The formerly derived ops (#192 phase 5).
    Not,
    Neg,
    Rotl,
    Sdiv,
    Srem,
}

/// How the formerly derived ops (`bvnot`, `bvneg`, `bvrotl`, `bvsdiv`,
/// `bvsrem`) reach the term DAG (#192 phase 5). Both settings lower through
/// the same proven `encode` / `compact` / `tseitin`; they differ in whether
/// the derived op is a node of its own.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DerivedOps {
    /// Rewrite them into the closed core BEFORE canonicalization
    /// (`lowering::expand_*`): the v0.27.0 lowering. Since v0.28.0 no
    /// production path uses it (maintainer decision, #192 phase 5); it is
    /// kept only so the differential tests can compare the old rewrite
    /// against the proven nodes.
    #[cfg_attr(not(test), allow(dead_code))]
    Rewrite,
    /// Keep them as their own `DagNode`s, encoded by the proven composite
    /// rules (`blast_kernel::blast_bvnot` … `blast_srem`), so the
    /// `ordeal-cert/v2` query block carries the operation itself and the
    /// trusted re-check covers it. Every production path since v0.28.0.
    Nodes,
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
        BvTerm::Not(..) => OpKind::Not,
        BvTerm::Neg(..) => OpKind::Neg,
        BvTerm::Rotl(..) => OpKind::Rotl,
        BvTerm::Sdiv(..) => OpKind::Sdiv,
        BvTerm::Srem(..) => OpKind::Srem,
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
        | BvTerm::Rotl(a, b)
        | BvTerm::Sdiv(a, b)
        | BvTerm::Srem(a, b)
        | BvTerm::Concat(a, b) => bv_uses_disabled(a) || bv_uses_disabled(b),
        BvTerm::Extract { arg, .. }
        | BvTerm::ZeroExt { arg, .. }
        | BvTerm::SignExt { arg, .. }
        | BvTerm::Not(arg)
        | BvTerm::Neg(arg) => bv_uses_disabled(arg),
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

/// The lowered query (issue #192 phase 3): the arena the CNF was encoded
/// from — built by the Lean-proven `blast_kernel::encode` over the term
/// DAG and compacted by the proven `blast_kernel::compact` — and the word
/// of every variable in it, for model decoding.
struct Blaster {
    /// Read by the #192 measurement harness only.
    #[cfg_attr(not(test), allow(dead_code))]
    aig: k::Aig,
    vars: HashMap<String, Vec<k::Lit>>,
    /// Input-creation order, for model decoding.
    var_order: Vec<(String, u32)>,
    /// The lowered query (#192 phase 4): the DAG, its constant table, the
    /// roots and the compaction hints the CNF was produced from — what an
    /// `ordeal-cert/v2` certificate carries so the trusted crate can
    /// re-encode it. `None` for the measurement-only configurations that
    /// skip compaction (the re-check always compacts).
    query: Option<crate::query::QueryDag>,
    /// The builder's variable map `(name, width, Var node)` (#192 phase 6):
    /// what turns a model into the DAG's input assignment for the trusted
    /// `check_query_model`, and what the `ordeal-cert/v2` SAT bundle
    /// carries so a reader can confirm the model IS that assignment.
    query_vars: Vec<(String, u32, usize)>,
}

impl Blaster {
    /// The number of AND gates in the arena (the #192 measurements).
    #[cfg_attr(not(test), allow(dead_code))]
    fn num_ands(&self) -> usize {
        self.aig
            .nodes
            .iter()
            .filter(|n| matches!(n, k::Node::And(..)))
            .count()
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
    /// The EXTENDED query this solver was built from
    /// ([`Solver::from_sliver`], TR-072), when it was: `assertions` is its
    /// lowering, and the trusted gate re-lowers it and runs
    /// `check_sliver_lowering` before the term and query checks. A later
    /// [`Solver::assert`] is appended here too (as a closed extended
    /// term) and the lowering is redone, so the two never drift.
    ext: Option<Vec<crate::sliver::ExtBoolTerm>>,
}

impl Solver {
    /// Create an empty solver with no assertions.
    pub fn new() -> Self {
        Self {
            assertions: Vec::new(),
            ext: None,
        }
    }

    /// The assertions added so far, in order (read-only). Lets an
    /// independent oracle, such as the fuzz target's brute-force evaluator
    /// check (#187), judge a verdict against the query rather than the CNF.
    pub fn assertions(&self) -> &[BoolTerm] {
        &self.assertions
    }

    /// Add a boolean assertion to the conjunction to be checked. On a
    /// solver built by [`Solver::from_sliver`] the assertion joins the
    /// extended query (as a closed extended term) and the lowering is
    /// redone, so the sliver gate still sees the whole query.
    pub fn assert(&mut self, term: BoolTerm) {
        if let Some(ext) = &mut self.ext {
            ext.push(crate::sliver::ext_of_core(&term));
            // A closed term never leaves the sliver; the lowering of the
            // extended list it joined was already accepted.
            if let Ok(lowered) = crate::sliver::lower(ext) {
                self.assertions = lowered;
                return;
            }
        }
        self.assertions.push(term);
    }

    /// Whether this solver was built from an extended query
    /// ([`Solver::from_sliver`]): then every verdict also rests on the
    /// trusted `check_sliver_lowering`, and
    /// [`Solver::check_sliver_with_term`] returns the extended certificate.
    pub fn is_sliver(&self) -> bool {
        self.ext.is_some()
    }

    /// Number of assertions accumulated so far.
    pub fn num_assertions(&self) -> usize {
        self.assertions.len()
    }

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

    /// Lower an **extended (array/UF sliver) query** into a [`Solver`] over
    /// the closed core, or say why it is outside the sliver (#236).
    ///
    /// The sliver is eliminated by [`crate::sliver::lower`]: eager
    /// read-over-write for `Array(BV32→BV8)` select/store over concrete
    /// **or symbolic** BV32 indices (TR-028), and Ackermannization for
    /// uninterpreted `pure_call` congruence. The returned solver holds the
    /// lowered assertions, so every entry point applies to it unchanged —
    /// [`Solver::check`], [`Solver::check_with_deadline`],
    /// [`Solver::check_with_limit`], [`Solver::check_with_query`].
    ///
    /// Use this rather than [`Solver::check_sliver`] when a refusal must be
    /// told apart from an undecided verdict: an out-of-sliver query (a bad
    /// array sort or an inconsistent call signature) is an `Err`, not
    /// [`CheckResult::Unknown`]. Note that the elimination itself runs here,
    /// before any bound you later apply to the search; it is quadratic in
    /// the reads of one base array.
    pub fn from_sliver(
        assertions: &[crate::sliver::ExtBoolTerm],
    ) -> Result<Solver, crate::sliver::SliverError> {
        let lowered = crate::sliver::lower(assertions)?;
        Ok(Solver {
            assertions: lowered,
            ext: Some(assertions.to_vec()),
        })
    }

    /// Decide an EXTENDED query (a solver built by [`Solver::from_sliver`])
    /// and return, with the v3 term certificate about the lowered core,
    /// the `ext` block relating that core to the query as asked (TR-072,
    /// `ordeal-cert/v4`): the extended query flattened
    /// ([`crate::sliver::flatten_ext`]), the untrusted map from its nodes
    /// to the core's and the read / call tables. The trusted
    /// `ordeal_lrat::check_sliver_lowering` verifies — BEFORE a verdict is
    /// returned, on every entry point of such a solver — that the core is
    /// the read-over-write, Ackermann and congruence elimination of the
    /// extended query, so the proof (`check_sliver_unsat_sound`: unsat
    /// under EVERY array and UF interpretation) or the model
    /// (`check_sliver_model_sound`: an interpretation built from the model
    /// satisfies the extended query) is about the question loom asked.
    /// Anything the trusted crate rejects degrades to `Unknown`; on a
    /// solver not built from the sliver the result is `Unknown` too (use
    /// [`Solver::check_with_term`]).
    pub fn check_sliver_with_term(&self) -> crate::query::SliverCheckResult {
        use crate::query::SliverCheckResult;
        match self.solve_core(Bound::None) {
            Outcome::Unsat(_, Some(sliver)) => SliverCheckResult::Unsat(*sliver),
            Outcome::Sat(_, Some(sliver)) => SliverCheckResult::Sat(*sliver),
            _ => SliverCheckResult::Unknown,
        }
    }

    /// One-shot decision for an **extended (array/UF sliver) query**:
    /// [`Solver::from_sliver`] then the unbounded [`Solver::check`].
    ///
    /// An **out-of-sliver** query (any [`crate::sliver::SliverError`])
    /// returns [`CheckResult::Unknown`]: conservative by construction, never
    /// a guess — but indistinguishable from an undecided verdict. Callers
    /// that need the refusal, or a bound, use [`Solver::from_sliver`] or the
    /// bounded twins [`Solver::check_sliver_with_deadline`] /
    /// [`Solver::check_sliver_with_limit`]. Soundness is unchanged from
    /// `check` — no array/UF construct ever reaches the bit-blaster; only the
    /// lowered core does.
    pub fn check_sliver(assertions: &[crate::sliver::ExtBoolTerm]) -> CheckResult {
        match Self::from_sliver(assertions) {
            Ok(solver) => solver.check(),
            // Out-of-sliver: conservative Unknown (callers must not optimize).
            Err(_) => CheckResult::Unknown,
        }
    }

    /// [`Solver::check_sliver`] under a **wall-clock deadline** (#236): the
    /// sliver twin of [`Solver::check_with_deadline`]. The clock starts
    /// before the sliver is lowered, so array elimination counts against
    /// `timeout_ms`; on expiry the result is [`CheckResult::Unknown`], never
    /// a wrong or unchecked verdict. As in the core twin, lowering and
    /// blasting are not interrupted mid-way — the deadline governs the SAT
    /// search, which starts with whatever budget lowering left.
    /// Out-of-sliver input is `Unknown`; use [`Solver::from_sliver`] to see
    /// the refusal.
    pub fn check_sliver_with_deadline(
        assertions: &[crate::sliver::ExtBoolTerm],
        timeout_ms: u64,
    ) -> CheckResult {
        let deadline = std::time::Instant::now() + std::time::Duration::from_millis(timeout_ms);
        match Self::from_sliver(assertions) {
            Ok(solver) => Self::verdict(solver.solve_core(Bound::Deadline(deadline))),
            Err(_) => CheckResult::Unknown,
        }
    }

    /// [`Solver::check_sliver`] under a **conflict budget** (#236): the
    /// sliver twin of [`Solver::check_with_limit`]. Exhaustion is
    /// [`CheckResult::Unknown`]; out-of-sliver input is `Unknown` too (use
    /// [`Solver::from_sliver`] to see the refusal).
    pub fn check_sliver_with_limit(
        assertions: &[crate::sliver::ExtBoolTerm],
        max_conflicts: u64,
    ) -> CheckResult {
        match Self::from_sliver(assertions) {
            Ok(solver) => solver.check_with_limit(max_conflicts),
            Err(_) => CheckResult::Unknown,
        }
    }

    /// Check that every assertion is well-sorted, reporting the first
    /// violation with a distinct error (TR-010). `check` treats ill-sorted
    /// input as `Unknown`; this gives callers the actionable diagnosis.
    ///
    /// Beyond per-operator sortedness this also demands a CONSISTENT width
    /// for every variable name across the whole assertion set: two `Var`s
    /// sharing a name at different widths are each locally well-sorted, yet
    /// the blaster binds variables by name — fuzz-found (#139): such input
    /// previously reached a blaster width assert and panicked instead of
    /// returning the contractual `Unknown`.
    pub fn validate(&self) -> Result<(), EvalError> {
        for a in &self.assertions {
            validate_bool(a)?;
        }
        let mut widths: std::collections::HashMap<&str, u32> = std::collections::HashMap::new();
        for a in &self.assertions {
            check_var_widths_bool(a, &mut widths)?;
        }
        Ok(())
    }

    /// Decide satisfiability of the conjunction of all asserted terms.
    ///
    /// Pipeline: blast → AIG → Tseitin CNF → CDCL, then the **trusted gate**
    /// (TR-070, v0.32.0): the answer is only returned once the trusted
    /// `ordeal-lrat` crate has related the assertions, flattened as asked,
    /// to the DAG the solver built from them (`check_term_dag`,
    /// `check_term_dag_sound`) and, on engine-UNSAT, re-encoded that DAG and
    /// checked the LRAT certificate against the CNF *it* produced
    /// (`check_query`, `check_term_unsat_sound`) — or, on engine-SAT,
    /// evaluated every root of the DAG under the model (`check_query_model`)
    /// and bound every model value through the term's own variable map
    /// (`check_input_value`, `check_term_model_sound`). The model is also
    /// re-evaluated against every assertion by the untrusted evaluator first
    /// (defence in depth). The proof is checked once, by `check_query`.
    /// Anything the trusted crate rejects degrades to `Unknown`, which is
    /// always sound — an unchecked `Unsat` or `Sat` is never reported. The
    /// certificate and the model are byte-for-byte what v0.31.0 returned;
    /// [`Solver::check_with_term`] exposes the term and the DAG the gate
    /// checked.
    pub fn check(&self) -> CheckResult {
        Self::verdict(self.solve_core(Bound::None))
    }

    /// Decide satisfiability under a conflict budget (DES-019 / TR-016).
    ///
    /// Runs the identical pipeline as [`Solver::check`] — blast → AIG →
    /// Tseitin CNF → bounded CDCL, then the same trusted gate — but caps the
    /// SAT core at `max_conflicts` search conflicts. On budget exhaustion
    /// the core reaches no verdict and this returns
    /// [`CheckResult::Unknown`]; on any decided verdict it behaves exactly
    /// like `check`.
    ///
    /// The budget bounds only completeness: the trusted gate and the model
    /// self-check are untouched, so an exhausted budget yields `Unknown` and
    /// never a wrong or unchecked verdict.
    pub fn check_with_limit(&self, max_conflicts: u64) -> CheckResult {
        Self::verdict(self.solve_core(Bound::Conflicts(max_conflicts)))
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
    /// budget). Blasting/canonicalization time is not bounded, nor is the
    /// trusted gate after the search — the deadline governs the SAT search,
    /// which dominates on hard queries.
    pub fn check_with_deadline(&self, timeout_ms: u64) -> CheckResult {
        let deadline = std::time::Instant::now() + std::time::Duration::from_millis(timeout_ms);
        Self::verdict(self.solve_core(Bound::Deadline(deadline)))
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
    ///   `0`/`1` (a consistent configuration). The assignment is re-checked by
    ///   `ordeal_lrat::check_sat` (the trusted, machine-checked kernel) before
    ///   return, in release builds too.
    /// - [`CheckResult::Unknown`] ⟹ conservative — only if the checker
    ///   rejects ordeal's own certificate or model (an ordeal bug, never a
    ///   wrong verdict).
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
                // Re-check the model with the TRUSTED kernel before return, in
                // every build profile (issue #184: this was a debug_assert, so
                // release builds returned `Sat` unchecked). A rejected model is
                // an ordeal bug and degrades to `Unknown`, never a wrong `Sat`.
                let verdict = cnf_sat_verdict(formula, &assignment);
                debug_assert!(
                    matches!(verdict, CheckResult::Sat(_)),
                    "SAT model must satisfy the formula — ordeal bug"
                );
                verdict
            }
        }
    }

    /// Map the core's gated outcome to the caller-facing verdict: the
    /// certificate (CNF + LRAT) or the model, as every entry point returned
    /// them before TR-070 — the term and the query the gate checked are
    /// dropped here and kept by [`Solver::check_with_term`].
    fn verdict(outcome: Outcome) -> CheckResult {
        match outcome {
            Outcome::Sat(cert, _) => CheckResult::Sat(cert.query.witness.model),
            Outcome::Unsat(cert, _) => CheckResult::Unsat(cert.query.certificate),
            // The trusted crate rejected our own certificate, model, term
            // map or sliver tables: an ordeal bug, but a sound outcome —
            // degrade to Unknown rather than assert a verdict.
            Outcome::Unknown => CheckResult::Unknown,
        }
    }

    /// The term-level projection of an outcome: what
    /// [`Solver::check_with_term`] returns (the sliver block, if any, was
    /// checked and is dropped here).
    fn term_outcome(outcome: Outcome) -> crate::query::TermCheckResult {
        use crate::query::TermCheckResult;
        match outcome {
            Outcome::Sat(cert, _) => TermCheckResult::Sat(cert),
            Outcome::Unsat(cert, _) => TermCheckResult::Unsat(cert),
            Outcome::Unknown => TermCheckResult::Unknown,
        }
    }

    /// The engine's raw verdict — crate-internal, differential oracle only.
    #[cfg(any(test, feature = "oracle"))]
    pub(crate) fn check_raw(&self) -> RawVerdict {
        match self.solve_core(Bound::None) {
            Outcome::Sat(cert, _) => {
                RawVerdict::Sat(cert.query.witness.model.assignments.into_iter().collect())
            }
            Outcome::Unsat(_, _) => RawVerdict::Unsat,
            Outcome::Unknown => RawVerdict::Unknown,
        }
    }

    /// **The one pipeline every entry point runs** (TR-070): lower, search
    /// under `bound`, then the trusted gate — [`Solver::gate_unsat`] or
    /// [`Solver::gate_sat`] — whose acceptance is what the returned verdict
    /// rests on. `check` / `check_with_limit` / `check_with_deadline` keep
    /// the certificate or the model of the result, `check_with_witness` the
    /// witness, `check_with_query` the query, `check_with_term` all of it.
    /// An exhausted bound, a refused lowering (disabled op, ill-sorted
    /// input) and a rejection by the trusted crate all surface as
    /// [`crate::query::TermCheckResult::Unknown`].
    fn solve_core(&self, bound: Bound) -> Outcome {
        use crate::query::{QueryInputs, QuerySatCertificate, QueryTerm, TermSatCertificate};
        use crate::witness::SatCertificate;
        if self.assertions.is_empty() {
            // An empty conjunction is trivially satisfiable by the empty
            // model: the empty witness re-checks vacuously (no clauses, no
            // bindings), and so do the empty query and the empty term (no
            // roots to evaluate, no nodes to relate). An empty EXTENDED
            // query likewise: its block is empty and the trusted check
            // accepts it; the gate below handles it uniformly.
            let cert = TermSatCertificate {
                query: QuerySatCertificate {
                    witness: SatCertificate {
                        model: Model {
                            assignments: Vec::new(),
                        },
                        cnf: Vec::new(),
                        assignment: Vec::new(),
                        bit_map: Vec::new(),
                    },
                    query: crate::query::QueryDag::default(),
                    inputs: QueryInputs::default(),
                },
                term: QueryTerm::default(),
            };
            return match &self.ext {
                None => Outcome::Sat(cert, None),
                Some(_) => self.gate_sat_sliver(cert),
            };
        }
        let Some((mut blaster, cnf)) = self.lower() else {
            return Outcome::Unknown;
        };
        // `lower()` always compacts, so the lowered query is always there;
        // moved out, not cloned. (Unknown is the sound answer regardless.)
        let Some(query) = blaster.query.take() else {
            return Outcome::Unknown;
        };
        let vars = std::mem::take(&mut blaster.query_vars);
        let mut sat_solver = SatSolver::new();
        let verdict = match bound {
            // Bounded solve: exhaustion ⇒ no verdict ⇒ conservative Unknown
            // (soundness contract preserved) — identically for a conflict
            // budget and a wall-clock deadline.
            Bound::Conflicts(max) => match sat_solver.solve_with_budget(&cnf, max) {
                Some(v) => v,
                None => return Outcome::Unknown,
            },
            Bound::Deadline(d) => match sat_solver.solve_with_deadline(&cnf, d) {
                Some(v) => v,
                None => return Outcome::Unknown,
            },
            Bound::None => sat_solver.solve(&cnf),
        };
        match verdict {
            SatResult::Unsat => {
                // Emit the LRAT certificate from the proof trace; the trusted
                // gate checks it (once, inside `check_query`, against the
                // CNF the trusted crate re-encodes from the query) BEFORE
                // UNSAT is asserted. The carried CNF is the solver's, checked
                // equal to the re-encoding, so the caller's Certificate is a
                // self-contained, independently re-checkable proof.
                let lrat =
                    crate::lrat::emit_lrat_trimmed(cnf.clauses.len(), sat_solver.proof_trace());
                self.gate_unsat(
                    query,
                    &vars,
                    Certificate {
                        lrat: lrat.into_bytes(),
                        cnf: cnf.clauses,
                    },
                )
            }
            SatResult::Sat(assignment) => {
                self.gate_sat(query, &vars, &blaster, cnf.clauses, assignment)
            }
        }
    }

    /// The trusted UNSAT gate of every entry point (TR-070): flatten the
    /// assertions as asked and map them onto the lowered `query`
    /// (`dag::flatten` / `dag::term_map`, untrusted advice), then the
    /// trusted crate verifies the DAG is a semantics-preserving rewrite of
    /// the term along the map (`check_term_dag`), re-encodes the DAG and
    /// checks the LRAT proof against the CNF it produced (`check_query`),
    /// which must equal the carried CNF. `Unsat` only on acceptance
    /// (`check_term_unsat_sound`: the proof refutes the TERM); a rejection
    /// degrades to `Unknown`.
    fn gate_unsat(
        &self,
        query: crate::query::QueryDag,
        vars: &[(String, u32, usize)],
        certificate: Certificate,
    ) -> Outcome {
        use crate::query::{QueryCertificate, QueryTerm, SliverCertificate, TermCertificate};
        // A sliver solver (TR-072): the term is the lowered core, hash-consed
        // with the tables' witness nodes, and the `ext` block relates the
        // extended query to it; the trusted `check_sliver_lowering` runs
        // first. A core solver: the assertions flattened as asked.
        let (term, sliver) = match &self.ext {
            Some(ext) => {
                let Ok(trace) = crate::sliver::lower_ext(ext) else {
                    return Outcome::Unknown;
                };
                let Ok((term, block)) = QueryTerm::flatten_sliver(&trace, &query, vars) else {
                    return Outcome::Unknown;
                };
                (term, Some(block))
            }
            None => {
                let Ok(term) = QueryTerm::flatten(&self.assertions, &query, vars) else {
                    return Outcome::Unknown;
                };
                (term, None)
            }
        };
        let (term, tampered) = tamper::apply(term);
        let cert = TermCertificate {
            query: QueryCertificate { certificate, query },
            term,
        };
        let result = match sliver {
            Some(block) => {
                let (block, tampered_block) = tamper::apply_sliver(block);
                let sliver = SliverCertificate {
                    term: cert,
                    sliver: block,
                };
                let outcome = match sliver.recheck() {
                    Ok(()) => Outcome::Unsat(sliver.term.clone(), Some(Box::new(sliver))),
                    Err(_) => Outcome::Unknown,
                };
                debug_assert!(
                    tampered
                        || tampered_block
                        || tamper::lowering_tampered()
                        || !matches!(outcome, Outcome::Unknown),
                    "trusted crate rejected our certificate, term map or sliver block — ordeal bug"
                );
                return outcome;
            }
            None => match cert.recheck() {
                Ok(()) => Outcome::Unsat(cert, None),
                Err(_) => Outcome::Unknown,
            },
        };
        debug_assert!(
            tampered || !matches!(result, Outcome::Unknown),
            "trusted crate rejected our certificate or term map — ordeal bug"
        );
        result
    }

    /// The sliver SAT gate for the EMPTY extended query (every root
    /// trivially true; the block is empty and the trusted check accepts an
    /// empty extended query against an empty core).
    fn gate_sat_sliver(&self, cert: crate::query::TermSatCertificate) -> Outcome {
        use crate::query::{QueryTerm, SliverSatCertificate};
        let Some(ext) = &self.ext else {
            return Outcome::Unknown;
        };
        let Ok(trace) = crate::sliver::lower_ext(ext) else {
            return Outcome::Unknown;
        };
        let Ok((term, block)) = QueryTerm::flatten_sliver(&trace, &cert.query.query, &[]) else {
            return Outcome::Unknown;
        };
        let Some(model) = block.pullback_model(&term, &cert.query.witness.model) else {
            return Outcome::Unknown;
        };
        let sliver = SliverSatCertificate {
            term: crate::query::TermSatCertificate { term, ..cert },
            sliver: block,
            model,
        };
        match sliver.recheck() {
            Ok(()) => Outcome::Sat(sliver.term.clone(), Some(Box::new(sliver))),
            Err(_) => Outcome::Unknown,
        }
    }

    /// The trusted SAT gate of every entry point (TR-070): the model is
    /// decoded and re-evaluated against the ORIGINAL assertions by the
    /// untrusted evaluator (defence in depth, [`Solver::decode_and_check`]),
    /// packed into the CNF-level witness, turned into the DAG's input
    /// assignment, and the assertions are flattened and mapped as for
    /// UNSAT; then the trusted crate verifies the term-to-DAG
    /// correspondence (`check_term_dag`), the witness (`check_sat` /
    /// `check_binding`), that EVERY root of the DAG is true under the
    /// inputs (`check_query_model`) and that every model value is the
    /// inputs at its term variable's image (`var_offset` /
    /// `check_input_value`). `Sat` only on acceptance
    /// (`check_term_model_sound`: the model satisfies the TERM); a rejection
    /// degrades to `Unknown`.
    fn gate_sat(
        &self,
        query: crate::query::QueryDag,
        vars: &[(String, u32, usize)],
        blaster: &Blaster,
        cnf: Vec<Vec<i32>>,
        assignment: Vec<bool>,
    ) -> Outcome {
        use crate::query::{
            QueryInputs, QuerySatCertificate, QueryTerm, SliverSatCertificate, TermSatCertificate,
        };
        use crate::witness::SatCertificate;
        let Some(env) = self.decode_and_check(blaster, &assignment) else {
            return Outcome::Unknown;
        };
        let mut assignments: Vec<(String, u128)> = env.into_iter().collect();
        assignments.sort();
        let mut bit_map: Vec<(String, u32, Vec<i32>)> = Vec::with_capacity(blaster.var_order.len());
        for (name, width) in &blaster.var_order {
            let word = &blaster.vars[name];
            let bits: Vec<i32> = word.iter().map(|l| k::cnf_lit(*l)).collect();
            bit_map.push((name.clone(), *width, bits));
        }
        let witness = SatCertificate {
            model: Model { assignments },
            cnf,
            assignment,
            bit_map,
        };
        let inputs = QueryInputs::from_model(&query, vars, &witness.model);
        let (term, sliver) = match &self.ext {
            Some(ext) => {
                let Ok(trace) = crate::sliver::lower_ext(ext) else {
                    return Outcome::Unknown;
                };
                let Ok((term, block)) = QueryTerm::flatten_sliver(&trace, &query, vars) else {
                    return Outcome::Unknown;
                };
                (term, Some(block))
            }
            None => {
                let Ok(term) = QueryTerm::flatten(&self.assertions, &query, vars) else {
                    return Outcome::Unknown;
                };
                (term, None)
            }
        };
        let (term, tampered) = tamper::apply(term);
        let cert = TermSatCertificate {
            query: QuerySatCertificate {
                witness,
                query,
                inputs,
            },
            term,
        };
        match sliver {
            Some(block) => {
                let (block, tampered_block) = tamper::apply_sliver(block);
                // The extended model: the pullback of the core model through
                // the tables (what `check_sliver_model_sound` builds).
                let Some(model) = block.pullback_model(&cert.term, &cert.query.witness.model)
                else {
                    return Outcome::Unknown;
                };
                let sliver = SliverSatCertificate {
                    term: cert,
                    sliver: block,
                    model,
                };
                let outcome = match sliver.recheck() {
                    Ok(()) => Outcome::Sat(sliver.term.clone(), Some(Box::new(sliver))),
                    Err(_) => Outcome::Unknown,
                };
                debug_assert!(
                    tampered
                        || tampered_block
                        || tamper::lowering_tampered()
                        || !matches!(outcome, Outcome::Unknown),
                    "trusted crate rejected our model, term map or sliver block — ordeal bug"
                );
                outcome
            }
            None => {
                let outcome = match cert.recheck() {
                    Ok(()) => Outcome::Sat(cert, None),
                    Err(_) => Outcome::Unknown,
                };
                debug_assert!(
                    tampered || !matches!(outcome, Outcome::Unknown),
                    "trusted crate rejected our model or term map — ordeal bug"
                );
                outcome
            }
        }
    }

    /// The pipeline's front half — validation, canonicalization, blasting,
    /// Tseitin — shared by every backend. `None` means conservative Unknown
    /// (disabled ops or ill-sorted input; `validate()` diagnoses).
    fn lower(&self) -> Option<(Blaster, CnfFormula)> {
        // The derived ops are lowered as PROVEN DAG nodes on the default
        // path (#192 phase 5; maintainer decision 2026-10-13, v0.28.0), so
        // the lowering.rs rewrite is no longer on any unsat answer's trust
        // path. This changes the emitted certificates of some queries with
        // `bvsdiv` / `bvsrem` operands (CNF variables renumbered, verdicts
        // unchanged; docs/design/query-cnf-gap.md, phase 5).
        self.lower_with(AigOptions::default(), DerivedOps::Nodes)
    }

    /// `lower` with explicit simplification settings. The production path
    /// is `lower()` (= the default options: folding and hashing); the
    /// other settings exist for the #192 CNF-size / time measurement
    /// (`cnf_gap_measurement` below) and yield a simulation-identical AIG.
    ///
    /// Issue #192 phase 3: this is the formally covered path. The
    /// canonicalized assertions become a term DAG (`dag::DagBuilder`,
    /// untrusted glue), the Lean-proven `blast_kernel::encode` builds the
    /// raw AIG by calling the proven rule for every node
    /// (`encode_sound`), the proven `blast_kernel::compact` folds and
    /// hashes it (`compact_sound`; the hints are untrusted advice it
    /// checks), and the proven `blast_kernel::tseitin` emits the CNF
    /// (`tseitin_sat_preserving`). `dag_refuted` in
    /// `lean/BlasterCapstone.lean` composes the three with
    /// `lrat_check_sound`: a certificate the checker accepts refutes the
    /// DAG, not only the CNF.
    fn lower_with(
        &self,
        options: AigOptions,
        derived: DerivedOps,
    ) -> Option<(Blaster, CnfFormula)> {
        if self.assertions.iter().any(bool_uses_disabled) {
            return None;
        }
        // Ill-sorted input never reaches a blast rule: conservative Unknown.
        if self.validate().is_err() {
            return None;
        }
        let mut builder = DagBuilder::new(options.strash);
        for a in &self.assertions {
            // #192 phase 5: on the default path the formerly derived ops are
            // rewritten into the core first (the v0.27.0 lowering, so the
            // shipped bytes are unchanged); on the query-carrying path they
            // stay nodes with proven rules. Untrusted either way.
            let a = match derived {
                DerivedOps::Rewrite => match crate::lowering::expand_bool(a) {
                    Ok(t) => t,
                    Err(_) => return None,
                },
                DerivedOps::Nodes => a.clone(),
            };
            // Untrusted canonicalization above the AIG (issue #35 / TR-009):
            // commutative-operand ordering + const-folding so equal-but-
            // structurally-different terms share a node. Soundness is unaffected
            // — Unsat stays LRAT-checked, and the SAT model self-check
            // re-evaluates against the ORIGINAL assertions.
            let a = crate::canon::canonicalize_bool(&a);
            if builder.assert_root(&a).is_err() {
                return None;
            }
        }
        let dag = builder.finish();
        let mut raw = k::aig_new();
        let (words, outs) = k::encode(&mut raw, &dag.nodes, &dag.bits, &dag.roots);
        let (aig, outs, var_words, query): (
            k::Aig,
            Vec<k::Lit>,
            Vec<Vec<k::Lit>>,
            Option<crate::query::QueryDag>,
        ) = if options.fold {
            let hints = if options.strash {
                strash_hints(&raw)
            } else {
                no_hints(&raw)
            };
            let (aig, map) = k::compact(&raw, &hints);
            let outs = k::map_word(&map, &outs);
            let var_words = dag
                .vars
                .iter()
                .map(|(_, _, n)| k::map_word(&map, &words[*n]))
                .collect();
            let query = crate::query::QueryDag {
                nodes: dag.nodes,
                bits: dag.bits,
                roots: dag.roots,
                hints,
            };
            (aig, outs, var_words, Some(query))
        } else {
            let var_words = dag.vars.iter().map(|(_, _, n)| words[*n].clone()).collect();
            (raw, outs, var_words, None)
        };
        let clauses = k::tseitin(&aig, &outs);
        let cnf = CnfFormula {
            num_vars: aig.nodes.len() as u32,
            clauses,
        };
        let mut vars = HashMap::new();
        let mut var_order = Vec::with_capacity(dag.vars.len());
        for ((name, width, _), word) in dag.vars.iter().zip(var_words) {
            vars.insert(name.clone(), word);
            var_order.push((name.clone(), *width));
        }
        Some((
            Blaster {
                aig,
                vars,
                var_order,
                query,
                query_vars: dag.vars,
            },
            cnf,
        ))
    }

    /// Decode a SAT assignment into a model and self-check it against the
    /// ORIGINAL assertions with the untrusted evaluator — shared by every
    /// backend, and defence in depth under the trusted gate
    /// ([`Solver::gate_sat`]). A failing self-check means an ordeal bug; the
    /// outcome degrades to Unknown (`None`), never a wrong Sat.
    fn decode_and_check(&self, blaster: &Blaster, assignment: &[bool]) -> Option<Env> {
        let mut env = Env::new();
        for (name, _width) in &blaster.var_order {
            let word = &blaster.vars[name];
            let mut value = 0u128;
            for (i, lit) in word.iter().enumerate() {
                let cnf_lit = k::cnf_lit(*lit);
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
            Some(env)
        } else {
            debug_assert!(false, "SAT model failed self-check — ordeal bug");
            None
        }
    }

    /// Decide satisfiability and, on `Sat`, return an INDEPENDENTLY
    /// re-checkable witness (TR-038 / #133, design:
    /// docs/design/sat-witness.md): the full CNF assignment plus the
    /// input-bit map, validated through the trusted `ordeal-lrat`
    /// `check_sat`/`check_binding` BEFORE `Sat` is returned — symmetric
    /// with the Unsat gate ("a Sat whose witness the trusted crate did
    /// not accept is never reported"; it degrades to `Unknown`).
    ///
    /// Always available (no feature gate since #162 / TR-045: the CLI emits
    /// the witness on every `sat`). Since TR-070 this is [`Solver::check`]'s
    /// own pipeline — the witness is built and checked on every path — so
    /// this entry costs nothing beyond `check` and returns the same
    /// certificate or model.
    pub fn check_with_witness(&self) -> crate::witness::WitnessCheckResult {
        use crate::witness::WitnessCheckResult;
        match self.solve_core(Bound::None) {
            Outcome::Unsat(cert, _) => WitnessCheckResult::Unsat(cert.query.certificate),
            Outcome::Sat(cert, _) => WitnessCheckResult::Sat(cert.query.witness),
            Outcome::Unknown => WitnessCheckResult::Unknown,
        }
    }

    /// Decide and, on `Unsat`, return the certificate TOGETHER WITH THE
    /// QUERY it refutes (issue #192 phase 4, `ordeal-cert/v2`): a
    /// [`crate::query::QueryCertificate`] carrying the lowered term DAG,
    /// its constant table, the asserted roots and the compaction hints
    /// next to the CNF + LRAT pair. Its `recheck()` re-encodes the DAG
    /// inside the trusted crate (`ordeal_lrat::check_query`) and checks the
    /// proof against the CNF *it* produced, so a consumer certifies the
    /// query and not a CNF it has to take on faith
    /// (`kernel.spec.check_query_sound`). Symmetric with the witness gate:
    /// the trusted query re-check runs BEFORE `Unsat` is returned, and a
    /// certificate it would reject degrades to `Unknown`. `Sat` is the
    /// usual re-checkable witness.
    ///
    /// Since TR-070 (v0.32.0) this is [`Solver::check`]'s own pipeline: the
    /// trusted query re-check (and the term check on top of it) runs on
    /// every path, so this entry costs nothing beyond `check` and returns
    /// the same certificate; only the query block is kept here. The
    /// formerly derived ops (`bvnot`, `bvneg`, `bvrotl`, `bvsdiv`,
    /// `bvsrem`) are lowered as their own DAG nodes through the proven
    /// composite rules ([`DerivedOps::Nodes`]) on every path since #192
    /// phase 5, so the query block carries the operation.
    ///
    /// Since #192 phase 6 (TR-065) `Sat` is symmetric: it carries a
    /// [`crate::query::QuerySatCertificate`] — the v1 witness plus the
    /// lowered query and the DAG's input assignment derived from the model
    /// — and the trusted `ordeal_lrat::check_query_model` must have
    /// evaluated EVERY root of that DAG to true under the assignment
    /// (`kernel.spec.check_query_model_sound`, the same `dagBool` semantics
    /// `check_query_sound` negates) before `Sat` is returned. The
    /// untrusted `eval.rs` self-check and the CNF-level witness re-check
    /// still run first (defence in depth); the answer rests on the trusted
    /// evaluation. A model it rejects degrades to `Unknown`.
    pub fn check_with_query(&self) -> crate::query::QueryCheckResult {
        use crate::query::QueryCheckResult;
        match self.solve_core(Bound::None) {
            Outcome::Unsat(cert, _) => QueryCheckResult::Unsat(cert.query),
            Outcome::Sat(cert, _) => QueryCheckResult::Sat(cert.query),
            Outcome::Unknown => QueryCheckResult::Unknown,
        }
    }

    /// Decide and return, with the certificate and the lowered query, the
    /// TERM the query was lowered from (issue #192 phase 7,
    /// `ordeal-cert/v3`): the assertions flattened as they were asked
    /// (`dag::flatten`, no canonicalization, no hash-consing) and the
    /// untrusted map from their nodes to the DAG's (`dag::term_map`). The
    /// trusted `ordeal_lrat::check_term_dag` verifies — BEFORE a verdict is
    /// returned, symmetric with the two gates of [`Solver::check_with_query`]
    /// — that the DAG is a semantics-preserving rewrite of the term along
    /// the map, so that the proof (`check_term_unsat_sound`) or the model
    /// (`check_term_model_sound`, plus the proven binding of every model
    /// value through the term's own variable map) is about the question
    /// asked and not about the DAG the solver built. Anything the trusted
    /// crate rejects degrades to `Unknown`.
    ///
    /// Since TR-070 (v0.32.0) this is [`Solver::check`]'s own pipeline
    /// ([`Solver::solve_core`]), returned whole: every entry point runs the
    /// same term gate, and this one keeps the term, the query and the
    /// certificate or witness it checked. It costs nothing beyond `check`.
    pub fn check_with_term(&self) -> crate::query::TermCheckResult {
        Self::term_outcome(self.solve_core(Bound::None))
    }

    /// The UNSAT gate of [`Solver::check_with_term`]: `Unsat` only if the
    /// trusted crate accepts the term-to-DAG correspondence (and the v2
    /// recheck); a rejection degrades to `Unknown`. Separate so the
    /// degradation is testable with a tampered certificate (the caller's
    /// `debug_assert` is what flags an ordeal bug in the real pipeline).
    #[cfg(test)]
    pub(crate) fn term_verdict(
        cert: crate::query::TermCertificate,
    ) -> crate::query::TermCheckResult {
        use crate::query::TermCheckResult;
        match cert.recheck() {
            Ok(()) => TermCheckResult::Unsat(cert),
            Err(_) => TermCheckResult::Unknown,
        }
    }

    /// The SAT gate of [`Solver::check_with_term`]: `Sat` only if the
    /// trusted crate accepts the correspondence, the model and every
    /// binding; a rejection degrades to `Unknown`.
    #[cfg(test)]
    pub(crate) fn term_sat_verdict(
        cert: crate::query::TermSatCertificate,
    ) -> crate::query::TermCheckResult {
        use crate::query::TermCheckResult;
        match cert.recheck() {
            Ok(()) => TermCheckResult::Sat(cert),
            Err(_) => TermCheckResult::Unknown,
        }
    }

    /// The query-level SAT gate of #192 phase 6, kept for its negative
    /// controls: `Sat` only if the trusted crate accepts the certificate's
    /// input assignment as a model of the query; anything it rejects — a
    /// wrong model, a malformed query, an assignment the model disagrees
    /// with — degrades to `Unknown`. Since TR-070 the production gate is
    /// [`Solver::term_sat_verdict`], whose re-check runs this one inside.
    #[cfg(test)]
    pub(crate) fn sat_verdict(
        cert: crate::query::QuerySatCertificate,
    ) -> crate::query::QueryCheckResult {
        use crate::query::QueryCheckResult;
        match cert.recheck() {
            Ok(()) => QueryCheckResult::Sat(cert),
            Err(_) => QueryCheckResult::Unknown,
        }
    }

    /// Decide with the optional CaDiCaL accelerator (TR-004's "benchmark
    /// yardstick" role) — identical pipeline and identical trusted gate
    /// ([`Solver::gate_unsat`] / [`Solver::gate_sat`]), only the SAT engine
    /// differs: `sat_cadical::solve` returns Unsat solely with an LRAT proof
    /// the verified checker already accepted (the gate then checks it once
    /// more, against the re-encoded query, as on every path).
    ///
    /// Hidden from docs on purpose: the production entry point is `check` on
    /// the pure-Rust core (TR-004 — CaDiCaL is never load-bearing). This
    /// exists for the benchmark lanes and parity tests.
    #[doc(hidden)]
    #[cfg(all(feature = "cadical", not(target_family = "wasm")))]
    pub fn check_with_cadical(&self) -> CheckResult {
        Self::verdict(self.solve_core_cadical())
    }

    #[cfg(all(feature = "cadical", not(target_family = "wasm")))]
    fn solve_core_cadical(&self) -> Outcome {
        use crate::sat_cadical::{self, CadicalVerdict};
        if self.assertions.is_empty() {
            return self.solve_core(Bound::None);
        }
        let Some((mut blaster, cnf)) = self.lower() else {
            return Outcome::Unknown;
        };
        let Some(query) = blaster.query.take() else {
            return Outcome::Unknown;
        };
        let vars = std::mem::take(&mut blaster.query_vars);
        match sat_cadical::solve(&cnf) {
            Ok(CadicalVerdict::Unsat { lrat }) => self.gate_unsat(
                query,
                &vars,
                Certificate {
                    lrat: lrat.into_bytes(),
                    cnf: cnf.clauses,
                },
            ),
            Ok(CadicalVerdict::Sat(assignment)) => {
                self.gate_sat(query, &vars, &blaster, cnf.clauses, assignment)
            }
            // Every CaDiCaL error is conservative no-verdict.
            Err(_) => Outcome::Unknown,
        }
    }
}

/// How a solve is bounded (crate-internal): unbounded, a conflict budget
/// (DES-019), or a wall-clock deadline (TR-029). Exhaustion of either bound
/// surfaces uniformly as a conservative `Unknown`.
enum Bound {
    None,
    Conflicts(u64),
    Deadline(std::time::Instant),
}

/// The gated outcome of one solve (crate-internal): the term certificate
/// every entry point projects its verdict from, and — for a solver built
/// from the sliver (TR-072) — the extended certificate whose trusted
/// re-check (`check_sliver_lowering` first) also passed.
enum Outcome {
    Unsat(
        crate::query::TermCertificate,
        Option<Box<crate::query::SliverCertificate>>,
    ),
    Sat(
        crate::query::TermSatCertificate,
        Option<Box<crate::query::SliverSatCertificate>>,
    ),
    Unknown,
}

/// The test-only tamper hook of the trusted gate (TR-070's negative
/// control): a unit test arms a [`tamper::Tamper`] for its thread, calls
/// the REAL entry point (`check`, `check_with_limit`, …), and the gate
/// hands the trusted crate a corrupted term map or variable map. The
/// verdict must then be `Unknown` — which shows that the answer rests on
/// the trusted rejection, not on the solver's say-so. Compiled out of every
/// non-test build: [`tamper::apply`] is the identity there.
#[cfg(test)]
pub(crate) mod tamper {
    use crate::query::QueryTerm;
    use std::cell::Cell;

    /// What to corrupt before the trusted check sees it.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub(crate) enum Tamper {
        /// Point the first mapped operator node of the term at a different
        /// DAG node: `check_term_dag` must reject (on SAT and on UNSAT).
        MapEntry,
        /// Swap the `Var` nodes of the term's first two variables: on SAT
        /// the proven binding (`var_offset` / `check_input_value`) must
        /// reject a model whose two values differ; UNSAT does not read the
        /// variable map and must be unaffected.
        SwapVars,
        /// TR-072: point the first mapped `select` or call of the
        /// extended query at a different core node (a tampered ext
        /// block): `check_sliver_lowering` must reject.
        ExtMap,
        /// TR-072: make the first two read entries share one read variable
        /// (a wrong read share): the table check must reject.
        ReadShare,
        /// TR-072: register the first query variable as the first read
        /// entry's variable (the #247 capture shape): the class partition
        /// must reject. (The fourth sliver control, a lowering that omits
        /// a congruence clause, is `sliver::hooks::drop_last_congruence`:
        /// it must live in the lowering so the core, the DAG and the CNF
        /// stay consistent with each other and only the sliver check can
        /// catch it.)
        CaptureName,
    }

    thread_local! {
        static ACTIVE: Cell<Option<Tamper>> = const { Cell::new(None) };
    }

    /// Arm (or, with `None`, disarm) the hook for the calling thread; the
    /// returned guard disarms it on drop, panic included.
    pub(crate) fn arm(t: Tamper) -> Armed {
        ACTIVE.with(|c| c.set(Some(t)));
        Armed
    }

    /// Disarms the hook when dropped.
    pub(crate) struct Armed;

    impl Drop for Armed {
        fn drop(&mut self) {
            ACTIVE.with(|c| c.set(None));
        }
    }

    /// Apply the armed tamper, if any; the flag says whether one was.
    pub(crate) fn apply(mut term: QueryTerm) -> (QueryTerm, bool) {
        use crate::blast_kernel::DagNode;
        match ACTIVE.with(|c| c.get()) {
            None => (term, false),
            Some(Tamper::MapEntry) => {
                let target = term.nodes.iter().enumerate().position(|(i, n)| {
                    !matches!(n, DagNode::Var(_) | DagNode::Const(_, _))
                        && term.map[i] != crate::dag::NO_IMAGE
                });
                let i = target.expect("a term with a mapped operator node");
                term.map[i] = if term.map[i] == 0 { 1 } else { 0 };
                (term, true)
            }
            Some(Tamper::SwapVars) => {
                assert!(term.vars.len() >= 2, "a term with two variables");
                let (n0, n1) = (term.vars[0].2, term.vars[1].2);
                term.vars[0].2 = n1;
                term.vars[1].2 = n0;
                (term, true)
            }
            // The sliver tampers leave the term alone; `apply_sliver` acts.
            Some(Tamper::ExtMap | Tamper::ReadShare | Tamper::CaptureName) => (term, false),
        }
    }

    /// Is the lowering itself tampered (`sliver::hooks::drop_last_congruence`)?
    /// Then the gate's rejection is the expected one.
    pub(crate) fn lowering_tampered() -> bool {
        crate::sliver::hooks::dropping_last_congruence()
    }

    /// Apply the armed sliver tamper, if any, to the `ext` block; the flag
    /// says whether one was.
    pub(crate) fn apply_sliver(
        mut block: crate::query::SliverBlock,
    ) -> (crate::query::SliverBlock, bool) {
        use ordeal_lrat::ExtNode;
        match ACTIVE.with(|c| c.get()) {
            Some(Tamper::ExtMap) => {
                let i = block
                    .ext
                    .nodes
                    .iter()
                    .position(|n| matches!(n, ExtNode::Select(..) | ExtNode::Call(..)))
                    .expect("an extended query with a select or a call");
                block.map[i] = if block.map[i] == 0 { 1 } else { 0 };
                (block, true)
            }
            Some(Tamper::ReadShare) => {
                assert!(block.reads.len() >= 6, "an extended query with two reads");
                block.reads[3] = block.reads[0];
                (block, true)
            }
            Some(Tamper::CaptureName) => {
                assert!(block.reads.len() >= 3, "an extended query with a read");
                let (_, _, node) = block
                    .ext
                    .vars
                    .first()
                    .expect("an extended query with a variable");
                let image = block.map[*node];
                block.reads[0] = image;
                (block, true)
            }
            _ => (block, false),
        }
    }
}

/// The non-test twin of [`tamper::apply`]: the identity, so the gate's
/// code is the same in every build and the hook costs nothing.
#[cfg(not(test))]
mod tamper {
    #[inline]
    pub(crate) fn apply(term: crate::query::QueryTerm) -> (crate::query::QueryTerm, bool) {
        (term, false)
    }
    #[inline]
    pub(crate) fn apply_sliver(
        block: crate::query::SliverBlock,
    ) -> (crate::query::SliverBlock, bool) {
        (block, false)
    }
    #[inline]
    pub(crate) fn lowering_tampered() -> bool {
        false
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

/// Walk every `Var` under a boolean term, demanding one width per name
/// across the whole assertion set (see [`Solver::validate`]). A conflict
/// reports the two widths as a [`EvalError::WidthMismatch`].
fn check_var_widths_bool<'t>(
    term: &'t BoolTerm,
    widths: &mut std::collections::HashMap<&'t str, u32>,
) -> Result<(), EvalError> {
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
        | BoolTerm::Sge(a, b) => {
            check_var_widths_bv(a, widths)?;
            check_var_widths_bv(b, widths)
        }
        BoolTerm::Not(t) => check_var_widths_bool(t, widths),
        BoolTerm::And(a, b) | BoolTerm::Or(a, b) => {
            check_var_widths_bool(a, widths)?;
            check_var_widths_bool(b, widths)
        }
    }
}

/// [`check_var_widths_bool`]'s bitvector leg.
fn check_var_widths_bv<'t>(
    term: &'t BvTerm,
    widths: &mut std::collections::HashMap<&'t str, u32>,
) -> Result<(), EvalError> {
    match term {
        BvTerm::Const { .. } => Ok(()),
        BvTerm::Var { name, sort } => match widths.get(name.as_str()) {
            None => {
                widths.insert(name.as_str(), sort.width);
                Ok(())
            }
            Some(&w) if w == sort.width => Ok(()),
            Some(&w) => Err(EvalError::WidthMismatch {
                left: w,
                right: sort.width,
            }),
        },
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
        | BvTerm::Rotl(a, b)
        | BvTerm::Sdiv(a, b)
        | BvTerm::Srem(a, b)
        | BvTerm::Concat(a, b) => {
            check_var_widths_bv(a, widths)?;
            check_var_widths_bv(b, widths)
        }
        BvTerm::Extract { arg, .. }
        | BvTerm::ZeroExt { arg, .. }
        | BvTerm::SignExt { arg, .. }
        | BvTerm::Not(arg)
        | BvTerm::Neg(arg) => check_var_widths_bv(arg, widths),
        BvTerm::Ite { cond, then_, else_ } => {
            check_var_widths_bool(cond, widths)?;
            check_var_widths_bv(then_, widths)?;
            check_var_widths_bv(else_, widths)
        }
    }
}

/// The `check_cnf` SAT gate (issue #184): `Sat` only if the trusted kernel's
/// `ordeal_lrat::check_sat` accepts `assignment` against `formula`, otherwise
/// the conservative `Unknown`. A runtime check in every build profile.
fn cnf_sat_verdict(formula: &crate::cnf::CnfFormula, assignment: &[bool]) -> CheckResult {
    if ordeal_lrat::check_sat(&formula.clauses, assignment).is_err() {
        return CheckResult::Unknown;
    }
    let assignments = assignment
        .iter()
        .enumerate()
        .map(|(i, &b)| (format!("v{}", i + 1), b as u128))
        .collect();
    CheckResult::Sat(Model { assignments })
}

/// Issue #192 phase 1 — the CNF-gap measurement: CNF size and blast +
/// Tseitin time of the SHIPPED pipeline with AIG simplification switched
/// off, folding only, and folding + hashing (production). A test-only
/// harness, `#[ignore]`d: it prints markdown tables (recorded in
/// docs/design/query-cnf-gap.md) rather than asserting anything beyond
/// the three configurations agreeing on the verdict's inputs.
///
///   cargo test -p ordeal --release --lib cnf_gap_measurement -- --ignored --nocapture
///   LIBRARY_PATH=/opt/homebrew/lib cargo test -p ordeal --release --lib \
///       --features oracle cnf_gap_measurement -- --ignored --nocapture
#[cfg(test)]
mod cnf_gap_measurement {
    use super::*;
    use crate::term::Sort;
    use std::time::{Duration, Instant};

    fn v(n: &str, w: u32) -> BvTerm {
        BvTerm::Var {
            name: n.into(),
            sort: Sort::new(w),
        }
    }
    fn c(val: u128, w: u32) -> BvTerm {
        BvTerm::Const {
            value: val,
            sort: Sort::new(w),
        }
    }

    /// The `benches/latency.rs` corpus (copied: a bench's `corpus()` is not
    /// a library item, and the bench must stay untouched).
    fn latency_corpus() -> Vec<(String, Vec<BoolTerm>)> {
        use crate::lowering;
        let mut out = Vec::new();
        {
            let (a, b) = (v("a", 32), v("b", 32));
            let ours = lowering::bvsrem(a.clone(), b.clone(), 32);
            let q = lowering::bvsdiv(a.clone(), b.clone(), 32);
            let theirs = BvTerm::Sub(Box::new(a), Box::new(BvTerm::Mul(Box::new(q), Box::new(b))));
            out.push((
                "srem_vc_32".to_string(),
                vec![BoolTerm::Ne(Box::new(ours), Box::new(theirs))],
            ));
        }
        {
            let (a, b) = (v("a", 32), v("b", 32));
            let ours = BvTerm::Urem(Box::new(a.clone()), Box::new(b.clone()));
            let q = BvTerm::Udiv(Box::new(a.clone()), Box::new(b.clone()));
            let theirs = BvTerm::Sub(Box::new(a), Box::new(BvTerm::Mul(Box::new(q), Box::new(b))));
            out.push((
                "urem_vc_32".to_string(),
                vec![BoolTerm::Ne(Box::new(ours), Box::new(theirs))],
            ));
        }
        {
            let x = v("x", 32);
            let bytes = crate::layout::to_le_bytes(&x, 32);
            let back = crate::layout::from_le_bytes(&bytes);
            out.push((
                "layout_roundtrip_32".to_string(),
                vec![BoolTerm::Ne(Box::new(back), Box::new(x))],
            ));
        }
        {
            use crate::trap::{DivOp, trap_div};
            let (a, b) = (v("a", 32), v("b", 32));
            let t1 = trap_div(DivOp::DivU, &a, &b, 32);
            let t2 = trap_div(DivOp::DivU, &a, &b, 32);
            let iff = BoolTerm::And(
                Box::new(BoolTerm::Or(
                    Box::new(BoolTerm::Not(Box::new(t1.clone()))),
                    Box::new(t2.clone()),
                )),
                Box::new(BoolTerm::Or(
                    Box::new(BoolTerm::Not(Box::new(t2))),
                    Box::new(t1),
                )),
            );
            out.push(("trap_vc_32".to_string(), vec![BoolTerm::Not(Box::new(iff))]));
        }
        {
            let (a, b, cc) = (v("a", 64), v("b", 64), v("c", 64));
            out.push((
                "ult_cycle_64".to_string(),
                vec![
                    BoolTerm::Ult(Box::new(a.clone()), Box::new(b.clone())),
                    BoolTerm::Ult(Box::new(b), Box::new(cc.clone())),
                    BoolTerm::Ult(Box::new(cc), Box::new(a)),
                ],
            ));
        }
        {
            let x = v("x", 64);
            let shl = BvTerm::Shl(Box::new(x.clone()), Box::new(c(1, 64)));
            let add = BvTerm::Add(Box::new(x.clone()), Box::new(x));
            out.push((
                "shl1_eq_add_64".to_string(),
                vec![BoolTerm::Ne(Box::new(shl), Box::new(add))],
            ));
        }
        out
    }

    /// One measurement: AIG ANDs, CNF vars, CNF clauses, and the median
    /// wall time of `lower_with` (canon + blast + Tseitin) over `runs`.
    struct Sample {
        ands: u64,
        vars: u64,
        clauses: u64,
        median: Duration,
    }

    fn measure(q: &[BoolTerm], opts: AigOptions, runs: usize) -> Sample {
        let mut s = Solver::new();
        for a in q {
            s.assert(a.clone());
        }
        let mut times = Vec::with_capacity(runs);
        let mut sample = None;
        for _ in 0..runs {
            let t0 = Instant::now();
            let lowered = s
                .lower_with(opts, DerivedOps::Nodes)
                .expect("corpus query must lower");
            times.push(t0.elapsed());
            sample = Some(Sample {
                ands: lowered.0.num_ands() as u64,
                vars: u64::from(lowered.1.num_vars),
                clauses: lowered.1.clauses.len() as u64,
                median: Duration::ZERO,
            });
        }
        times.sort();
        let mut sample = sample.expect("at least one run");
        sample.median = times[runs / 2];
        sample
    }

    const CONFIGS: [(&str, AigOptions); 3] = [
        ("raw", AigOptions::RAW),
        ("fold", AigOptions::FOLD_ONLY),
        (
            "fold+hash",
            AigOptions {
                fold: true,
                strash: true,
            },
        ),
    ];

    fn fmt_us(d: Duration) -> String {
        format!("{:.1}", d.as_secs_f64() * 1e6)
    }

    /// Per-query table over a named corpus.
    fn table(title: &str, corpus: &[(String, Vec<BoolTerm>)], runs: usize) {
        println!("\n### {title}\n");
        println!(
            "| query | config | AIG ANDs | CNF vars | CNF clauses | blast+Tseitin median (µs) |"
        );
        println!("|---|---|---:|---:|---:|---:|");
        for (name, q) in corpus {
            for (cname, opts) in CONFIGS {
                let s = measure(q, opts, runs);
                println!(
                    "| {name} | {cname} | {} | {} | {} | {} |",
                    s.ands,
                    s.vars,
                    s.clauses,
                    fmt_us(s.median)
                );
            }
        }
    }

    /// Aggregate table over a corpus of unnamed queries: totals and the
    /// per-query medians.
    #[cfg(feature = "oracle")]
    fn aggregate_table(title: &str, corpus: &[Vec<BoolTerm>], runs: usize) {
        println!("\n### {title} ({} queries)\n", corpus.len());
        println!(
            "| config | total AIG ANDs | total CNF vars | total CNF clauses | median ANDs/query | median clauses/query | total blast+Tseitin (ms, sum of medians) | median per query (µs) |"
        );
        println!("|---|---:|---:|---:|---:|---:|---:|---:|");
        for (cname, opts) in CONFIGS {
            let samples: Vec<Sample> = corpus.iter().map(|q| measure(q, opts, runs)).collect();
            let total = |f: &dyn Fn(&Sample) -> u64| samples.iter().map(f).sum::<u64>();
            let median_of = |mut xs: Vec<u64>| {
                xs.sort();
                xs[xs.len() / 2]
            };
            let sum_t: Duration = samples.iter().map(|s| s.median).sum();
            let med_t = {
                let mut ts: Vec<Duration> = samples.iter().map(|s| s.median).collect();
                ts.sort();
                ts[ts.len() / 2]
            };
            println!(
                "| {cname} | {} | {} | {} | {} | {} | {:.2} | {} |",
                total(&|s| s.ands),
                total(&|s| s.vars),
                total(&|s| s.clauses),
                median_of(samples.iter().map(|s| s.ands).collect()),
                median_of(samples.iter().map(|s| s.clauses).collect()),
                sum_t.as_secs_f64() * 1e3,
                fmt_us(med_t)
            );
        }
    }

    /// SHA-256 over the production CNF (`num_vars`, then every clause, every
    /// literal as little-endian `i32`, clause-terminated by a zero) of every
    /// query in a corpus, in corpus order — one line per corpus.
    fn digest(title: &str, corpus: &[Vec<BoolTerm>]) {
        digest_with(title, corpus, DerivedOps::Nodes);
    }

    /// `digest` under an explicit derived-op setting (#192 phase 5): the
    /// `Nodes` line quantifies how the query-carrying path's CNF differs
    /// from the default path's over a corpus.
    fn digest_with(title: &str, corpus: &[Vec<BoolTerm>], derived: DerivedOps) {
        let mut bytes: Vec<u8> = Vec::new();
        let mut clauses = 0u64;
        for q in corpus {
            let mut s = Solver::new();
            for a in q {
                s.assert(a.clone());
            }
            let (_, cnf) = s
                .lower_with(AigOptions::default(), derived)
                .expect("corpus query must lower");
            bytes.extend_from_slice(&cnf.num_vars.to_le_bytes());
            for c in &cnf.clauses {
                for &l in c {
                    bytes.extend_from_slice(&l.to_le_bytes());
                }
                bytes.extend_from_slice(&0i32.to_le_bytes());
                clauses += 1;
            }
        }
        println!(
            "| {title} | {} | {clauses} | {} |",
            corpus.len(),
            crate::sha256::sha256_hex(&bytes)
        );
    }

    /// Issue #192 phase 2: the production CNF of every corpus query, as one
    /// digest per corpus. Run on the base commit and on the branch; equal
    /// digests mean the shipped CNF is byte-identical over the whole corpus
    /// (the `cli_baseline` fixtures are a handful of queries; this is ~1200).
    #[test]
    #[ignore = "measurement, not a check: prints the #192 phase-2 CNF digests"]
    fn cnf_gap_digest() {
        println!("\n| corpus | queries | clauses | sha256 of every production CNF |");
        println!("|---|---:|---:|---|");
        let latency: Vec<Vec<BoolTerm>> = latency_corpus().into_iter().map(|(_, q)| q).collect();
        digest("benches/latency.rs corpus", &latency);
        // #192 phase 5: the same corpus with the derived ops as nodes (the
        // `check_with_query` path) — `srem_vc_32` is the one query here
        // with `bvsdiv` / `bvsrem`.
        digest_with(
            "benches/latency.rs corpus (derived ops as nodes)",
            &latency,
            DerivedOps::Nodes,
        );
        let bmc: Vec<Vec<BoolTerm>> = [16usize, 32, 64]
            .iter()
            .map(|&k| crate::bmc_corpus::queue_overflow(k, k as u8))
            .chain(
                [24usize, 48]
                    .iter()
                    .map(|&k| crate::bmc_corpus::deadlock(k, false)),
            )
            .collect();
        digest("benches/bmc.rs corpus", &bmc);
        #[cfg(feature = "oracle")]
        {
            digest(
                "oracle::gen_corpus(0x192, 200)",
                &crate::oracle::gen_corpus(0x192, 200),
            );
            digest(
                "oracle::gen_corpus(0xC0FFEE, 1000)",
                &crate::oracle::gen_corpus(0xC0FFEE, 1000),
            );
        }
    }

    #[test]
    #[ignore = "measurement, not a check: prints the #192 CNF-gap tables (release build)"]
    fn cnf_gap_measurement() {
        let runs = 7;
        println!(
            "\nconfigurations: raw = no folding, no hashing; fold = constant folding only; \
             fold+hash = production (constant folding + structural hashing)"
        );
        table("benches/latency.rs corpus", &latency_corpus(), runs);
        let bmc: Vec<(String, Vec<BoolTerm>)> = [16usize, 32, 64]
            .iter()
            .map(|&k| {
                (
                    format!("queue_overflow_k{k}"),
                    crate::bmc_corpus::queue_overflow(k, k as u8),
                )
            })
            .chain([24usize, 48].iter().map(|&k| {
                (
                    format!("deadlock_k{k}"),
                    crate::bmc_corpus::deadlock(k, false),
                )
            }))
            .collect();
        table("benches/bmc.rs corpus", &bmc, runs);
        #[cfg(feature = "oracle")]
        {
            let corpus = crate::oracle::gen_corpus(0x192, 200);
            aggregate_table(
                "oracle::gen_corpus(0x192, 200) — the Z3 differential corpus",
                &corpus,
                runs,
            );
        }
        #[cfg(not(feature = "oracle"))]
        println!("\n(oracle corpus skipped: build with --features oracle)");
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

    /// The production CNF of `assertions` under a derived-op setting.
    fn cnf_under(assertions: &[BoolTerm], derived: DerivedOps) -> CnfFormula {
        let mut s = Solver::new();
        for a in assertions {
            s.assert(a.clone());
        }
        s.lower_with(AigOptions::default(), derived)
            .expect("lowers")
            .1
    }

    // rivet: verifies VER-064
    /// #192 phase 5: with the operand variables created before the derived
    /// op and a non-commutative parent, the query-carrying path (derived
    /// ops as nodes, proven composite rules) produces the SAME production
    /// CNF as the default path (the v0.27.0 rewrite) — for every derived
    /// op, a constant and a variable rotate amount, at power-of-two and
    /// other widths. This is the gate-identity claim of the design (the
    /// composite rule IS the rewrite's gates); the two ways the paths CAN
    /// differ — canon reordering a commutative parent or operand by the
    /// nodes' `Debug` names (`Not(` sorts before `Var`, its rewrite `Xor(`
    /// after), and a variable first created inside the second operand —
    /// are the parent's and the builder's, not the rule's;
    /// `derived_nodes_can_renumber_the_cnf` pins one of them.
    #[test]
    fn derived_nodes_lower_to_the_rewrite_cnf_when_operands_come_first() {
        for &w in &[5u32, 8, 12, 32] {
            let (a, bb, r) = (var("a", w), var("b", w), var("r", w));
            let ops: Vec<(&str, BvTerm)> = vec![
                ("bvnot", BvTerm::Not(b(a.clone()))),
                ("bvneg", BvTerm::Neg(b(a.clone()))),
                ("bvrotl const", BvTerm::Rotl(b(a.clone()), b(c(3, w)))),
                ("bvrotl var", BvTerm::Rotl(b(a.clone()), b(bb.clone()))),
                ("bvsdiv", BvTerm::Sdiv(b(a.clone()), b(bb.clone()))),
                ("bvsrem", BvTerm::Srem(b(a.clone()), b(bb.clone()))),
            ];
            for (name, t) in ops {
                let q = vec![
                    BoolTerm::Ult(b(a.clone()), b(bb.clone())),
                    BoolTerm::Ult(b(t), b(r.clone())),
                ];
                let rewrite = cnf_under(&q, DerivedOps::Rewrite);
                let nodes = cnf_under(&q, DerivedOps::Nodes);
                assert_eq!(rewrite.num_vars, nodes.num_vars, "{name} w{w}: num_vars");
                assert_eq!(rewrite.clauses, nodes.clauses, "{name} w{w}: clauses");
            }
        }
    }

    // rivet: verifies VER-064
    /// The documented difference (#192 phase 5, the reason the default path
    /// keeps the rewrite): when a variable's FIRST occurrence is inside a
    /// derived op's second operand, the rewrite creates its primary inputs
    /// in the middle of the rewritten tree while the node creates them
    /// before its gates, so the arena — and the CNF's variable numbering —
    /// differ (same clause count, same verdict, both certified; this is the
    /// `srem_vc_32` digest difference in docs/design/query-cnf-gap.md).
    #[test]
    fn derived_nodes_can_renumber_the_cnf() {
        let (a, bb) = (var("a", 32), var("b", 32));
        let ours = BvTerm::Srem(b(a.clone()), b(bb.clone()));
        let q = BvTerm::Sdiv(b(a.clone()), b(bb.clone()));
        let theirs = BvTerm::Sub(b(a), b(BvTerm::Mul(b(q), b(bb))));
        let query = vec![BoolTerm::Ne(b(ours), b(theirs))];
        let rewrite = cnf_under(&query, DerivedOps::Rewrite);
        let nodes = cnf_under(&query, DerivedOps::Nodes);
        assert_eq!(rewrite.num_vars, nodes.num_vars, "same arena size");
        assert_eq!(
            rewrite.clauses.len(),
            nodes.clauses.len(),
            "same clause count"
        );
        assert_ne!(
            rewrite.clauses, nodes.clauses,
            "the two paths number the variables differently here; if this \
             stops holding, the default path can switch to DerivedOps::Nodes \
             without changing emitted certificates — update the design doc"
        );
    }

    /// fuzz-found (#139): two `Var`s sharing a name at different widths are
    /// each locally well-sorted but bind by name in the blaster — this used
    /// to panic in blast_udivrem. validate must reject it and check must
    /// stay conservative (`Unknown`), per the VER-005 contract.
    #[test]
    fn inconsistent_var_widths_are_unknown() {
        let mut s = Solver::new();
        s.assert(BoolTerm::Eq(b(var("a", 32)), b(c(0, 32))));
        s.assert(BoolTerm::Eq(
            b(BvTerm::Udiv(b(var("a", 8)), b(c(1, 8)))),
            b(c(0, 8)),
        ));
        assert!(
            s.validate().is_err(),
            "cross-assertion width conflict must fail validate"
        );
        assert!(matches!(s.check(), CheckResult::Unknown));
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
    // rivet: verifies VER-050
    /// Issue #184: the `check_cnf` SAT gate is a runtime check, not a
    /// `debug_assert`. A model that violates a clause must degrade to
    /// `Unknown` in every build profile (CI runs this under `--release`).
    #[test]
    fn check_cnf_sat_gate_rejects_a_wrong_model_in_every_profile() {
        let f = crate::cnf::CnfFormula {
            num_vars: 2,
            clauses: vec![vec![1, 2], vec![-1]],
        };
        // v1 = true violates the unit clause (-1).
        assert!(matches!(
            cnf_sat_verdict(&f, &[true, true]),
            CheckResult::Unknown
        ));
        // A model that does not bind every variable is rejected too.
        assert!(matches!(
            cnf_sat_verdict(&f, &[false]),
            CheckResult::Unknown
        ));
        // The real model is accepted with its bindings.
        match cnf_sat_verdict(&f, &[false, true]) {
            CheckResult::Sat(m) => assert_eq!(
                m.assignments,
                vec![("v1".to_string(), 0), ("v2".to_string(), 1)]
            ),
            other => panic!("expected Sat, got {other:?}"),
        }
    }

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

    // ── #236: the refusal is visible, and the sliver entry can be bounded ──

    /// A bad array sort is the one refusal left (a symbolic index is in the
    /// sliver since TR-028): `from_sliver` reports it as an `Err`, where the
    /// one-shot entries can only say `Unknown`.
    fn bad_sort_query() -> crate::sliver::ExtBoolTerm {
        use crate::sliver::{ArrayTerm, ExtBoolTerm, ExtBvTerm};
        let bv8 = Sort::new(8);
        ExtBoolTerm::Eq(
            ExtBvTerm::Select {
                array: Box::new(ArrayTerm::Var { name: "a".into() }),
                index: Box::new(ExtBvTerm::Core(BvTerm::Var {
                    name: "i".into(),
                    sort: bv8,
                })),
            },
            ExtBvTerm::Core(BvTerm::Const {
                value: 0,
                sort: bv8,
            }),
        )
    }

    // rivet: verifies VER-067
    #[test]
    fn from_sliver_reports_the_refusal_not_unknown() {
        let q = [bad_sort_query()];
        assert_eq!(
            Solver::from_sliver(&q).err(),
            Some(crate::sliver::SliverError::BadArraySort)
        );
        assert!(matches!(
            Solver::check_sliver_with_deadline(&q, 60_000),
            CheckResult::Unknown
        ));
        assert!(matches!(
            Solver::check_sliver_with_limit(&q, 1_000_000),
            CheckResult::Unknown
        ));
    }

    /// The lowered solver decides exactly as `check_sliver` does, and every
    /// core entry point works on it — including the trusted query recheck.
    // rivet: verifies VER-067
    #[test]
    fn from_sliver_solver_takes_every_core_entry_point() {
        use crate::sliver::ExtBoolTerm;
        let i = sym_bv32("i");
        let v = sym_bv8("v");
        let read = sel(st(base("mem"), i.clone(), v.clone()), i);
        let valid = [ExtBoolTerm::Ne(read.clone(), v.clone())];
        let free = [ExtBoolTerm::Ne(read, sym_bv8("w"))];
        let s = Solver::from_sliver(&valid).expect("in the sliver");
        assert!(matches!(s.check(), CheckResult::Unsat(_)));
        assert!(matches!(
            s.check_with_deadline(60_000),
            CheckResult::Unsat(_)
        ));
        assert!(matches!(
            s.check_with_limit(1_000_000),
            CheckResult::Unsat(_)
        ));
        assert!(matches!(
            s.check_with_query(),
            crate::query::QueryCheckResult::Unsat(_)
        ));
        assert!(matches!(
            Solver::check_sliver(&valid),
            CheckResult::Unsat(_)
        ));
        let s = Solver::from_sliver(&free).expect("in the sliver");
        assert!(matches!(s.check(), CheckResult::Sat(_)));
        assert!(matches!(Solver::check_sliver(&free), CheckResult::Sat(_)));
    }

    /// `x*(y+z) != x*y + x*z` over values read from memory at a symbolic
    /// base: UNSAT, and (like `hard_mul_equivalence`) not decided by
    /// canonicalization, so it needs real search. Each operand is
    /// `width/8` little-endian bytes read from `mem[addr + k]`.
    fn sliver_distributivity(width: u32) -> Vec<crate::sliver::ExtBoolTerm> {
        use crate::sliver::{ExtBoolTerm, ExtBvTerm, ExtOp};
        let op = |o: ExtOp| ExtBvTerm::Op(Box::new(o));
        let bytes = width / 8;
        let word = |slot: u32| {
            let at = |k: u32| {
                sel(
                    base("mem"),
                    op(ExtOp::Add(
                        sym_bv32("addr"),
                        ExtBvTerm::Core(BvTerm::Const {
                            value: (slot * bytes + k) as u128,
                            sort: Sort::new(32),
                        }),
                    )),
                )
            };
            (1..bytes).fold(at(0), |acc, k| op(ExtOp::Concat(at(k), acc)))
        };
        let (x, y, z) = (word(0), word(1), word(2));
        let lhs = op(ExtOp::Mul(x.clone(), op(ExtOp::Add(y.clone(), z.clone()))));
        let rhs = op(ExtOp::Add(
            op(ExtOp::Mul(x.clone(), y)),
            op(ExtOp::Mul(x, z)),
        ));
        vec![ExtBoolTerm::Ne(lhs, rhs)]
    }

    /// Exhausted bounds give `Unknown`, never a wrong verdict; generous bounds
    /// decide like the unbounded entry, with a checked certificate.
    // rivet: verifies VER-067
    #[test]
    fn bounded_sliver_entries_are_conservative() {
        let hard = sliver_distributivity(32);
        // A zero conflict budget cannot decide it: strictly Unknown, so this
        // test does exercise the exhaustion path.
        assert!(matches!(
            Solver::check_sliver_with_limit(&hard, 0),
            CheckResult::Unknown
        ));
        match Solver::check_sliver_with_deadline(&hard, 0) {
            CheckResult::Unknown => {}
            CheckResult::Unsat(cert) => cert.recheck().expect("decided-in-time cert must check"),
            CheckResult::Sat(m) => {
                panic!("an expired deadline must never yield a wrong Sat: {m:?}")
            }
        }
        // read-over-write at a symbolic index: decided quickly, so generous
        // bounds must return the same checked Unsat as the unbounded entry.
        let i = sym_bv32("i");
        let v = sym_bv8("v");
        let easy = [crate::sliver::ExtBoolTerm::Ne(
            sel(st(base("mem"), i.clone(), v.clone()), i),
            v,
        )];
        for v in [
            Solver::check_sliver_with_deadline(&easy, 600_000),
            Solver::check_sliver_with_limit(&easy, u64::MAX),
        ] {
            match v {
                CheckResult::Unsat(cert) => cert.recheck().expect("certificate must check"),
                other => panic!("a generous bound must decide: {other:?}"),
            }
        }
    }

    // ── #247: fresh names never capture a query variable ────────────────

    /// `select(a, 5) != $sel:a:5` is satisfiable (the cell and the variable
    /// are independent). Before #247 it was a certified `Unsat`.
    // rivet: verifies VER-071
    #[test]
    fn a_query_variable_named_like_a_fresh_read_is_not_captured() {
        use crate::sliver::{ExtBoolTerm, ExtBvTerm};
        let q = [ExtBoolTerm::Ne(
            sel(
                base("a"),
                crate::sliver::ExtBvTerm::Core(BvTerm::Const {
                    value: 5,
                    sort: Sort::new(32),
                }),
            ),
            sym_bv8("$sel:a:5"),
        )];
        assert!(
            matches!(Solver::check_sliver(&q), CheckResult::Sat(_)),
            "#247 regression"
        );
        let call = ExtBvTerm::PureCall {
            name: "f".into(),
            args: vec![sym_bv8("x")],
            sort: Sort::new(8),
        };
        let q = [ExtBoolTerm::Ne(call, sym_bv8("$uf:f:0"))];
        assert!(
            matches!(Solver::check_sliver(&q), CheckResult::Sat(_)),
            "#247 regression"
        );
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

    // ── #231: operators lifted over sliver children ──────────────────────
    //
    // loom's encoder models `select`/`if` and its trap guard as `ite`, so
    // these are the shapes slices 3-5 of loom #313 emit. Each `Unsat` is
    // certificate-checked by construction; each has a `Sat` twin so a
    // lowering that made everything unsat could not pass.

    fn xop(op: crate::sliver::ExtOp) -> crate::sliver::ExtBvTerm {
        crate::sliver::ExtBvTerm::Op(Box::new(op))
    }
    fn f8(arg: crate::sliver::ExtBvTerm) -> crate::sliver::ExtBvTerm {
        crate::sliver::ExtBvTerm::PureCall {
            name: "f".into(),
            args: vec![arg],
            sort: Sort::new(8),
        }
    }

    /// `ite(c, select(store(m, i, v), i), v) = v` for symbolic `c`, `i`, `v`:
    /// a conditional over an array read. The `= x` twin is satisfiable.
    // rivet: verifies VER-066
    #[test]
    fn ite_over_select_is_decided() {
        use crate::sliver::{ExtBoolTerm, ExtOp};
        let i = sym_bv32("i");
        let v = sym_bv8("v");
        let read = sel(st(base("mem"), i.clone(), v.clone()), i);
        let ite = |else_: crate::sliver::ExtBvTerm| {
            xop(ExtOp::Ite {
                cond: ExtBoolTerm::Ult(sym_bv8("p"), sym_bv8("q")),
                then_: read.clone(),
                else_,
            })
        };
        match Solver::prove_equiv_sliver(ite(v.clone()), v.clone()) {
            CheckResult::Unsat(_) => {}
            other => panic!("ite over a read-over-write hit must equal v; got {other:?}"),
        }
        match Solver::prove_equiv_sliver(ite(sym_bv8("x")), v) {
            CheckResult::Sat(_) => {}
            other => panic!("the else branch is free, so this must be sat; got {other:?}"),
        }
    }

    /// `ite(c, f(a), x)` with `a = b`: equals `ite(c, f(b), x)` by congruence
    /// even though the call sits under one branch of a conditional.
    // rivet: verifies VER-066
    #[test]
    fn ite_over_pure_call_keeps_congruence() {
        use crate::sliver::{ExtBoolTerm, ExtOp};
        let ite = |arg: &str| {
            xop(ExtOp::Ite {
                cond: ExtBoolTerm::Ult(sym_bv8("p"), sym_bv8("q")),
                then_: f8(sym_bv8(arg)),
                else_: sym_bv8("x"),
            })
        };
        let differ = ExtBoolTerm::Ne(ite("a"), ite("b"));
        let same_arg = ExtBoolTerm::Eq(sym_bv8("a"), sym_bv8("b"));
        match Solver::check_sliver(&[same_arg, differ.clone()]) {
            CheckResult::Unsat(_) => {}
            other => panic!("congruence under an ite must hold; got {other:?}"),
        }
        match Solver::check_sliver(&[differ]) {
            CheckResult::Sat(_) => {}
            other => panic!("with a, b free the calls may differ; got {other:?}"),
        }
    }

    /// `urem`, `sdiv`, `srem`, `rotl`, `not`, `neg` of a call result: each is
    /// a function of the call, so equal arguments give equal results.
    // rivet: verifies VER-066
    #[test]
    fn lifted_arith_over_pure_call_keeps_congruence() {
        use crate::sliver::{ExtBoolTerm, ExtOp};
        type Mk = fn(crate::sliver::ExtBvTerm, crate::sliver::ExtBvTerm) -> ExtOp;
        let ops: [(&str, Mk); 6] = [
            ("urem", ExtOp::Urem),
            ("sdiv", ExtOp::Sdiv),
            ("srem", ExtOp::Srem),
            ("rotl", ExtOp::Rotl),
            ("not", |a, _| ExtOp::Not(a)),
            ("neg", |a, _| ExtOp::Neg(a)),
        ];
        for (name, mk) in ops {
            let t = |arg: &str| xop(mk(f8(sym_bv8(arg)), sym_bv8("d")));
            let same_arg = ExtBoolTerm::Eq(sym_bv8("a"), sym_bv8("b"));
            match Solver::check_sliver(&[same_arg, ExtBoolTerm::Ne(t("a"), t("b"))]) {
                CheckResult::Unsat(_) => {}
                other => {
                    panic!("{name}(f(a), d) must equal {name}(f(b), d) when a = b; got {other:?}")
                }
            }
        }
    }

    /// loom #313's trap guard: `[trap] ++ ite(trap, 0, value)` with the value
    /// a signed division of a memory read by a call result. Whenever the trap
    /// flag is set the value half is forced to zero.
    // rivet: verifies VER-066
    #[test]
    fn loom_trap_guard_over_sdiv_of_select_and_call() {
        use crate::sliver::{ExtBoolTerm, ExtOp};
        let read = sel(base("mem"), sym_bv32("addr"));
        let value = xop(ExtOp::Sdiv(read, f8(sym_bv8("a"))));
        let trap = ExtBoolTerm::Eq(
            f8(sym_bv8("a")),
            crate::sliver::ExtBvTerm::Core(BvTerm::Const {
                value: 0,
                sort: Sort::new(8),
            }),
        );
        let guarded = xop(ExtOp::Ite {
            cond: trap.clone(),
            then_: crate::sliver::ExtBvTerm::Core(BvTerm::Const {
                value: 0,
                sort: Sort::new(8),
            }),
            else_: value,
        });
        let zero = crate::sliver::ExtBvTerm::Core(BvTerm::Const {
            value: 0,
            sort: Sort::new(8),
        });
        match Solver::check_sliver(&[trap.clone(), ExtBoolTerm::Ne(guarded.clone(), zero.clone())])
        {
            CheckResult::Unsat(_) => {}
            other => panic!("a trapping value must be forced to 0; got {other:?}"),
        }
        match Solver::check_sliver(&[
            ExtBoolTerm::Not(Box::new(trap)),
            ExtBoolTerm::Ne(guarded, zero),
        ]) {
            CheckResult::Sat(_) => {}
            other => panic!("a non-trapping value is free to be nonzero; got {other:?}"),
        }
    }

    // rivet: verifies VER-065
    /// #192 phase 6: the SAT gate of `check_with_query` is the trusted
    /// `check_query_model`. A genuine certificate passes it; the same
    /// witness and the same inputs against a query whose first root is
    /// negated — the v1 witness still re-checks (same CNF, assignment and
    /// bit map) and the model still IS the inputs, so the only layer that
    /// can see the DAG is no longer satisfied is the trusted evaluation —
    /// is rejected, and the answer degrades to `Unknown`, never a wrong
    /// `Sat`. A flipped input bit is caught too (by the untrusted
    /// consistency check first, by the trusted check regardless).
    #[test]
    fn a_rejected_model_degrades_to_unknown_not_sat() {
        use crate::query::QueryCheckResult;
        // `a urem 5 = 3` at width 8: a = 3 is a model.
        let mut s = Solver::new();
        s.assert(BoolTerm::Eq(
            Box::new(BvTerm::Urem(Box::new(var("a", 8)), Box::new(c(5, 8)))),
            Box::new(c(3, 8)),
        ));
        let QueryCheckResult::Sat(cert) = s.check_with_query() else {
            panic!("expected Sat");
        };
        assert!(matches!(
            Solver::sat_verdict(cert.clone()),
            QueryCheckResult::Sat(_)
        ));
        // The negated root: witness and inputs untouched.
        let mut negated = cert.clone();
        let root = negated.query.roots[0];
        negated.query.nodes.push(k::DagNode::Not(root));
        negated.query.roots[0] = negated.query.nodes.len() - 1;
        negated
            .witness
            .recheck()
            .expect("the v1 witness is untouched");
        negated
            .inputs
            .check_consistent(&negated.query, &negated.witness.model)
            .expect("the model is still the inputs");
        assert!(
            ordeal_lrat::check_query_model(
                &negated.query.nodes,
                &negated.query.bits,
                &negated.query.roots,
                &negated.inputs.bits
            )
            .is_err(),
            "the trusted crate must reject the negated root"
        );
        assert!(
            matches!(Solver::sat_verdict(negated), QueryCheckResult::Unknown),
            "a query the trusted crate does not accept the model of must degrade to Unknown"
        );
        // A flipped input bit.
        let mut flipped = cert;
        flipped.inputs.bits[0] = !flipped.inputs.bits[0];
        assert!(
            ordeal_lrat::check_query_model(
                &flipped.query.nodes,
                &flipped.query.bits,
                &flipped.query.roots,
                &flipped.inputs.bits
            )
            .is_err(),
            "the trusted crate must reject the flipped input"
        );
        assert!(matches!(
            Solver::sat_verdict(flipped),
            QueryCheckResult::Unknown
        ));
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
            // the same canonicalize → encode → compact → Tseitin steps.
            let (_, cnf) = solver.lower().expect("a decided query lowers");
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
