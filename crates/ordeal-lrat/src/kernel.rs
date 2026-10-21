//! The string-free checking core — **the Aeneas → Lean translation target**.
//!
//! Everything semantic lives here, over already-parsed data: no `&str`, no
//! `String`, no formatting, no I/O. The soundness theorem (issue #12) is
//! stated about [`check_steps`]:
//!
//! > If `check_steps(cnf, steps)` returns `Ok(())`, then `cnf` is
//! > unsatisfiable.
//!
//! The text parser (in `lib.rs`) is **outside** this trusted core, and that
//! is sound by construction: the CNF reaches [`check_steps`] directly (never
//! through the parser), so a buggy parser can only produce a *different*
//! step list — which still has to check against the real CNF — or reject.
//! It can never manufacture an acceptance the core would not itself verify.
//!
//! # Style constraints (Aeneas)
//!
//! This module is written in the fragment Aeneas translates cleanly today:
//! index-based `while` loops instead of iterators/closures, no early
//! `return` inside nested loops (every inner loop is its own function), no
//! slice patterns, and no std methods beyond `Vec::{new, push, len}` and
//! indexing. Keep it that way — a "cleanup" that reintroduces iterator
//! sugar breaks the translation.
//!
//! # One translation unit (issue #192 phase 4)
//!
//! This file is the crate root of the Aeneas translation (`lean/regen.sh`
//! translates it as a standalone crate named `kernel`). The proven
//! lowering — the blast rules, the term-DAG encoder, the folding + hashing
//! pass and the Tseitin encoder — is the submodule [`blast_kernel`],
//! `#[path]`-included so that the same file is a module of this crate under
//! `cargo` and a module of the translation unit under Charon. The Lean model
//! is therefore ONE file, `lean/Kernel.lean`, with the checker in namespace
//! `kernel` and the lowering in `kernel.blast_kernel`; [`check_query`] below
//! composes the two, and `lean/QueryCheck.lean` proves `check_query_sound`
//! about it.

/// The proven lowering (blast rules, DAG encoder, compaction, Tseitin) —
/// the other half of the translation unit (see the module docs).
#[path = "blast_kernel.rs"]
pub mod blast_kernel;

/// The sliver correspondence check (TR-072): the same translation unit,
/// so `kernel.sliver_kernel.*` is modelled next to the checker and the
/// lowering it composes with.
#[path = "sliver_kernel.rs"]
pub mod sliver_kernel;

use blast_kernel::{DagNode, Lit, aig_new, compact, encode, eval_lit, map_word, simulate, tseitin};

/// One already-parsed certificate step.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Step {
    /// Add clause `clause` with id `id`, justified by RUP through `hints`.
    Add {
        /// The 1-based clause id this step claims (must be sequential).
        id: usize,
        /// The added clause's literals (DIMACS convention, no `0`).
        clause: Vec<i32>,
        /// Live clause ids whose in-order unit propagation derives a
        /// conflict from the negated clause.
        hints: Vec<usize>,
    },
    /// Mark the named clause ids dead.
    Delete {
        /// The 1-based ids to delete (must be known and live).
        ids: Vec<usize>,
    },
}

/// Why the core rejected. Data-only (no strings) so the Lean model stays
/// simple; `step` is the 0-based index into the step list (the parser maps
/// it back to a certificate line for reporting).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CoreError {
    /// The input CNF contains the literal `0` or `i32::MIN`.
    InvalidCnfLiteral {
        /// 0-based index of the offending clause in the input CNF.
        clause_index: usize,
    },
    /// An addition step's clause contains the literal `0` or `i32::MIN`.
    /// The text parser already rejects these, but the kernel validates
    /// independently: the kernel's guarantees must not depend on the
    /// (untrusted) parser, and rejecting more is always sound.
    InvalidStepLiteral {
        /// 0-based step index.
        step: usize,
    },
    /// An addition step did not use the next sequential clause id.
    NonSequentialId {
        /// 0-based step index.
        step: usize,
        /// The id this step was required to use.
        expected: usize,
        /// The id the step actually used.
        found: usize,
    },
    /// A hint or deletion referenced an id that was never assigned.
    UnknownId {
        /// 0-based step index.
        step: usize,
        /// The unknown clause id.
        id: usize,
    },
    /// A hint or deletion referenced a clause that was already deleted.
    DeletedId {
        /// 0-based step index.
        step: usize,
        /// The dead clause id.
        id: usize,
    },
    /// A hint clause was neither unit nor falsified under the current
    /// assignment.
    HintNotUnit {
        /// 0-based step index.
        step: usize,
        /// The id of the offending hint clause.
        hint: usize,
    },
    /// The hint list ended before unit propagation reached a conflict.
    HintsExhausted {
        /// 0-based step index.
        step: usize,
    },
    /// No verified addition of the empty clause occurred.
    NoEmptyClause,
}

/// The variable index of a literal. `lit` must be nonzero and not
/// `i32::MIN` — guaranteed KERNEL-SIDE for every literal that reaches an
/// assignment: `load_cnf` validates the CNF and `apply_add` validates each
/// certificate clause (both via `clause_has_invalid_literal`), and the
/// property is preserved under negation. Hand-rolled so the Lean model
/// needs no `unsigned_abs` axiom.
fn lit_var(lit: i32) -> usize {
    if lit >= 0 {
        lit as usize
    } else {
        (-lit) as usize
    }
}

/// A partial assignment over DIMACS variables.
///
/// `values[v]` is the value of variable `v` (index 0 unused), `None` when
/// unassigned. The vector grows on demand (by pushes; see `assign_true`).
struct Assignment {
    values: Vec<Option<bool>>,
}

impl Assignment {
    fn new() -> Self {
        Assignment { values: Vec::new() }
    }

    /// The truth value of `lit` under this assignment, or `None` if the
    /// underlying variable is unassigned. `lit` must be nonzero and not
    /// `i32::MIN` (guaranteed by CNF validation and parsing).
    fn value(&self, lit: i32) -> Option<bool> {
        let var = lit_var(lit);
        if var >= self.values.len() {
            return None;
        }
        match self.values[var] {
            None => None,
            Some(var_value) => {
                if lit > 0 {
                    Some(var_value)
                } else {
                    Some(!var_value)
                }
            }
        }
    }

    /// Make `lit` true. Returns `true` iff this contradicts an existing
    /// assignment (i.e. `lit` was already false — a conflict).
    fn assign_true(&mut self, lit: i32) -> bool {
        match self.value(lit) {
            Some(true) => false, // already true: nothing to do
            Some(false) => true, // conflict
            None => {
                let var = lit_var(lit);
                while self.values.len() <= var {
                    self.values.push(None);
                }
                self.values[var] = Some(lit > 0);
                false
            }
        }
    }
}

/// Look up a clause id, requiring it to be known and still live.
fn get_live(clauses: &[Option<Vec<i32>>], id: usize, step: usize) -> Result<&[i32], CoreError> {
    if id == 0 || id > clauses.len() {
        return Err(CoreError::UnknownId { step, id });
    }
    match &clauses[id - 1] {
        Some(clause) => Ok(clause),
        None => Err(CoreError::DeletedId { step, id }),
    }
}

/// Assume the negation of every literal of `clause` (make each false).
/// Returns `true` iff a conflict arose — i.e. the clause is a tautology,
/// which verifies the step trivially.
fn assume_negation(assignment: &mut Assignment, clause: &[i32]) -> bool {
    let mut i = 0;
    while i < clause.len() {
        if assignment.assign_true(-clause[i]) {
            return true;
        }
        i += 1;
    }
    false
}

/// Does `lits[0..len]` contain `lit`? (Hand-rolled: keeps the Aeneas
/// translation free of slice-method externals.)
fn contains_lit(lits: &[i32], lit: i32) -> bool {
    let mut i = 0;
    while i < lits.len() {
        if lits[i] == lit {
            return true;
        }
        i += 1;
    }
    false
}

/// How a hint clause looks under the current assignment.
enum HintClass {
    /// Some literal is already true: useless for propagation.
    Satisfied,
    /// Every literal is false: conflict — the step is verified.
    Falsified,
    /// Exactly one unassigned literal (duplicates collapsed): propagate it.
    Unit(i32),
    /// Two or more distinct unassigned literals: not a usable hint.
    Multi,
}

/// Classify one hint clause under the current assignment. Duplicate
/// literals are collapsed so that e.g. `[x, x]` counts as unit on `x`.
fn classify_hint(assignment: &Assignment, clause: &[i32]) -> HintClass {
    let mut unassigned: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < clause.len() {
        let lit = clause[i];
        match assignment.value(lit) {
            Some(true) => return HintClass::Satisfied,
            Some(false) => {}
            None => {
                if !contains_lit(&unassigned, lit) {
                    unassigned.push(lit);
                }
            }
        }
        i += 1;
    }
    match unassigned.len() {
        0 => HintClass::Falsified,
        1 => HintClass::Unit(unassigned[0]),
        _ => HintClass::Multi,
    }
}

/// Verify one RUP addition step: assume the negation of `new_clause`, then
/// unit-propagate through the hint clauses in order; each hint must be unit
/// (assign its literal) or falsified (conflict — verified).
///
/// `Ok(())` means the hint chain derived a conflict, i.e. `new_clause` is
/// implied by the live clauses.
fn check_rup(
    clauses: &[Option<Vec<i32>>],
    new_clause: &[i32],
    hints: &[usize],
    step: usize,
) -> Result<(), CoreError> {
    let mut assignment = Assignment::new();

    if assume_negation(&mut assignment, new_clause) {
        return Ok(());
    }

    // Propagate through the hint clauses, in order. The loop carries its
    // outcome in `outcome` instead of returning early (Aeneas constraint).
    let mut outcome: Option<Result<(), CoreError>> = None;
    let mut i = 0;
    while outcome.is_none() && i < hints.len() {
        let hint_id = hints[i];
        match get_live(clauses, hint_id, step) {
            Err(e) => outcome = Some(Err(e)),
            Ok(clause) => match classify_hint(&assignment, clause) {
                HintClass::Falsified => outcome = Some(Ok(())),
                HintClass::Unit(unit) => {
                    // It cannot conflict: the literal was unassigned.
                    let conflict = assignment.assign_true(unit);
                    debug_assert!(!conflict);
                }
                HintClass::Satisfied | HintClass::Multi => {
                    outcome = Some(Err(CoreError::HintNotUnit {
                        step,
                        hint: hint_id,
                    }));
                }
            },
        }
        i += 1;
    }

    match outcome {
        Some(result) => result,
        None => Err(CoreError::HintsExhausted { step }),
    }
}

/// Does a clause contain an invalid literal (`0`, or `i32::MIN` whose
/// negation would overflow)?
fn clause_has_invalid_literal(clause: &[i32]) -> bool {
    let mut i = 0;
    while i < clause.len() {
        if clause[i] == 0 || clause[i] == i32::MIN {
            return true;
        }
        i += 1;
    }
    false
}

/// Load the input CNF as live clauses with ids `1..=cnf.len()`, validating
/// every literal so later negation is always meaningful and safe.
fn load_cnf(cnf: &[Vec<i32>]) -> Result<Vec<Option<Vec<i32>>>, CoreError> {
    let mut clauses: Vec<Option<Vec<i32>>> = Vec::new();
    let mut i = 0;
    while i < cnf.len() {
        if clause_has_invalid_literal(&cnf[i]) {
            return Err(CoreError::InvalidCnfLiteral { clause_index: i });
        }
        clauses.push(Some(cnf[i].clone()));
        i += 1;
    }
    Ok(clauses)
}

/// Overwrite one slot with `None`. Split into a helper: assigning the enum
/// constant directly through an index projection (`clauses[i] = None`)
/// currently extracts incorrectly in Aeneas (the stored value becomes `()`);
/// routing the write through a plain `&mut` extracts correctly.
fn clear_slot(slot: &mut Option<Vec<i32>>) {
    *slot = None;
}

/// Mark every id in `ids` dead. Deleting an unknown or already-dead clause
/// is rejected: the certificate and checker disagree about the clause set.
fn apply_delete(
    clauses: &mut [Option<Vec<i32>>],
    ids: &[usize],
    step: usize,
) -> Result<(), CoreError> {
    let mut i = 0;
    while i < ids.len() {
        let id = ids[i];
        get_live(clauses, id, step)?;
        clear_slot(&mut clauses[id - 1]);
        i += 1;
    }
    Ok(())
}

/// Verify one addition step and append its clause. Returns `true` iff the
/// added (verified) clause is the empty clause — the certificate's goal.
fn apply_add(
    clauses: &mut Vec<Option<Vec<i32>>>,
    id: usize,
    clause: &[i32],
    hints: &[usize],
    step: usize,
) -> Result<bool, CoreError> {
    // Independent kernel-side validation of the certificate clause: the
    // untrusted parser also rejects 0 / i32::MIN, but the soundness
    // invariant ("every live clause is implied under EVERY assignment")
    // must not lean on the parser, and negating i32::MIN must be
    // impossible in the kernel regardless of who produced the steps.
    if clause_has_invalid_literal(clause) {
        return Err(CoreError::InvalidStepLiteral { step });
    }
    let expected = clauses.len() + 1;
    if id != expected {
        return Err(CoreError::NonSequentialId {
            step,
            expected,
            found: id,
        });
    }
    check_rup(clauses, clause, hints, step)?;
    // `len() == 0` instead of `is_empty()`: keeps the Lean model free of a
    // `Vec::is_empty` axiom.
    #[allow(clippy::len_zero)]
    let is_empty = clause.len() == 0;
    clauses.push(Some(clause.to_vec()));
    Ok(is_empty)
}

/// Check a parsed step list against the input CNF.
///
/// Returns `Ok(())` iff some verified addition step adds the **empty
/// clause**, which proves the CNF unsatisfiable (checking stops there;
/// trailing steps are ignored). See the module docs for the soundness
/// theorem this function carries.
pub fn check_steps(cnf: &[Vec<i32>], steps: &[Step]) -> Result<(), CoreError> {
    let mut clauses = load_cnf(cnf)?;

    // The loop carries its outcome in `outcome` instead of returning early
    // (Aeneas constraint): `Some(Ok(()))` the moment a verified empty
    // clause lands — nothing after it can change unsatisfiability — and
    // `Some(Err(..))` on the first rejection.
    let mut outcome: Option<Result<(), CoreError>> = None;
    let mut step_index = 0;
    while outcome.is_none() && step_index < steps.len() {
        // Owned copy: keeps the loop free of a shared borrow of `steps`
        // alongside the mutable borrow of `clauses` (Aeneas join limits).
        // This kernel optimizes for provability, not allocation counts.
        let current = steps[step_index].clone();
        match current {
            Step::Delete { ids } => {
                if let Err(e) = apply_delete(&mut clauses, &ids, step_index) {
                    outcome = Some(Err(e));
                }
            }
            Step::Add { id, clause, hints } => {
                match apply_add(&mut clauses, id, &clause, &hints, step_index) {
                    Err(e) => outcome = Some(Err(e)),
                    Ok(true) => outcome = Some(Ok(())),
                    Ok(false) => {}
                }
            }
        }
        step_index += 1;
    }

    match outcome {
        Some(result) => result,
        None => Err(CoreError::NoEmptyClause),
    }
}

/// Why the kernel rejected a SAT witness. Data-only (no strings), like
/// [`CoreError`], so the Lean model stays simple.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SatWitnessError {
    /// The input CNF contains the literal `0` or `i32::MIN`.
    InvalidCnfLiteral {
        /// 0-based index of the offending clause.
        clause_index: usize,
    },
    /// A literal references a variable past the end of the assignment.
    AssignmentTooShort {
        /// The 1-based DIMACS variable index that was out of range.
        var: usize,
    },
    /// A clause has no literal made true by the assignment.
    UnsatisfiedClause {
        /// 0-based index of the unsatisfied clause.
        clause_index: usize,
    },
    /// A model binding's value disagrees with the assignment at one bit.
    BindingMismatch {
        /// 0-based bit index (within the binding) that disagrees.
        bit: usize,
    },
    /// A binding names more bits than a `u128` value can carry.
    BindingTooWide {
        /// The offending bit count.
        bits: usize,
    },
}

/// Is some literal of `clause` true under `assignment`? (Own function so
/// the caller's loop has no early return — Aeneas constraint; same style
/// as [`classify_hint`].) `assignment[i]` is the value of DIMACS variable
/// `i + 1`. The variable is computed by [`lit_var`], as in
/// [`check_binding`] — the kernel has exactly one spelling of `|lit|`.
/// (It was `lit.unsigned_abs() as usize` until TR-044: identical for the
/// non-`MIN` literals that reach it, but `i32::unsigned_abs` has no model
/// in the pinned Aeneas and was extracted as an opaque `axiom`, which
/// made the SAT-witness theorems conditional. The `ci.yml` "generated
/// models carry no axioms" gate now fails on any recurrence.)
fn clause_satisfied(
    clause: &[i32],
    assignment: &[bool],
    clause_index: usize,
) -> Result<bool, SatWitnessError> {
    let mut sat = false;
    let mut i = 0;
    while !sat && i < clause.len() {
        let lit = clause[i];
        if lit == 0 || lit == i32::MIN {
            return Err(SatWitnessError::InvalidCnfLiteral { clause_index });
        }
        let var = lit_var(lit);
        if var > assignment.len() {
            return Err(SatWitnessError::AssignmentTooShort { var });
        }
        let value = assignment[var - 1];
        if (lit > 0 && value) || (lit < 0 && !value) {
            sat = true;
        }
        i += 1;
    }
    Ok(sat)
}

/// Check a claimed satisfying assignment against a CNF — the SAT twin of
/// [`check_steps`] (TR-038, the ordeal-cert/v1 witness):
///
/// > If `check_sat(cnf, assignment)` returns `Ok(())`, then `cnf` is
/// > satisfiable — by exhibition: `assignment` makes some literal of
/// > every clause true.
///
/// A linear scan, no search, no solver state: soundness is immediate from
/// the definition of satisfaction, which is what makes this small enough
/// to sit in the trusted kernel. Machine-checked over the Aeneas model as
/// `kernel.spec.check_sat_sound` / `check_sat_satisfiable`
/// (lean/SatWitness.lean, TR-044 / VER-039), axiom-clean like the LRAT
/// path; `verdicts_exclusive` there shows no CNF has both an accepted
/// refutation and an accepted witness. See docs/formal-verification.md.
pub fn check_sat(cnf: &[Vec<i32>], assignment: &[bool]) -> Result<(), SatWitnessError> {
    let mut clause_index = 0;
    while clause_index < cnf.len() {
        if !clause_satisfied(&cnf[clause_index], assignment, clause_index)? {
            return Err(SatWitnessError::UnsatisfiedClause { clause_index });
        }
        clause_index += 1;
    }
    Ok(())
}

/// Check one model binding against the assignment: bit `k` of `value`
/// (LSB-first) must equal the truth value of the DIMACS **literal**
/// `bits[k]` — signed, because Tseitin encoding may bind a model bit to a
/// negated CNF literal (`-v` means "bit k is the negation of variable
/// v"). This is what makes the *advertised* model part of the witness
/// rather than decoration: a bundle whose model disagrees with its own
/// assignment is rejected here (TR-038). Machine-checked as
/// `kernel.spec.check_binding_sound` (lean/SatWitness.lean, TR-044):
/// accepted ⟹ bit `k` of `value` equals the truth value of `bits[k]` under
/// the assignment — axiom-clean.
pub fn check_binding(
    assignment: &[bool],
    bits: &[i32],
    value: u128,
) -> Result<(), SatWitnessError> {
    if bits.len() > 128 {
        return Err(SatWitnessError::BindingTooWide { bits: bits.len() });
    }
    let mut k = 0;
    while k < bits.len() {
        let lit = bits[k];
        if lit == 0 || lit == i32::MIN {
            return Err(SatWitnessError::InvalidCnfLiteral { clause_index: k });
        }
        let var = lit_var(lit);
        if var > assignment.len() {
            return Err(SatWitnessError::AssignmentTooShort { var });
        }
        let var_value = assignment[var - 1];
        let bit = (value >> k) & 1;
        // Four-way branch instead of boolean-valued lets: every comparison
        // sits in an `if` condition, the position the Aeneas translation
        // handles cleanly (a `!x` / `x == y` in a value position extracted
        // as Prop and broke the model's elaboration — caught by the
        // regenerate-then-prove gate on the first CI run).
        if lit > 0 {
            if var_value {
                if bit != 1 {
                    return Err(SatWitnessError::BindingMismatch { bit: k });
                }
            } else if bit != 0 {
                return Err(SatWitnessError::BindingMismatch { bit: k });
            }
        } else if var_value {
            if bit != 0 {
                return Err(SatWitnessError::BindingMismatch { bit: k });
            }
        } else if bit != 1 {
            return Err(SatWitnessError::BindingMismatch { bit: k });
        }
        k += 1;
    }
    Ok(())
}

// ───────────── The query re-check (issue #192 phase 4) ─────────────

/// Why [`check_query`] rejected. Data-only (no strings), like
/// [`CoreError`], so the Lean model stays simple.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QueryError {
    /// DAG node `node` is not well-formed: an operand is not an earlier
    /// node, operand widths disagree or are zero, an extract range or a
    /// constant slice does not fit, or the node's width would overflow
    /// `usize` (`dag_wf`; the Lean `DagWF` predicate).
    NodeNotWellFormed {
        /// 0-based index of the offending node.
        node: usize,
    },
    /// Root entry `root` does not name a boolean (width-1) node of the DAG.
    BadRoot {
        /// 0-based index into the root list.
        root: usize,
    },
    /// The query is beyond the capacity the soundness theorems are stated
    /// for: the arena's gate budget, the `i32` variable numbers or the
    /// clause count would not fit. Rejecting is sound; nothing this size
    /// is ever produced in practice.
    TooLarge,
    /// The LRAT steps do not refute the CNF re-encoded from the DAG.
    Check(CoreError),
}

/// Two bitvector operands `a`, `b` of an earlier node each, of the same
/// positive width (`DagNodeWF`'s binary-word case).
fn bin_wf(ws: &[usize], a: usize, b: usize) -> bool {
    let n = ws.len();
    a < n && b < n && ws[a] > 0 && ws[a] == ws[b]
}

/// Two boolean operands (width 1) of an earlier node each.
fn bool_bin_wf(ws: &[usize], a: usize, b: usize) -> bool {
    let n = ws.len();
    a < n && b < n && ws[a] == 1 && ws[b] == 1
}

/// One bitvector operand `a` of an earlier node, of positive width
/// (`DagNodeWF`'s unary-word case: `BvNot`, `Neg`).
fn un_wf(ws: &[usize], a: usize) -> bool {
    let n = ws.len();
    a < n && ws[a] > 0
}

/// One bitvector operand of positive width whose extension would not
/// overflow `usize` (`ZeroExt` / `SignExt`).
fn ext_wf(ws: &[usize], a: usize, by: usize) -> bool {
    let n = ws.len();
    a < n && ws[a] > 0 && ws[a] <= usize::MAX - by
}

/// Well-formedness of ONE node against the widths `ws` of the nodes before
/// it (`ws.len()` is the node's own index) and the size `nbits` of the
/// constant table: the Lean `DagNodeWF` predicate (`lean/BlasterDag.lean`)
/// plus "the node's width fits `usize`" (`Concat` and the extensions add
/// widths; a sum past `usize::MAX` is rejected rather than wrapped).
/// `dag_wf_spec` proves exactly that equivalence. The five derived
/// operators (phase 5) are word operators like the ones they used to be
/// rewritten into.
fn node_wf(ws: &[usize], nbits: usize, node: DagNode) -> bool {
    let n = ws.len();
    match node {
        DagNode::Var(w) => w > 0,
        DagNode::Const(s, w) => w > 0 && s <= nbits && w <= nbits - s,
        DagNode::Add(a, b) => bin_wf(ws, a, b),
        DagNode::Sub(a, b) => bin_wf(ws, a, b),
        DagNode::Mul(a, b) => bin_wf(ws, a, b),
        DagNode::Udiv(a, b) => bin_wf(ws, a, b),
        DagNode::Urem(a, b) => bin_wf(ws, a, b),
        DagNode::And(a, b) => bin_wf(ws, a, b),
        DagNode::Or(a, b) => bin_wf(ws, a, b),
        DagNode::Xor(a, b) => bin_wf(ws, a, b),
        DagNode::Shl(a, b) => bin_wf(ws, a, b),
        DagNode::Lshr(a, b) => bin_wf(ws, a, b),
        DagNode::Ashr(a, b) => bin_wf(ws, a, b),
        DagNode::Rotr(a, b) => bin_wf(ws, a, b),
        DagNode::Extract(hi, lo, a) => a < n && lo <= hi && hi < ws[a],
        DagNode::Concat(a, b) => {
            a < n && b < n && ws[a] > 0 && ws[b] > 0 && ws[a] <= usize::MAX - ws[b]
        }
        DagNode::ZeroExt(a, by) => ext_wf(ws, a, by),
        DagNode::SignExt(a, by) => ext_wf(ws, a, by),
        DagNode::Ite(c, t, e) => {
            c < n && t < n && e < n && ws[c] == 1 && ws[t] > 0 && ws[t] == ws[e]
        }
        DagNode::Eq(a, b) => bin_wf(ws, a, b),
        DagNode::Ne(a, b) => bin_wf(ws, a, b),
        DagNode::Ult(a, b) => bin_wf(ws, a, b),
        DagNode::Ule(a, b) => bin_wf(ws, a, b),
        DagNode::Ugt(a, b) => bin_wf(ws, a, b),
        DagNode::Uge(a, b) => bin_wf(ws, a, b),
        DagNode::Slt(a, b) => bin_wf(ws, a, b),
        DagNode::Sle(a, b) => bin_wf(ws, a, b),
        DagNode::Sgt(a, b) => bin_wf(ws, a, b),
        DagNode::Sge(a, b) => bin_wf(ws, a, b),
        DagNode::Not(a) => a < n && ws[a] == 1,
        DagNode::BoolAnd(a, b) => bool_bin_wf(ws, a, b),
        DagNode::BoolOr(a, b) => bool_bin_wf(ws, a, b),
        DagNode::BvNot(a) => un_wf(ws, a),
        DagNode::Neg(a) => un_wf(ws, a),
        DagNode::Rotl(a, b) => bin_wf(ws, a, b),
        DagNode::Sdiv(a, b) => bin_wf(ws, a, b),
        DagNode::Srem(a, b) => bin_wf(ws, a, b),
    }
}

/// The width of one node from the widths of the earlier nodes (the Lean
/// `dagNodeWidth`). Only called after [`node_wf`] accepted the node, so
/// every index is in range and no sum overflows.
fn node_width(ws: &[usize], node: DagNode) -> usize {
    match node {
        DagNode::Var(w) => w,
        DagNode::Const(_, w) => w,
        DagNode::Add(a, _) => ws[a],
        DagNode::Sub(a, _) => ws[a],
        DagNode::Mul(a, _) => ws[a],
        DagNode::Udiv(a, _) => ws[a],
        DagNode::Urem(a, _) => ws[a],
        DagNode::And(a, _) => ws[a],
        DagNode::Or(a, _) => ws[a],
        DagNode::Xor(a, _) => ws[a],
        DagNode::Shl(a, _) => ws[a],
        DagNode::Lshr(a, _) => ws[a],
        DagNode::Ashr(a, _) => ws[a],
        DagNode::Rotr(a, _) => ws[a],
        DagNode::Extract(hi, lo, _) => hi - lo + 1,
        DagNode::Concat(a, b) => ws[a] + ws[b],
        DagNode::ZeroExt(a, by) => ws[a] + by,
        DagNode::SignExt(a, by) => ws[a] + by,
        DagNode::Ite(_, t, _) => ws[t],
        DagNode::Eq(_, _) => 1,
        DagNode::Ne(_, _) => 1,
        DagNode::Ult(_, _) => 1,
        DagNode::Ule(_, _) => 1,
        DagNode::Ugt(_, _) => 1,
        DagNode::Uge(_, _) => 1,
        DagNode::Slt(_, _) => 1,
        DagNode::Sle(_, _) => 1,
        DagNode::Sgt(_, _) => 1,
        DagNode::Sge(_, _) => 1,
        DagNode::Not(_) => 1,
        DagNode::BoolAnd(_, _) => 1,
        DagNode::BoolOr(_, _) => 1,
        DagNode::BvNot(a) => ws[a],
        DagNode::Neg(a) => ws[a],
        DagNode::Rotl(a, _) => ws[a],
        DagNode::Sdiv(a, _) => ws[a],
        DagNode::Srem(a, _) => ws[a],
    }
}

/// The proven well-formedness check of a term DAG (issue #192 phase 4):
/// every node against the widths of the nodes before it, in order,
/// returning every node's width. `Ok(ws)` iff the DAG satisfies the Lean
/// `DagWF` predicate the encoder's soundness theorem assumes (and every
/// width fits `usize`) — `dag_wf_spec` in `lean/QueryCheck.lean`. `nbits`
/// is the length of the constant table the `Const` nodes slice.
pub fn dag_wf(ns: &[DagNode], nbits: usize) -> Result<Vec<usize>, QueryError> {
    let mut ws: Vec<usize> = Vec::new();
    let n = ns.len();
    let mut i = 0usize;
    while i < n {
        let node = ns[i];
        if !node_wf(&ws, nbits, node) {
            return Err(QueryError::NodeNotWellFormed { node: i });
        }
        let w = node_width(&ws, node);
        ws.push(w);
        i += 1;
    }
    Ok(ws)
}

/// Every root names a boolean (width-1) node: the encoder's `hroots`
/// precondition.
pub fn roots_wf(ws: &[usize], roots: &[usize]) -> Result<(), QueryError> {
    let n = ws.len();
    let m = roots.len();
    let mut r = 0usize;
    while r < m {
        let root = roots[r];
        if root >= n || ws[root] != 1 {
            return Err(QueryError::BadRoot { root: r });
        }
        r += 1;
    }
    Ok(())
}

/// The largest width in `ws` (0 for an empty DAG): the width bound `W` of
/// `encode_sound`.
pub fn max_width(ws: &[usize]) -> usize {
    let mut m = 0usize;
    let n = ws.len();
    let mut i = 0usize;
    while i < n {
        if ws[i] > m {
            m = ws[i];
        }
        i += 1;
    }
    m
}

/// Is `1 + n * (70·w² + 70·w + 1) <= usize::MAX` — the arena capacity
/// hypothesis of `encode_sound` (`gateBound`), for a DAG of `n` nodes whose
/// widths are at most `w`? Computed without overflowing: every product is
/// bounded by a division first (`x * y <= MAX` iff `x <= MAX / y`). The
/// budget was `25·w² + 20·w + 1` until phase 5; `bvrotl` at a
/// non-power-of-two width (three remainders plus the barrel) needs
/// `66·w² + 69·w + 3·w·stages`, so one node's budget is now `70·w² + 70·w +
/// 1`. Nothing a solver produces comes near it (`w ≤ 128`, so `1.2·10^6`
/// gates per node against `usize::MAX`).
pub fn encode_fits(w: usize, n: usize) -> bool {
    let max = usize::MAX;
    if w > max / 70 {
        return false;
    }
    let w70 = 70 * w;
    if w > 0 && w70 > max / w {
        return false;
    }
    let sq = w70 * w;
    let lin = 70 * w;
    if sq > max - lin {
        return false;
    }
    let s = sq + lin;
    if s > max - 1 {
        return false;
    }
    let gb = s + 1;
    if n > 0 && gb > max / n {
        return false;
    }
    let total = n * gb;
    total < max
}

/// Is `1 + 3 * nodes + outs < usize::MAX` — the clause-count capacity of
/// `tseitin_sat_preserving`? Computed without overflowing.
pub fn tseitin_fits(nodes: usize, outs: usize) -> bool {
    let max = usize::MAX;
    if nodes > max / 3 {
        return false;
    }
    let three = 3 * nodes;
    if outs > max - 2 {
        return false;
    }
    three <= max - 2 - outs
}

/// **The query re-check** (issue #192 phase 4, `ordeal-cert/v2`): accept
/// iff the term DAG `ns` (constants in `bits`, asserted roots `roots`) is
/// well-formed and `steps` is an LRAT refutation of the CNF that the
/// proven lowering — `encode`, `compact` with the certificate's `hints`,
/// `map_word`, `tseitin` — produces from it. The solver lowers through the
/// very same functions, so the CNF re-encoded here is the CNF it solved;
/// a consumer who re-checks a v2 bundle certifies the QUERY, not a CNF it
/// has to take on faith.
///
/// > If `check_query(ns, bits, roots, hints, steps)` returns `Ok(cnf)`,
/// > then no assignment to the DAG's variables makes every root true.
///
/// The `Ok` payload is the re-encoded CNF (so a bundle reader can confirm
/// it is the CNF the bundle also carries for v1 readers); the soundness
/// statement does not depend on it. Machine-checked as
/// `kernel.spec.check_query_sound` (`lean/QueryCheck.lean`):
/// `dag_wf_spec` discharges the `DagWF` precondition that phase 3's
/// `dag_refuted` assumed, the capacity checks discharge its `usize` /
/// `i32` hypotheses, and the rest is `dag_refuted` itself. The hints are
/// untrusted advice (`compact_sound` holds for any hints); the steps are
/// untrusted (`lrat_check_sound`).
pub fn check_query(
    ns: &[DagNode],
    bits: &[bool],
    roots: &[usize],
    hints: &[usize],
    steps: &[Step],
) -> Result<Vec<Vec<i32>>, QueryError> {
    let ws = dag_wf(ns, bits.len())?;
    roots_wf(&ws, roots)?;
    let wmax = max_width(&ws);
    if !encode_fits(wmax, ns.len()) {
        return Err(QueryError::TooLarge);
    }
    let mut raw = aig_new();
    let (_words, outs) = encode(&mut raw, ns, bits, roots);
    let (aig, map) = compact(&raw, hints);
    let outs2 = map_word(&map, &outs);
    // `i32::MAX` spelled out: the Lean spec compares against `I32.max`.
    if aig.nodes.len() > 2147483647 || !tseitin_fits(aig.nodes.len(), outs2.len()) {
        return Err(QueryError::TooLarge);
    }
    let cnf = tseitin(&aig, &outs2);
    if steps.len() > usize::MAX - cnf.len() {
        return Err(QueryError::TooLarge);
    }
    match check_steps(&cnf, steps) {
        Ok(()) => Ok(cnf),
        Err(e) => Err(QueryError::Check(e)),
    }
}

// ───────────── The model re-check (issue #192 phase 6, TR-065) ─────────────

/// Why [`check_query_model`] rejected. Data-only, like [`QueryError`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ModelError {
    /// The DAG is malformed, a root is not boolean, or the query exceeds
    /// the proven capacity — the same checks [`check_query`] runs first
    /// (`QueryError::Check` cannot occur here: no steps are involved).
    Query(QueryError),
    /// The input assignment is shorter than the DAG's primary inputs: the
    /// `Var` nodes take `needed` bits in node order, `given` were supplied.
    /// (An assignment with MORE bits than needed is accepted; the surplus
    /// is never read.)
    ModelTooShort {
        /// Bits the DAG's variables take (the Lean `dagNin`).
        needed: usize,
        /// Bits supplied.
        given: usize,
    },
    /// Root entry `root` evaluates to false under the assignment.
    RootFalse {
        /// 0-based index into the root list.
        root: usize,
    },
}

/// The number of primary-input bits the DAG's variables take — the sum of
/// the `Var` widths in node order (the Lean `dagNin`), which is how the
/// encoder numbers the AIG inputs and how `dagSim` reads a `Var` node's
/// bits off the input list. `Err(TooLarge)` if the sum would overflow
/// `usize` (rejected rather than wrapped; unreachable after
/// [`encode_fits`] accepted, kept so this function is total on its own).
pub fn dag_nin(ns: &[DagNode]) -> Result<usize, ModelError> {
    let mut nin = 0usize;
    let n = ns.len();
    let mut i = 0usize;
    while i < n {
        // Copied into a local first: the pinned Aeneas cannot interpret a
        // slice index as a pattern scrutinee (`dag_wf` does the same).
        let node = ns[i];
        if let DagNode::Var(w) = node {
            if w > usize::MAX - nin {
                return Err(ModelError::Query(QueryError::TooLarge));
            }
            nin += w;
        }
        i += 1;
    }
    Ok(nin)
}

/// **The model re-check** (issue #192 phase 6, TR-065): the SAT twin of
/// [`check_query`]. Accept iff the term DAG `ns` (constants in `bits`,
/// asserted roots `roots`) is well-formed and, under the primary-input
/// assignment `inp` — bit `nin + j` is bit `j` (LSB first) of the `Var`
/// node that is reached after `nin` earlier input bits, exactly the
/// `inp : List Bool` the DAG semantics `dagSim` reads — EVERY root
/// evaluates to true.
///
/// > If `check_query_model(ns, bits, roots, inp)` returns `Ok(())`, then
/// > `inp` makes every root of the DAG true: the DAG is satisfiable, and
/// > `inp` is a witness.
///
/// Built from the same proven pieces as the UNSAT direction, with no new
/// evaluator to trust: `dag_wf` / `roots_wf` / `encode_fits` establish
/// the hypotheses of `encode_sound`, [`dag_nin`] checks the assignment
/// covers every input the encoder will create (`simulate` reads
/// `inputs[k]`; a short assignment is rejected, never padded), then the
/// proven `encode` builds the AIG and the proven `simulate` evaluates it
/// — `encode_sound` says every asserted output literal simulates to its
/// root's `dagBool` value, so checking the output literals IS checking
/// the roots. Machine-checked as `kernel.spec.check_query_model_sound`
/// (`lean/QueryCheck.lean`): accepted ⟹ `∀ k < roots.len, dagBool inp
/// bits ns roots[k] = true` — the SAME `dagBool` that `check_query_sound`
/// negates, so a SAT and an UNSAT claim about one query are about one
/// semantics (`query_verdicts_exclusive`). No compaction and no Tseitin
/// here: the model is checked against the raw encoding, which is what
/// the theorem is about; the CNF-level witness (`check_sat` /
/// `check_binding`) remains the v1 check.
pub fn check_query_model(
    ns: &[DagNode],
    bits: &[bool],
    roots: &[usize],
    inp: &[bool],
) -> Result<(), ModelError> {
    let ws = match dag_wf(ns, bits.len()) {
        Ok(ws) => ws,
        Err(e) => return Err(ModelError::Query(e)),
    };
    match roots_wf(&ws, roots) {
        Ok(()) => {}
        Err(e) => return Err(ModelError::Query(e)),
    }
    let wmax = max_width(&ws);
    if !encode_fits(wmax, ns.len()) {
        return Err(ModelError::Query(QueryError::TooLarge));
    }
    let nin = dag_nin(ns)?;
    if inp.len() < nin {
        return Err(ModelError::ModelTooShort {
            needed: nin,
            given: inp.len(),
        });
    }
    let mut raw = aig_new();
    let (_words, outs) = encode(&mut raw, ns, bits, roots);
    let vals = simulate(&raw, inp);
    let m = outs.len();
    let mut k = 0usize;
    while k < m {
        if !eval_lit(&vals, outs[k]) {
            return Err(ModelError::RootFalse { root: k });
        }
        k += 1;
    }
    Ok(())
}

// ───────────── The term-to-DAG correspondence check (issue #192 phase 7) ─────────────

/// Why [`check_term_dag`] rejected. Data-only, like [`QueryError`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TermError {
    /// The term (the flattened, un-canonicalized assertions) is malformed
    /// or too large (`dag_wf` on it).
    Term(QueryError),
    /// The lowered DAG is malformed or too large (`dag_wf` on it).
    Query(QueryError),
    /// The map does not have one entry per term node.
    MapLength {
        /// The term's node count.
        expected: usize,
        /// The map's length.
        found: usize,
    },
    /// Term node `node` is mapped past the end of the lowered DAG.
    MapOutOfRange {
        /// 0-based index of the term node.
        node: usize,
    },
    /// Term node `node` is a variable whose image is not a variable of the
    /// same width, or whose image is already the image of another
    /// variable (two term variables aliased to one DAG variable would make
    /// the DAG MORE constrained — a refutation of it would say nothing
    /// about the term).
    VarMismatch {
        /// 0-based index of the term node.
        node: usize,
    },
    /// Term node `node` is a constant whose image is not the same constant.
    ConstMismatch {
        /// 0-based index of the term node.
        node: usize,
    },
    /// Term node `node` is an operator whose image is neither the same
    /// operator over the images of its operands, nor that with the
    /// operands of a commutative operator swapped, nor the mirror of a
    /// comparison.
    NodeMismatch {
        /// 0-based index of the term node.
        node: usize,
    },
    /// Term node `node` is an operator whose image is a constant, but the
    /// node is not closed (its cone reads a variable), its width differs,
    /// or the constant is not the node's value.
    FoldMismatch {
        /// 0-based index of the term node.
        node: usize,
    },
    /// The asserted roots do not correspond one for one through the map.
    RootMismatch,
}

/// A node's constructor, as a number (`Var` 0, `Const` 1, then the
/// operators in declaration order). Comparing tags and fields
/// ([`node_f1`], [`node_f2`], [`node_f3`]) is how the fragment spells
/// structural equality of two nodes without a derived `==` (which the
/// pinned Aeneas has no model of), and without a nested match on two
/// enums (which it expands to 37 × 37 arms).
fn node_tag(node: DagNode) -> usize {
    match node {
        DagNode::Var(_) => 0,
        DagNode::Const(_, _) => 1,
        DagNode::Add(_, _) => 2,
        DagNode::Sub(_, _) => 3,
        DagNode::Mul(_, _) => 4,
        DagNode::Udiv(_, _) => 5,
        DagNode::Urem(_, _) => 6,
        DagNode::And(_, _) => 7,
        DagNode::Or(_, _) => 8,
        DagNode::Xor(_, _) => 9,
        DagNode::Shl(_, _) => 10,
        DagNode::Lshr(_, _) => 11,
        DagNode::Ashr(_, _) => 12,
        DagNode::Rotr(_, _) => 13,
        DagNode::Extract(_, _, _) => 14,
        DagNode::Concat(_, _) => 15,
        DagNode::ZeroExt(_, _) => 16,
        DagNode::SignExt(_, _) => 17,
        DagNode::Ite(_, _, _) => 18,
        DagNode::Eq(_, _) => 19,
        DagNode::Ne(_, _) => 20,
        DagNode::Ult(_, _) => 21,
        DagNode::Ule(_, _) => 22,
        DagNode::Ugt(_, _) => 23,
        DagNode::Uge(_, _) => 24,
        DagNode::Slt(_, _) => 25,
        DagNode::Sle(_, _) => 26,
        DagNode::Sgt(_, _) => 27,
        DagNode::Sge(_, _) => 28,
        DagNode::Not(_) => 29,
        DagNode::BoolAnd(_, _) => 30,
        DagNode::BoolOr(_, _) => 31,
        DagNode::BvNot(_) => 32,
        DagNode::Neg(_) => 33,
        DagNode::Rotl(_, _) => 34,
        DagNode::Sdiv(_, _) => 35,
        DagNode::Srem(_, _) => 36,
    }
}

/// The first field of a node in constructor order (0 when absent).
fn node_f1(node: DagNode) -> usize {
    match node {
        DagNode::Var(w) => w,
        DagNode::Const(s, _) => s,
        DagNode::Add(a, _) => a,
        DagNode::Sub(a, _) => a,
        DagNode::Mul(a, _) => a,
        DagNode::Udiv(a, _) => a,
        DagNode::Urem(a, _) => a,
        DagNode::And(a, _) => a,
        DagNode::Or(a, _) => a,
        DagNode::Xor(a, _) => a,
        DagNode::Shl(a, _) => a,
        DagNode::Lshr(a, _) => a,
        DagNode::Ashr(a, _) => a,
        DagNode::Rotr(a, _) => a,
        DagNode::Extract(hi, _, _) => hi,
        DagNode::Concat(a, _) => a,
        DagNode::ZeroExt(a, _) => a,
        DagNode::SignExt(a, _) => a,
        DagNode::Ite(c, _, _) => c,
        DagNode::Eq(a, _) => a,
        DagNode::Ne(a, _) => a,
        DagNode::Ult(a, _) => a,
        DagNode::Ule(a, _) => a,
        DagNode::Ugt(a, _) => a,
        DagNode::Uge(a, _) => a,
        DagNode::Slt(a, _) => a,
        DagNode::Sle(a, _) => a,
        DagNode::Sgt(a, _) => a,
        DagNode::Sge(a, _) => a,
        DagNode::Not(a) => a,
        DagNode::BoolAnd(a, _) => a,
        DagNode::BoolOr(a, _) => a,
        DagNode::BvNot(a) => a,
        DagNode::Neg(a) => a,
        DagNode::Rotl(a, _) => a,
        DagNode::Sdiv(a, _) => a,
        DagNode::Srem(a, _) => a,
    }
}

/// The second field of a node in constructor order (0 when absent).
fn node_f2(node: DagNode) -> usize {
    match node {
        DagNode::Var(_) => 0,
        DagNode::Const(_, w) => w,
        DagNode::Add(_, b) => b,
        DagNode::Sub(_, b) => b,
        DagNode::Mul(_, b) => b,
        DagNode::Udiv(_, b) => b,
        DagNode::Urem(_, b) => b,
        DagNode::And(_, b) => b,
        DagNode::Or(_, b) => b,
        DagNode::Xor(_, b) => b,
        DagNode::Shl(_, b) => b,
        DagNode::Lshr(_, b) => b,
        DagNode::Ashr(_, b) => b,
        DagNode::Rotr(_, b) => b,
        DagNode::Extract(_, lo, _) => lo,
        DagNode::Concat(_, b) => b,
        DagNode::ZeroExt(_, by) => by,
        DagNode::SignExt(_, by) => by,
        DagNode::Ite(_, t, _) => t,
        DagNode::Eq(_, b) => b,
        DagNode::Ne(_, b) => b,
        DagNode::Ult(_, b) => b,
        DagNode::Ule(_, b) => b,
        DagNode::Ugt(_, b) => b,
        DagNode::Uge(_, b) => b,
        DagNode::Slt(_, b) => b,
        DagNode::Sle(_, b) => b,
        DagNode::Sgt(_, b) => b,
        DagNode::Sge(_, b) => b,
        DagNode::Not(_) => 0,
        DagNode::BoolAnd(_, b) => b,
        DagNode::BoolOr(_, b) => b,
        DagNode::BvNot(_) => 0,
        DagNode::Neg(_) => 0,
        DagNode::Rotl(_, b) => b,
        DagNode::Sdiv(_, b) => b,
        DagNode::Srem(_, b) => b,
    }
}

/// The third field of a node in constructor order (0 when absent).
fn node_f3(node: DagNode) -> usize {
    match node {
        DagNode::Extract(_, _, a) => a,
        DagNode::Ite(_, _, e) => e,
        _ => 0,
    }
}

/// Structural equality of two nodes: the same constructor and the same
/// fields.
fn node_eq(a: DagNode, b: DagNode) -> bool {
    node_tag(a) == node_tag(b)
        && node_f1(a) == node_f1(b)
        && node_f2(a) == node_f2(b)
        && node_f3(a) == node_f3(b)
}

/// The image of term node `a` under the map (`usize::MAX`, "no image",
/// past the end).
fn map_at(map: &[usize], a: usize) -> usize {
    if a < map.len() { map[a] } else { usize::MAX }
}

/// A term node with every operand replaced by its image under the map
/// (parameters — widths, extract bounds, extension amounts — unchanged).
fn map_node(map: &[usize], node: DagNode) -> DagNode {
    match node {
        DagNode::Var(w) => DagNode::Var(w),
        DagNode::Const(s, w) => DagNode::Const(s, w),
        DagNode::Add(a, b) => DagNode::Add(map_at(map, a), map_at(map, b)),
        DagNode::Sub(a, b) => DagNode::Sub(map_at(map, a), map_at(map, b)),
        DagNode::Mul(a, b) => DagNode::Mul(map_at(map, a), map_at(map, b)),
        DagNode::Udiv(a, b) => DagNode::Udiv(map_at(map, a), map_at(map, b)),
        DagNode::Urem(a, b) => DagNode::Urem(map_at(map, a), map_at(map, b)),
        DagNode::And(a, b) => DagNode::And(map_at(map, a), map_at(map, b)),
        DagNode::Or(a, b) => DagNode::Or(map_at(map, a), map_at(map, b)),
        DagNode::Xor(a, b) => DagNode::Xor(map_at(map, a), map_at(map, b)),
        DagNode::Shl(a, b) => DagNode::Shl(map_at(map, a), map_at(map, b)),
        DagNode::Lshr(a, b) => DagNode::Lshr(map_at(map, a), map_at(map, b)),
        DagNode::Ashr(a, b) => DagNode::Ashr(map_at(map, a), map_at(map, b)),
        DagNode::Rotr(a, b) => DagNode::Rotr(map_at(map, a), map_at(map, b)),
        DagNode::Extract(hi, lo, a) => DagNode::Extract(hi, lo, map_at(map, a)),
        DagNode::Concat(a, b) => DagNode::Concat(map_at(map, a), map_at(map, b)),
        DagNode::ZeroExt(a, by) => DagNode::ZeroExt(map_at(map, a), by),
        DagNode::SignExt(a, by) => DagNode::SignExt(map_at(map, a), by),
        DagNode::Ite(c, t, e) => DagNode::Ite(map_at(map, c), map_at(map, t), map_at(map, e)),
        DagNode::Eq(a, b) => DagNode::Eq(map_at(map, a), map_at(map, b)),
        DagNode::Ne(a, b) => DagNode::Ne(map_at(map, a), map_at(map, b)),
        DagNode::Ult(a, b) => DagNode::Ult(map_at(map, a), map_at(map, b)),
        DagNode::Ule(a, b) => DagNode::Ule(map_at(map, a), map_at(map, b)),
        DagNode::Ugt(a, b) => DagNode::Ugt(map_at(map, a), map_at(map, b)),
        DagNode::Uge(a, b) => DagNode::Uge(map_at(map, a), map_at(map, b)),
        DagNode::Slt(a, b) => DagNode::Slt(map_at(map, a), map_at(map, b)),
        DagNode::Sle(a, b) => DagNode::Sle(map_at(map, a), map_at(map, b)),
        DagNode::Sgt(a, b) => DagNode::Sgt(map_at(map, a), map_at(map, b)),
        DagNode::Sge(a, b) => DagNode::Sge(map_at(map, a), map_at(map, b)),
        DagNode::Not(a) => DagNode::Not(map_at(map, a)),
        DagNode::BoolAnd(a, b) => DagNode::BoolAnd(map_at(map, a), map_at(map, b)),
        DagNode::BoolOr(a, b) => DagNode::BoolOr(map_at(map, a), map_at(map, b)),
        DagNode::BvNot(a) => DagNode::BvNot(map_at(map, a)),
        DagNode::Neg(a) => DagNode::Neg(map_at(map, a)),
        DagNode::Rotl(a, b) => DagNode::Rotl(map_at(map, a), map_at(map, b)),
        DagNode::Sdiv(a, b) => DagNode::Sdiv(map_at(map, a), map_at(map, b)),
        DagNode::Srem(a, b) => DagNode::Srem(map_at(map, a), map_at(map, b)),
    }
}

/// A commutative operator with its operands swapped (`bvadd`, `bvmul`,
/// `bvand`, `bvor`, `bvxor`, `=`, `distinct`, boolean `and` / `or`) —
/// what canonicalization may do to a node; every other node unchanged.
fn swap_comm(node: DagNode) -> DagNode {
    match node {
        DagNode::Add(a, b) => DagNode::Add(b, a),
        DagNode::Mul(a, b) => DagNode::Mul(b, a),
        DagNode::And(a, b) => DagNode::And(b, a),
        DagNode::Or(a, b) => DagNode::Or(b, a),
        DagNode::Xor(a, b) => DagNode::Xor(b, a),
        DagNode::Eq(a, b) => DagNode::Eq(b, a),
        DagNode::Ne(a, b) => DagNode::Ne(b, a),
        DagNode::BoolAnd(a, b) => DagNode::BoolAnd(b, a),
        DagNode::BoolOr(a, b) => DagNode::BoolOr(b, a),
        _ => node,
    }
}

/// A comparison mirrored (`a < b` is `b > a`, and so on, unsigned and
/// signed) — the other rewrite canonicalization may make; every other
/// node unchanged.
fn mirror(node: DagNode) -> DagNode {
    match node {
        DagNode::Ult(a, b) => DagNode::Ugt(b, a),
        DagNode::Ule(a, b) => DagNode::Uge(b, a),
        DagNode::Ugt(a, b) => DagNode::Ult(b, a),
        DagNode::Uge(a, b) => DagNode::Ule(b, a),
        DagNode::Slt(a, b) => DagNode::Sgt(b, a),
        DagNode::Sle(a, b) => DagNode::Sge(b, a),
        DagNode::Sgt(a, b) => DagNode::Slt(b, a),
        DagNode::Sge(a, b) => DagNode::Sle(b, a),
        _ => node,
    }
}

/// Does the lowered node `d` correspond to the term operator `tn`: is it
/// `tn` over the images of its operands, or that with the operands of a
/// commutative operator swapped, or the mirror of a comparison?
fn node_corr(map: &[usize], tn: DagNode, d: DagNode) -> bool {
    let e = map_node(map, tn);
    node_eq(e, d) || node_eq(e, swap_comm(d)) || node_eq(e, mirror(d))
}

/// Is operand `a` an earlier node marked constant-valued?
fn const_at(cval: &[bool], a: usize) -> bool {
    a < cval.len() && cval[a]
}

/// The boolean value of node `c` (its word's first literal) under the
/// simulation `vals`, as `(known, value)`: `known` is false when the word
/// or the literal is out of range, and then the rules below do not fire
/// (they never guess a branch).
#[allow(clippy::len_zero)] // `is_empty` has no model in the pinned Aeneas (it became an `axiom`); `len` does
fn cond_value(vals: &[bool], words: &[Vec<Lit>], c: usize) -> (bool, bool) {
    if c < words.len() && words[c].len() > 0 {
        let l = words[c][0];
        if l.node < vals.len() {
            return (true, eval_lit(vals, l));
        }
    }
    (false, false)
}

/// Is a node's value independent of the inputs, given which earlier nodes'
/// are? A constant's is; a variable's is not; an operator's is iff its
/// operands' are — except the three the evaluator behind canonicalization
/// short-circuits: an `ite` whose condition is constant and known is iff
/// the branch that condition selects is; a boolean `and` (`or`) with a
/// constant, known operand that decides it — `false` (`true`) — is.
/// Canonicalization folds exactly such nodes even when the other branch
/// or operand reads a variable. `vals` / `words` are the proven encoder's
/// and simulator's: the values are read off them.
fn node_const(cval: &[bool], vals: &[bool], words: &[Vec<Lit>], node: DagNode) -> bool {
    match node {
        DagNode::Var(_) => false,
        DagNode::Const(_, _) => true,
        DagNode::Add(a, b) => const_at(cval, a) && const_at(cval, b),
        DagNode::Sub(a, b) => const_at(cval, a) && const_at(cval, b),
        DagNode::Mul(a, b) => const_at(cval, a) && const_at(cval, b),
        DagNode::Udiv(a, b) => const_at(cval, a) && const_at(cval, b),
        DagNode::Urem(a, b) => const_at(cval, a) && const_at(cval, b),
        DagNode::And(a, b) => const_at(cval, a) && const_at(cval, b),
        DagNode::Or(a, b) => const_at(cval, a) && const_at(cval, b),
        DagNode::Xor(a, b) => const_at(cval, a) && const_at(cval, b),
        DagNode::Shl(a, b) => const_at(cval, a) && const_at(cval, b),
        DagNode::Lshr(a, b) => const_at(cval, a) && const_at(cval, b),
        DagNode::Ashr(a, b) => const_at(cval, a) && const_at(cval, b),
        DagNode::Rotr(a, b) => const_at(cval, a) && const_at(cval, b),
        DagNode::Extract(_, _, a) => const_at(cval, a),
        DagNode::Concat(a, b) => const_at(cval, a) && const_at(cval, b),
        DagNode::ZeroExt(a, _) => const_at(cval, a),
        DagNode::SignExt(a, _) => const_at(cval, a),
        DagNode::Ite(c, t, e) => {
            let (known, cv) = cond_value(vals, words, c);
            if const_at(cval, c) && known {
                if cv {
                    const_at(cval, t)
                } else {
                    const_at(cval, e)
                }
            } else {
                false
            }
        }
        DagNode::Eq(a, b) => const_at(cval, a) && const_at(cval, b),
        DagNode::Ne(a, b) => const_at(cval, a) && const_at(cval, b),
        DagNode::Ult(a, b) => const_at(cval, a) && const_at(cval, b),
        DagNode::Ule(a, b) => const_at(cval, a) && const_at(cval, b),
        DagNode::Ugt(a, b) => const_at(cval, a) && const_at(cval, b),
        DagNode::Uge(a, b) => const_at(cval, a) && const_at(cval, b),
        DagNode::Slt(a, b) => const_at(cval, a) && const_at(cval, b),
        DagNode::Sle(a, b) => const_at(cval, a) && const_at(cval, b),
        DagNode::Sgt(a, b) => const_at(cval, a) && const_at(cval, b),
        DagNode::Sge(a, b) => const_at(cval, a) && const_at(cval, b),
        DagNode::Not(a) => const_at(cval, a),
        DagNode::BoolAnd(a, b) => {
            let (ka, va) = cond_value(vals, words, a);
            let (kb, vb) = cond_value(vals, words, b);
            (const_at(cval, a) && ka && !va)
                || (const_at(cval, b) && kb && !vb)
                || (const_at(cval, a) && const_at(cval, b))
        }
        DagNode::BoolOr(a, b) => {
            let (ka, va) = cond_value(vals, words, a);
            let (kb, vb) = cond_value(vals, words, b);
            (const_at(cval, a) && ka && va)
                || (const_at(cval, b) && kb && vb)
                || (const_at(cval, a) && const_at(cval, b))
        }
        DagNode::BvNot(a) => const_at(cval, a),
        DagNode::Neg(a) => const_at(cval, a),
        DagNode::Rotl(a, b) => const_at(cval, a) && const_at(cval, b),
        DagNode::Sdiv(a, b) => const_at(cval, a) && const_at(cval, b),
        DagNode::Srem(a, b) => const_at(cval, a) && const_at(cval, b),
    }
}

/// Which nodes of a DAG are constant-valued, in node order.
fn dag_const(ns: &[DagNode], vals: &[bool], words: &[Vec<Lit>]) -> Vec<bool> {
    let mut cval: Vec<bool> = Vec::new();
    let n = ns.len();
    let mut i = 0usize;
    while i < n {
        let node = ns[i];
        let c = node_const(&cval, vals, words, node);
        cval.push(c);
        i += 1;
    }
    cval
}

/// Are the `w` bits of `tbits` from `s0` the `w` bits of `bits` from `s1`?
/// (`false`, never a panic, when either slice is out of range.)
fn bits_eq(tbits: &[bool], s0: usize, bits: &[bool], s1: usize, w: usize) -> bool {
    if s0 > tbits.len() || w > tbits.len() - s0 || s1 > bits.len() || w > bits.len() - s1 {
        return false;
    }
    let mut j = 0usize;
    while j < w {
        if tbits[s0 + j] != bits[s1 + j] {
            return false;
        }
        j += 1;
    }
    true
}

/// Are the `w` literals of `word`, under the simulation `vals`, the `w`
/// bits of `bits` from `s1`? (`false`, never a panic, out of range.)
fn fold_bits_ok(vals: &[bool], word: &[Lit], bits: &[bool], s1: usize, w: usize) -> bool {
    if word.len() != w || s1 > bits.len() || w > bits.len() - s1 {
        return false;
    }
    let mut j = 0usize;
    while j < w {
        let l = word[j];
        if l.node >= vals.len() {
            return false;
        }
        if eval_lit(vals, l) != bits[s1 + j] {
            return false;
        }
        j += 1;
    }
    true
}

/// Term node `i` against its image `mi` (`mi < ns.len()`): the two must
/// correspond node for node — a variable to a fresh variable of its width,
/// a constant to the same constant, an operator to the same operator over
/// the images of its operands up to a commutative swap or a comparison
/// mirror — or the node is a constant-valued operator whose image is a
/// constant of its width and of its value: a FOLD, the value coming from
/// the proven encoder and simulator (`vals`, `words`, all inputs false —
/// a constant-valued node reads none of them). `seen` marks the DAG
/// variables already used as an image.
#[allow(clippy::too_many_arguments)] // the fragment has no structs to bundle them
fn term_node_corr(
    t: &[DagNode],
    tbits: &[bool],
    ws0: &[usize],
    cval: &[bool],
    map: &[usize],
    ns: &[DagNode],
    bits: &[bool],
    vals: &[bool],
    words: &[Vec<Lit>],
    seen: &mut [bool],
    i: usize,
    mi: usize,
) -> Result<(), TermError> {
    let tn = t[i];
    let d = ns[mi];
    let tt = node_tag(tn);
    let td = node_tag(d);
    if tt == 0 {
        // A variable: its image is an unused variable of the same width.
        if td != 0 || node_f1(tn) != node_f1(d) || seen[mi] {
            return Err(TermError::VarMismatch { node: i });
        }
        seen[mi] = true;
        return Ok(());
    }
    if tt == 1 {
        // A constant: its image is the same constant (same width and bits).
        if td != 1
            || node_f2(tn) != node_f2(d)
            || !bits_eq(tbits, node_f1(tn), bits, node_f1(d), node_f2(tn))
        {
            return Err(TermError::ConstMismatch { node: i });
        }
        return Ok(());
    }
    if td == 1 {
        // An operator folded to a constant: constant-valued, same width,
        // same bits as its simulated word.
        if !cval[i]
            || ws0[i] != node_f2(d)
            || !fold_bits_ok(vals, &words[i], bits, node_f1(d), node_f2(d))
        {
            return Err(TermError::FoldMismatch { node: i });
        }
        return Ok(());
    }
    if node_corr(map, tn, d) {
        Ok(())
    } else {
        Err(TermError::NodeMismatch { node: i })
    }
}

/// One term node of the main loop of [`check_term_dag`]: nothing to check
/// when node `i` has no image; otherwise the image must be a DAG node
/// (`n1` is the DAG's length) and [`term_node_corr`] decides.
#[allow(clippy::too_many_arguments)] // the fragment has no structs to bundle them
fn term_step(
    t: &[DagNode],
    tbits: &[bool],
    ws0: &[usize],
    cval: &[bool],
    map: &[usize],
    ns: &[DagNode],
    bits: &[bool],
    vals: &[bool],
    words: &[Vec<Lit>],
    seen: &mut [bool],
    i: usize,
    n1: usize,
) -> Result<(), TermError> {
    let mi = map[i];
    if mi == usize::MAX {
        return Ok(());
    }
    if mi >= n1 {
        return Err(TermError::MapOutOfRange { node: i });
    }
    term_node_corr(t, tbits, ws0, cval, map, ns, bits, vals, words, seen, i, mi)
}

/// Do the asserted roots correspond one for one: as many, and each term
/// root's image is the DAG root?
#[allow(clippy::if_same_then_else)] // two tests, two reasons; one `||` would change the model's shape
fn roots_corr(troots: &[usize], map: &[usize], roots: &[usize]) -> bool {
    let m = troots.len();
    if m != roots.len() {
        return false;
    }
    // The loop carries its verdict in `ok` (the pinned Charon rejects
    // more than two early returns from one loop body).
    let mut ok = true;
    let mut k = 0usize;
    while ok && k < m {
        let r = troots[k];
        if r < map.len() {
            let image = map[r];
            let rk = roots[k];
            if image == usize::MAX {
                ok = false;
            } else if image != rk {
                ok = false;
            }
        } else {
            ok = false;
        }
        k += 1;
    }
    ok
}

/// **The term-to-DAG correspondence check** (issue #192 phase 7,
/// `ordeal-cert/v3`): is the lowered DAG `ns` (constants `bits`, roots
/// `roots`) — the DAG [`check_query`] refutes or [`check_query_model`]
/// evaluates — a semantics-preserving rewrite of the TERM `t` (constants
/// `tbits`, roots `troots`: the caller's assertions flattened as they
/// were asked, variables shared by name and nothing else), along the
/// untrusted index map `map` (term node → DAG node, `usize::MAX` for a
/// node that has no image)?
///
/// Every mapped term node must correspond to its image: a variable to an
/// unused variable of its width (the map is injective on variables), a
/// constant to the same constant, an operator to the same operator over
/// its operands' images — up to the two rewrites canonicalization makes,
/// a commutative swap and a comparison mirror — or, when the operator's
/// value does not depend on the inputs (its cone reads no variable, or
/// only in the branch of an `ite` that a constant condition does not
/// select), to a constant of its width that is its value, as the proven
/// encoder and simulator compute it. The roots correspond one for one.
///
/// > If `check_term_dag(t, tbits, troots, map, ns, bits, roots)` returns
/// > `Ok(())`, then under any pair of input assignments that agree on the
/// > variables (through the map), every term root has the value of its
/// > DAG root; both directions of transport exist, so a refutation of the
/// > DAG refutes the term and a model of the DAG is a model of the term.
///
/// Machine-checked as `kernel.spec.check_term_dag_sound`,
/// `check_term_unsat_sound`, `check_term_model_sound` and
/// `term_verdicts_exclusive` (`lean/TermCheck.lean`), composed with
/// `check_query_sound` / `check_query_model_sound`, whose statements are
/// unchanged. The map is untrusted advice: a wrong one is rejected, never
/// accepted on a different formula.
pub fn check_term_dag(
    t: &[DagNode],
    tbits: &[bool],
    troots: &[usize],
    map: &[usize],
    ns: &[DagNode],
    bits: &[bool],
    roots: &[usize],
) -> Result<(), TermError> {
    let ws0 = match dag_wf(t, tbits.len()) {
        Ok(ws) => ws,
        Err(e) => return Err(TermError::Term(e)),
    };
    let ws1 = match dag_wf(ns, bits.len()) {
        Ok(ws) => ws,
        Err(e) => return Err(TermError::Query(e)),
    };
    let n0 = t.len();
    let n1 = ns.len();
    if map.len() != n0 {
        return Err(TermError::MapLength {
            expected: n0,
            found: map.len(),
        });
    }
    // The term, encoded by the proven `encode` and simulated by the proven
    // `simulate` under the all-false assignment: the evaluator the folds
    // are checked with (a constant-valued node reads no input), and the
    // source of the `ite` conditions' values for `dag_const`. No
    // evaluator of its own.
    let wmax = max_width(&ws0);
    if !encode_fits(wmax, n0) {
        return Err(TermError::Term(QueryError::TooLarge));
    }
    let nin = match dag_nin(t) {
        Ok(n) => n,
        Err(_) => return Err(TermError::Term(QueryError::TooLarge)),
    };
    let mut inp: Vec<bool> = Vec::new();
    let mut k = 0usize;
    while k < nin {
        inp.push(false);
        k += 1;
    }
    let no_roots: Vec<usize> = Vec::new();
    let mut raw = aig_new();
    let (words, _outs) = encode(&mut raw, t, tbits, &no_roots);
    let vals = simulate(&raw, &inp);
    let cval = dag_const(t, &vals, &words);
    let mut seen: Vec<bool> = Vec::new();
    let mut k1 = 0usize;
    while k1 < n1 {
        seen.push(false);
        k1 += 1;
    }
    // The loop carries its outcome in `failure` instead of returning early
    // from a `match` arm (the Aeneas constraint `check_steps` documents).
    let mut failure: Option<TermError> = None;
    let mut i = 0usize;
    while failure.is_none() && i < n0 {
        match term_step(
            t, tbits, &ws0, &cval, map, ns, bits, &vals, &words, &mut seen, i, n1,
        ) {
            Ok(()) => {}
            Err(e) => failure = Some(e),
        }
        i += 1;
    }
    if let Some(e) = failure {
        return Err(e);
    }
    if !roots_corr(troots, map, roots) {
        return Err(TermError::RootMismatch);
    }
    // `ws1` is read for its well-formedness verdict only (a malformed
    // lowered DAG is rejected above); its widths enter the proof through
    // `dag_wf_spec`.
    let _ = ws1;
    Ok(())
}

// ───────────── The model binding at the DAG level (issue #192 phase 7d) ─────────────

/// The primary-input offset of DAG node `node`: the `Var` widths of the
/// nodes BEFORE it summed (`dagNin` of the prefix) — where that node's
/// bits start in the input assignment `check_query_model` evaluates.
/// `Err(TooLarge)` on a `usize` overflow of the sum, or when `node` is
/// past the end.
pub fn var_offset(ns: &[DagNode], node: usize) -> Result<usize, ModelError> {
    if node > ns.len() {
        return Err(ModelError::Query(QueryError::TooLarge));
    }
    let mut nin = 0usize;
    let mut i = 0usize;
    while i < node {
        let nd = ns[i];
        if let DagNode::Var(w) = nd {
            if w > usize::MAX - nin {
                return Err(ModelError::Query(QueryError::TooLarge));
            }
            nin += w;
        }
        i += 1;
    }
    Ok(nin)
}

/// Is the `w`-bit value `value` (`w ≤ 128`) the bits `inp[offset .. offset
/// + w]`, LSB first — the proven reading of a model binding off the DAG's
/// input assignment (`check_binding`'s twin at the DAG level, #192 phase
/// 7d). `false`, never a panic, out of range. Machine-checked as
/// `kernel.spec.check_input_value_sound`: `true` ⟹ for every `j < w`,
/// `inp[offset + j]` is bit `j` of `value`.
pub fn check_input_value(inp: &[bool], offset: usize, w: usize, value: u128) -> bool {
    if w > 128 || offset > inp.len() || w > inp.len() - offset {
        return false;
    }
    let mut j = 0usize;
    while j < w {
        let bit = (value >> j) & 1;
        let b = inp[offset + j];
        if b {
            if bit != 1 {
                return false;
            }
        } else if bit != 0 {
            return false;
        }
        j += 1;
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    fn add(id: usize, clause: &[i32], hints: &[usize]) -> Step {
        Step::Add {
            id,
            clause: clause.to_vec(),
            hints: hints.to_vec(),
        }
    }

    #[test]
    fn empty_clause_from_two_units_is_accepted() {
        let cnf = vec![vec![1], vec![-1]];
        assert_eq!(check_steps(&cnf, &[add(3, &[], &[1, 2])]), Ok(()));
    }

    #[test]
    fn rejects_without_empty_clause() {
        let cnf = vec![vec![1, 2], vec![-1, 2]];
        // Deriving [2] is fine, but no empty clause ⇒ reject.
        let steps = [add(3, &[2], &[1, 2])];
        assert_eq!(check_steps(&cnf, &steps), Err(CoreError::NoEmptyClause));
    }

    #[test]
    fn rejects_non_sequential_and_dead_ids() {
        let cnf = vec![vec![1], vec![-1]];
        assert!(matches!(
            check_steps(&cnf, &[add(5, &[], &[1, 2])]),
            Err(CoreError::NonSequentialId { .. })
        ));
        let steps = [
            Step::Delete { ids: vec![1] },
            add(3, &[], &[1, 2]), // hint 1 is dead
        ];
        assert!(matches!(
            check_steps(&cnf, &steps),
            Err(CoreError::DeletedId { step: 1, id: 1 })
        ));
    }

    #[test]
    fn rejects_invalid_step_literals() {
        let cnf = vec![vec![1], vec![-1]];
        for bad in [0i32, i32::MIN] {
            assert!(matches!(
                check_steps(&cnf, &[add(3, &[bad], &[1, 2])]),
                Err(CoreError::InvalidStepLiteral { step: 0 })
            ));
        }
    }

    #[test]
    fn check_sat_accepts_a_satisfying_assignment() {
        // (1 ∨ 2) ∧ (¬1 ∨ 2) ∧ (¬2 ∨ 1) — satisfied by 1=true, 2=true.
        let cnf = vec![vec![1, 2], vec![-1, 2], vec![-2, 1]];
        assert_eq!(check_sat(&cnf, &[true, true]), Ok(()));
    }

    #[test]
    fn check_sat_rejects_an_unsatisfied_clause() {
        let cnf = vec![vec![1, 2], vec![-1, -2]];
        assert!(matches!(
            check_sat(&cnf, &[true, true]),
            Err(SatWitnessError::UnsatisfiedClause { clause_index: 1 })
        ));
    }

    #[test]
    fn check_sat_rejects_short_assignments_and_bad_literals() {
        // The out-of-range variable must actually be reached: a clause
        // already satisfied by an earlier in-range literal is accepted
        // lazily (sound — satisfaction is established without it).
        assert!(matches!(
            check_sat(&[vec![3]], &[true]),
            Err(SatWitnessError::AssignmentTooShort { var: 3 })
        ));
        assert_eq!(check_sat(&[vec![1, 3]], &[true]), Ok(()));
        for bad in [0i32, i32::MIN] {
            assert!(matches!(
                check_sat(&[vec![bad]], &[true]),
                Err(SatWitnessError::InvalidCnfLiteral { clause_index: 0 })
            ));
        }
    }

    #[test]
    fn check_binding_verifies_and_rejects() {
        // Literals 1..=4 = bits of value 0b1010 (LSB-first): 1=false,
        // 2=true, 3=false, 4=true.
        let assignment = [false, true, false, true];
        assert_eq!(check_binding(&assignment, &[1, 2, 3, 4], 0b1010), Ok(()));
        // Negated literal: bit reads the variable's complement.
        assert_eq!(check_binding(&assignment, &[-1, -2], 0b01), Ok(()));
        assert!(matches!(
            check_binding(&assignment, &[1, 2, 3, 4], 0b1011),
            Err(SatWitnessError::BindingMismatch { bit: 0 })
        ));
        assert!(matches!(
            check_binding(&assignment, &[9], 0),
            Err(SatWitnessError::AssignmentTooShort { var: 9 })
        ));
        assert!(matches!(
            check_binding(&assignment, &[0], 0),
            Err(SatWitnessError::InvalidCnfLiteral { .. })
        ));
    }

    // ── #192 phase 4: the query re-check ────────────────────────────────

    use super::blast_kernel::DagNode as N;

    /// `x : BV1`, `x = 1`, `¬(x = 1)`: a well-formed two-root DAG.
    fn tiny_dag() -> (Vec<N>, Vec<bool>, Vec<usize>) {
        (
            vec![N::Var(1), N::Const(0, 1), N::Eq(0, 1), N::Not(2)],
            vec![true],
            vec![2, 3],
        )
    }

    #[test]
    fn check_query_dag_wf_accepts_well_formed_dags_with_their_widths() {
        let (ns, bits, _) = tiny_dag();
        assert_eq!(dag_wf(&ns, bits.len()), Ok(vec![1, 1, 1, 1]));
        let ns = vec![
            N::Var(8),
            N::Const(0, 8),
            N::Add(0, 1),
            N::Extract(7, 4, 2),
            N::Concat(3, 0),
            N::ZeroExt(3, 3),
            N::SignExt(4, 1),
            N::Ult(0, 1),
            N::Ite(7, 0, 1),
            N::BoolAnd(7, 7),
        ];
        assert_eq!(dag_wf(&ns, 8), Ok(vec![8, 8, 8, 4, 12, 7, 13, 1, 8, 1]));
        // #192 phase 5: the derived-op nodes are word operators like the
        // ones they used to be rewritten into.
        let ns = vec![
            N::Var(12),
            N::Var(12),
            N::BvNot(0),
            N::Neg(1),
            N::Rotl(0, 1),
            N::Sdiv(2, 3),
            N::Srem(4, 5),
            N::Eq(5, 6),
        ];
        assert_eq!(dag_wf(&ns, 0), Ok(vec![12, 12, 12, 12, 12, 12, 12, 1]));
        assert_eq!(roots_wf(&[8, 1, 1], &[1, 2]), Ok(()));
        assert_eq!(max_width(&[3, 9, 2]), 9);
        assert_eq!(max_width(&[]), 0);
    }

    #[test]
    fn check_query_dag_wf_rejects_each_malformation_at_its_node() {
        let bad = |ns: Vec<N>, nbits: usize, node: usize| {
            assert_eq!(
                dag_wf(&ns, nbits),
                Err(QueryError::NodeNotWellFormed { node }),
                "{node}"
            );
        };
        bad(vec![N::Var(0)], 0, 0); // zero width
        bad(vec![N::Const(0, 2)], 1, 0); // constant slice past the table
        bad(vec![N::Var(8), N::Add(0, 1)], 0, 1); // operand not earlier
        bad(vec![N::Var(8), N::Var(4), N::Add(0, 1)], 0, 2); // widths disagree
        bad(vec![N::Var(8), N::Extract(8, 0, 0)], 0, 1); // hi past the width
        bad(vec![N::Var(8), N::Extract(2, 3, 0)], 0, 1); // lo > hi
        bad(vec![N::Var(8), N::Ite(0, 0, 0)], 0, 1); // condition not boolean
        bad(vec![N::Var(8), N::Not(0)], 0, 1); // Not of a word
        bad(vec![N::Var(8), N::ZeroExt(0, usize::MAX)], 0, 1); // width overflow
        bad(vec![N::Var(usize::MAX), N::Concat(0, 0)], 0, 1); // width overflow
        // #192 phase 5: the derived-op nodes under the same discipline.
        bad(vec![N::Var(8), N::Neg(1)], 0, 1); // operand not earlier
        bad(vec![N::Var(8), N::BvNot(2)], 0, 1); // operand not earlier
        bad(vec![N::Var(8), N::Var(4), N::Sdiv(0, 1)], 0, 2); // widths disagree
        bad(vec![N::Var(8), N::Var(4), N::Srem(1, 0)], 0, 2); // widths disagree
        bad(vec![N::Var(8), N::Rotl(0, 1)], 0, 1); // amount not earlier
        assert_eq!(
            roots_wf(&[8, 1], &[1, 0]),
            Err(QueryError::BadRoot { root: 1 })
        );
        assert_eq!(
            roots_wf(&[8, 1], &[2]),
            Err(QueryError::BadRoot { root: 0 })
        );
    }

    #[test]
    fn check_query_capacity_checks_match_their_formulas() {
        // gateBound(W) = 70 W² + 70 W + 1; 1 + n · gateBound(W) ≤ usize::MAX.
        assert!(encode_fits(0, 0));
        assert!(encode_fits(128, 1 << 20));
        assert!(encode_fits(0, usize::MAX - 1));
        assert!(!encode_fits(0, usize::MAX)); // 1 + MAX overflows
        assert!(!encode_fits(usize::MAX / 1000, 1));
        assert!(!encode_fits(1 << 16, usize::MAX / 1000));
        // The exact edge: 1 + n · (70·w² + 70·w + 1) ≤ MAX at w = 1 (budget 141).
        assert!(encode_fits(1, (usize::MAX - 1) / 141));
        assert!(!encode_fits(1, (usize::MAX - 1) / 141 + 1));
        // 1 + 3 · nodes + outs < usize::MAX.
        assert!(tseitin_fits(0, 0));
        assert!(tseitin_fits((usize::MAX - 2) / 3, 0));
        assert!(!tseitin_fits((usize::MAX - 2) / 3 + 1, 0));
        assert!(!tseitin_fits(0, usize::MAX - 1));
        assert!(tseitin_fits(0, usize::MAX - 2));
    }

    #[test]
    fn check_query_rejects_before_encoding_and_without_a_refutation() {
        let (ns, bits, roots) = tiny_dag();
        let hints: Vec<usize> = Vec::new();
        // No steps: the re-encoded CNF is not refuted.
        assert_eq!(
            check_query(&ns, &bits, &roots, &hints, &[]),
            Err(QueryError::Check(CoreError::NoEmptyClause))
        );
        // A malformed DAG never reaches the encoder.
        let mut bad = ns.clone();
        bad[2] = N::Eq(0, 9);
        assert_eq!(
            check_query(&bad, &bits, &roots, &hints, &[]),
            Err(QueryError::NodeNotWellFormed { node: 2 })
        );
        // A root that is a word, not a boolean (the tiny DAG's `Var(1)`
        // IS boolean, so an 8-bit variable is used here).
        assert_eq!(
            check_query(&[N::Var(8)], &[], &[0], &hints, &[]),
            Err(QueryError::BadRoot { root: 0 })
        );
        // A constant table too short for the Const node.
        assert_eq!(
            check_query(&ns, &[], &roots, &hints, &[]),
            Err(QueryError::NodeNotWellFormed { node: 1 })
        );
    }

    /// The tiny DAG's CNF, refuted by hand: `x = 1` is `x` (node 1 is the
    /// input, node 2 the AND `1 & x` folded to `x` by `compact`), so the
    /// roots are the literals `x` and `¬x` — two contradictory unit
    /// clauses after the constant clause `[-1]`.
    #[test]
    fn check_query_accepts_a_hand_refuted_query() {
        let (ns, bits, roots) = tiny_dag();
        // Hints are advice: an empty list means "share nothing".
        let cnf = check_query(&ns, &bits, &roots, &[], &[add(4, &[], &[2, 3])])
            .expect("the hand-written refutation is accepted");
        assert_eq!(cnf, vec![vec![-1], vec![2], vec![-2]]);
        // The same steps against a different root polarity: not a refutation.
        assert!(matches!(
            check_query(&ns, &bits, &[2, 2], &[], &[add(4, &[], &[2, 3])]),
            Err(QueryError::Check(_))
        ));
    }

    // ── #192 phase 6: the model re-check ────────────────────────────────

    // rivet: verifies VER-065
    /// The tiny DAG (`x : BV1`, node 2 = `x = 1`, node 3 = `¬(x = 1)`): the
    /// assignment `x = 1` satisfies root 2 and falsifies root 3, `x = 0`
    /// the other way round, and no assignment satisfies both — the pair
    /// `check_query` refutes.
    #[test]
    fn check_query_model_accepts_a_witness_and_rejects_a_falsified_root() {
        let (ns, bits, _) = tiny_dag();
        assert_eq!(dag_nin(&ns), Ok(1));
        assert_eq!(check_query_model(&ns, &bits, &[2], &[true]), Ok(()));
        assert_eq!(
            check_query_model(&ns, &bits, &[3], &[true]),
            Err(ModelError::RootFalse { root: 0 })
        );
        assert_eq!(check_query_model(&ns, &bits, &[3], &[false]), Ok(()));
        assert_eq!(
            check_query_model(&ns, &bits, &[2], &[false]),
            Err(ModelError::RootFalse { root: 0 })
        );
        assert_eq!(
            check_query_model(&ns, &bits, &[2, 3], &[true]),
            Err(ModelError::RootFalse { root: 1 })
        );
        assert_eq!(
            check_query_model(&ns, &bits, &[2, 3], &[false]),
            Err(ModelError::RootFalse { root: 0 })
        );
        // Surplus input bits are never read; no roots is vacuously true.
        assert_eq!(
            check_query_model(&ns, &bits, &[2], &[true, false, true]),
            Ok(())
        );
        assert_eq!(check_query_model(&ns, &bits, &[], &[true]), Ok(()));
    }

    // rivet: verifies VER-065
    /// Inputs are read in node order, LSB first within a variable (the
    /// `dagSim` convention): `a + b = 7 ∧ a < b` at width 4 with `a = 3`,
    /// `b = 4`; swapping the values keeps the sum but fails `a < b`; one
    /// flipped input bit (`a = 2`) fails the sum.
    #[test]
    fn check_query_model_reads_inputs_in_node_order_lsb_first() {
        let ns = vec![
            N::Var(4),
            N::Var(4),
            N::Add(0, 1),
            N::Const(0, 4),
            N::Eq(2, 3),
            N::Ult(0, 1),
        ];
        let bits = vec![true, true, true, false]; // 7, LSB first
        assert_eq!(dag_nin(&ns), Ok(8));
        let inp = [true, true, false, false, false, false, true, false];
        assert_eq!(check_query_model(&ns, &bits, &[4, 5], &inp), Ok(()));
        let swapped = [false, false, true, false, true, true, false, false];
        assert_eq!(
            check_query_model(&ns, &bits, &[4, 5], &swapped),
            Err(ModelError::RootFalse { root: 1 })
        );
        let mut tampered = inp;
        tampered[0] = false;
        assert_eq!(
            check_query_model(&ns, &bits, &[4, 5], &tampered),
            Err(ModelError::RootFalse { root: 0 })
        );
    }

    // rivet: verifies VER-065
    /// Malformed input fails closed before anything is evaluated: a short
    /// assignment is rejected (never padded), a malformed DAG, a word root
    /// and a short constant table are the `check_query` rejections, and an
    /// input count past `usize::MAX` is `TooLarge`, not a wrap.
    #[test]
    fn check_query_model_fails_closed_on_malformed_input() {
        let (ns, bits, roots) = tiny_dag();
        assert_eq!(
            check_query_model(&ns, &bits, &roots, &[]),
            Err(ModelError::ModelTooShort {
                needed: 1,
                given: 0
            })
        );
        let mut bad = ns.clone();
        bad[2] = N::Eq(0, 9);
        assert_eq!(
            check_query_model(&bad, &bits, &[2], &[true]),
            Err(ModelError::Query(QueryError::NodeNotWellFormed { node: 2 }))
        );
        assert_eq!(
            check_query_model(&[N::Var(8)], &[], &[0], &[true; 8]),
            Err(ModelError::Query(QueryError::BadRoot { root: 0 }))
        );
        assert_eq!(
            check_query_model(&ns, &[], &[2], &[true]),
            Err(ModelError::Query(QueryError::NodeNotWellFormed { node: 1 }))
        );
        assert_eq!(
            dag_nin(&[N::Var(usize::MAX), N::Var(1)]),
            Err(ModelError::Query(QueryError::TooLarge))
        );
        // Through the entry point the capacity check fires first.
        assert_eq!(
            check_query_model(&[N::Var(usize::MAX), N::Var(1)], &[], &[], &[]),
            Err(ModelError::Query(QueryError::TooLarge))
        );
    }

    #[test]
    fn rejects_exhausted_and_non_unit_hints() {
        let cnf = vec![vec![1, 2], vec![-1, 2], vec![-2, 1]];
        // Hints run out before a conflict.
        assert!(matches!(
            check_steps(&cnf, &[add(4, &[], &[1])]),
            Err(CoreError::HintNotUnit { .. }) | Err(CoreError::HintsExhausted { .. })
        ));
    }

    // ── The term-to-DAG correspondence check (#192 phase 7) ─────────────

    /// A `w`-bit constant table entry, LSB first.
    fn cbits(v: u128, w: usize) -> Vec<bool> {
        (0..w).map(|j| (v >> j) & 1 == 1).collect()
    }

    /// The term `y + x > 2 * 3`, `x = y` over 8-bit `x`, `y`, as flattened
    /// (no canon, no sharing beyond the variables), and the DAG the solver
    /// lowers it to: the sum's operands ordered, the product folded to the
    /// constant 6, the comparison mirrored to `6 < x + y`.
    type Pair = (
        Vec<DagNode>,
        Vec<bool>,
        Vec<usize>,
        Vec<usize>,
        Vec<DagNode>,
        Vec<bool>,
        Vec<usize>,
    );
    fn term_and_dag() -> Pair {
        use DagNode as N;
        let t = vec![
            N::Var(8),      // 0: x
            N::Var(8),      // 1: y
            N::Add(1, 0),   // 2: y + x
            N::Const(0, 8), // 3: 2
            N::Const(8, 8), // 4: 3
            N::Mul(3, 4),   // 5: 2 * 3  (closed)
            N::Ugt(2, 5),   // 6: y + x > 2 * 3
            N::Eq(0, 1),    // 7: x = y
        ];
        let mut tbits = cbits(2, 8);
        tbits.extend(cbits(3, 8));
        let troots = vec![6, 7];
        let ns = vec![
            N::Var(8),      // 0: x
            N::Var(8),      // 1: y
            N::Add(0, 1),   // 2: x + y   (swapped)
            N::Const(0, 8), // 3: 6       (the fold)
            N::Ult(3, 2),   // 4: 6 < x + y (mirrored)
            N::Eq(0, 1),    // 5: x = y
        ];
        let bits = cbits(6, 8);
        let roots = vec![4, 5];
        let none = usize::MAX;
        let map = vec![0, 1, 2, none, none, 3, 4, 5];
        (t, tbits, troots, map, ns, bits, roots)
    }

    // rivet: verifies VER-069
    /// The positive control: a swap, a mirror, a fold and two shared
    /// variables are all accepted, and the hand-written map is the one the
    /// solver's pipeline would produce.
    #[test]
    fn check_term_dag_accepts_swap_mirror_fold_and_shared_vars() {
        let (t, tbits, troots, map, ns, bits, roots) = term_and_dag();
        assert_eq!(
            check_term_dag(&t, &tbits, &troots, &map, &ns, &bits, &roots),
            Ok(())
        );
    }

    // rivet: verifies VER-069
    /// One negative control per risk: two term variables aliased to one DAG
    /// variable, a wrong fold value, a non-commutative operator swapped, a
    /// wrong mirror, a tampered map entry, a root that does not correspond.
    #[test]
    fn check_term_dag_rejects_each_unsound_rewrite() {
        use DagNode as N;
        let none = usize::MAX;
        // Aliasing: x and y both mapped to the DAG's y.
        let (t, tbits, troots, mut map, ns, bits, roots) = term_and_dag();
        map[0] = 1;
        assert_eq!(
            check_term_dag(&t, &tbits, &troots, &map, &ns, &bits, &roots),
            Err(TermError::VarMismatch { node: 1 })
        );
        // A wrong fold: the constant says 7, the product is 6.
        let (t, tbits, troots, map, ns, _, roots) = term_and_dag();
        let bits7 = cbits(7, 8);
        assert_eq!(
            check_term_dag(&t, &tbits, &troots, &map, &ns, &bits7, &roots),
            Err(TermError::FoldMismatch { node: 5 })
        );
        // A fold of an OPEN node: `x * 3` mapped to a constant.
        let (mut t, tbits, troots, map, ns, bits, roots) = term_and_dag();
        t[5] = N::Mul(0, 4);
        assert_eq!(
            check_term_dag(&t, &tbits, &troots, &map, &ns, &bits, &roots),
            Err(TermError::FoldMismatch { node: 5 })
        );
        // A fold of an open node whose value at the ALL-FALSE assignment
        // happens to equal the constant (`x * 3` is 0 there; the DAG says
        // 0): only the constant-valuedness check rejects it, not the bit
        // comparison — the control for the fold rule itself.
        let (mut t, tbits, troots, map, ns, _, roots) = term_and_dag();
        t[5] = N::Mul(0, 4);
        let bits0 = cbits(0, 8);
        assert_eq!(
            check_term_dag(&t, &tbits, &troots, &map, &ns, &bits0, &roots),
            Err(TermError::FoldMismatch { node: 5 }),
            "an open node is never a fold, even when the all-false value matches"
        );
        // An `ite` with a constant condition is constant-valued through
        // the branch the condition selects, even if the other branch
        // reads a variable — canonicalization folds exactly those: `ite(2
        // < 3, 6, x)` is 6 (accepted), `ite(3 < 2, 6, x)` is `x` (not).
        let (_, tbits, _, _, ns, bits, roots) = term_and_dag();
        let t2 = vec![
            N::Var(8),       // 0: x
            N::Var(8),       // 1: y
            N::Add(1, 0),    // 2: y + x
            N::Const(0, 8),  // 3: 2
            N::Const(8, 8),  // 4: 3
            N::Ult(3, 4),    // 5: 2 < 3 (true)
            N::Const(16, 8), // 6: 6
            N::Ite(5, 6, 0), // 7: ite(2 < 3, 6, x) — constant-valued, reads x in the dead branch
            N::Ugt(2, 7),    // 8: y + x > ite(...)
            N::Eq(0, 1),     // 9: x = y
        ];
        let mut tbits2 = tbits.clone();
        tbits2.extend(cbits(6, 8));
        let troots2 = vec![8, 9];
        let map2 = vec![0, 1, 2, none, none, none, none, 3, 4, 5];
        assert_eq!(
            check_term_dag(&t2, &tbits2, &troots2, &map2, &ns, &bits, &roots),
            Ok(()),
            "an ite with a constant condition and a constant selected branch folds"
        );
        let mut t3 = t2.clone();
        t3[5] = N::Ult(4, 3); // 3 < 2 (false): the selected branch is x
        assert_eq!(
            check_term_dag(&t3, &tbits2, &troots2, &map2, &ns, &bits, &roots),
            Err(TermError::FoldMismatch { node: 7 }),
            "an ite whose selected branch reads a variable is not constant-valued"
        );
        // A non-commutative swap: y - x against x - y.
        let (mut t, tbits, troots, map, mut ns, bits, roots) = term_and_dag();
        t[2] = N::Sub(1, 0);
        ns[2] = N::Sub(0, 1);
        assert_eq!(
            check_term_dag(&t, &tbits, &troots, &map, &ns, &bits, &roots),
            Err(TermError::NodeMismatch { node: 2 })
        );
        // The same without the swap is fine.
        ns[2] = N::Sub(1, 0);
        assert_eq!(
            check_term_dag(&t, &tbits, &troots, &map, &ns, &bits, &roots),
            Ok(())
        );
        // A wrong mirror: `>` against `<=` with the operands swapped.
        let (t, tbits, troots, map, mut ns, bits, roots) = term_and_dag();
        ns[4] = N::Ule(3, 2);
        assert_eq!(
            check_term_dag(&t, &tbits, &troots, &map, &ns, &bits, &roots),
            Err(TermError::NodeMismatch { node: 6 })
        );
        // A tampered map entry: `x = y` pointed at the comparison.
        let (t, tbits, troots, mut map, ns, bits, roots) = term_and_dag();
        map[7] = 4;
        assert_eq!(
            check_term_dag(&t, &tbits, &troots, &map, &ns, &bits, &roots),
            Err(TermError::NodeMismatch { node: 7 })
        );
        // A root with no image, a map of the wrong length, an image past
        // the end.
        let (t, tbits, troots, mut map, ns, bits, roots) = term_and_dag();
        map[6] = none;
        assert_eq!(
            check_term_dag(&t, &tbits, &troots, &map, &ns, &bits, &roots),
            Err(TermError::RootMismatch)
        );
        let (t, tbits, troots, map, ns, bits, roots) = term_and_dag();
        assert!(matches!(
            check_term_dag(&t, &tbits, &troots, &map[..7], &ns, &bits, &roots),
            Err(TermError::MapLength {
                expected: 8,
                found: 7
            })
        ));
        let mut far = map.clone();
        far[2] = 99;
        assert_eq!(
            check_term_dag(&t, &tbits, &troots, &far, &ns, &bits, &roots),
            Err(TermError::MapOutOfRange { node: 2 })
        );
        // A constant whose image has other bits.
        let (mut t, mut tbits, troots, mut map, ns, bits, roots) = term_and_dag();
        t.push(N::Const(16, 8));
        tbits.extend(cbits(5, 8));
        map.push(3);
        assert_eq!(
            check_term_dag(&t, &tbits, &troots, &map, &ns, &bits, &roots),
            Err(TermError::ConstMismatch { node: 8 })
        );
    }

    // rivet: verifies VER-069
    /// The model binding at the DAG level (7d): the offset is the `Var`
    /// widths before the node, and a value is accepted iff its bits are the
    /// inputs at that offset, LSB first.
    #[test]
    fn var_offset_and_check_input_value_read_the_inputs_lsb_first() {
        use DagNode as N;
        let ns = vec![N::Var(3), N::Const(0, 2), N::Var(5), N::Add(0, 0)];
        assert_eq!(var_offset(&ns, 0), Ok(0));
        assert_eq!(var_offset(&ns, 2), Ok(3));
        assert_eq!(var_offset(&ns, 4), Ok(8));
        assert!(var_offset(&ns, 5).is_err());
        // inputs: x = 0b101 (bits 1,0,1), y = 0b10110 (bits 0,1,1,0,1).
        let inp = [true, false, true, false, true, true, false, true];
        assert!(check_input_value(&inp, 0, 3, 0b101));
        assert!(check_input_value(&inp, 3, 5, 0b10110));
        assert!(!check_input_value(&inp, 3, 5, 0b10111));
        assert!(!check_input_value(&inp, 0, 3, 0b100));
        // Out of range, never a panic.
        assert!(!check_input_value(&inp, 3, 6, 0));
        assert!(!check_input_value(&inp, 9, 0, 0));
        assert!(!check_input_value(&inp, 0, 129, 0));
        assert!(check_input_value(&inp, 8, 0, 0));
    }
}
