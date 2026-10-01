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

use blast_kernel::{DagNode, aig_new, compact, encode, map_word, tseitin};

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
/// `dag_wf_spec` proves exactly that equivalence.
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

/// Is `1 + n * (25·w² + 20·w + 1) <= usize::MAX` — the arena capacity
/// hypothesis of `encode_sound` (`gateBound`), for a DAG of `n` nodes whose
/// widths are at most `w`? Computed without overflowing: every product is
/// bounded by a division first (`x * y <= MAX` iff `x <= MAX / y`).
pub fn encode_fits(w: usize, n: usize) -> bool {
    let max = usize::MAX;
    if w > max / 25 {
        return false;
    }
    let w25 = 25 * w;
    if w > 0 && w25 > max / w {
        return false;
    }
    let sq = w25 * w;
    let lin = 20 * w;
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
        // gateBound(W) = 25 W² + 20 W + 1; 1 + n · gateBound(W) ≤ usize::MAX.
        assert!(encode_fits(0, 0));
        assert!(encode_fits(128, 1 << 20));
        assert!(encode_fits(0, usize::MAX - 1));
        assert!(!encode_fits(0, usize::MAX)); // 1 + MAX overflows
        assert!(!encode_fits(usize::MAX / 1000, 1));
        assert!(!encode_fits(1 << 16, usize::MAX / 1000));
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

    #[test]
    fn rejects_exhausted_and_non_unit_hints() {
        let cnf = vec![vec![1, 2], vec![-1, 2], vec![-2, 1]];
        // Hints run out before a conflict.
        assert!(matches!(
            check_steps(&cnf, &[add(4, &[], &[1])]),
            Err(CoreError::HintNotUnit { .. }) | Err(CoreError::HintsExhausted { .. })
        ));
    }
}
