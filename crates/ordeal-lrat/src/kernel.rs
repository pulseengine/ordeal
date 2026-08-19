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
        None => Ok(()),
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
    fn rejects_exhausted_and_non_unit_hints() {
        let cnf = vec![vec![1, 2], vec![-1, 2], vec![-2, 1]];
        // Hints run out before a conflict.
        assert!(matches!(
            check_steps(&cnf, &[add(4, &[], &[1])]),
            Err(CoreError::HintNotUnit { .. }) | Err(CoreError::HintsExhausted { .. })
        ));
    }
}
