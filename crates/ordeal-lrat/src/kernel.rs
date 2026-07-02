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

/// A partial assignment over DIMACS variables.
///
/// `values[v]` is the value of variable `v` (index 0 unused), `None` when
/// unassigned.
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
        let var = lit.unsigned_abs() as usize;
        let var_value = self.values.get(var).copied().flatten()?;
        Some(if lit > 0 { var_value } else { !var_value })
    }

    /// Make `lit` true. Returns `true` iff this contradicts an existing
    /// assignment (i.e. `lit` was already false — a conflict).
    fn assign_true(&mut self, lit: i32) -> bool {
        match self.value(lit) {
            Some(true) => false, // already true: nothing to do
            Some(false) => true, // conflict
            None => {
                let var = lit.unsigned_abs() as usize;
                if var >= self.values.len() {
                    self.values.resize(var + 1, None);
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

    // Assume the negation of the new clause: every literal becomes false.
    // If the clause contains complementary literals (a tautology) this
    // already conflicts, and the step is trivially verified.
    for &lit in new_clause {
        if assignment.assign_true(-lit) {
            return Ok(());
        }
    }

    // Propagate through the hint clauses, in order.
    for &hint_id in hints {
        let clause = get_live(clauses, hint_id, step)?;

        // Classify the hint clause under the current assignment. Duplicate
        // literals are collapsed so that e.g. [x, x] counts as unit on x.
        let mut unassigned: Vec<i32> = Vec::new();
        for &lit in clause {
            match assignment.value(lit) {
                // A satisfied hint can never become unit or falsified:
                // it is useless for propagation, so the hint is invalid.
                Some(true) => {
                    return Err(CoreError::HintNotUnit {
                        step,
                        hint: hint_id,
                    });
                }
                Some(false) => {}
                None => {
                    if !unassigned.contains(&lit) {
                        unassigned.push(lit);
                    }
                }
            }
        }

        match unassigned.as_slice() {
            // Every literal false: conflict reached — the step is verified.
            [] => return Ok(()),
            // Exactly one unassigned literal: the clause is unit; assign it.
            // (It cannot conflict: the literal was unassigned.)
            [unit] => {
                let conflict = assignment.assign_true(*unit);
                debug_assert!(!conflict);
            }
            // Two or more unassigned literals: not a usable hint.
            _ => {
                return Err(CoreError::HintNotUnit {
                    step,
                    hint: hint_id,
                });
            }
        }
    }

    Err(CoreError::HintsExhausted { step })
}

/// Check a parsed step list against the input CNF.
///
/// Returns `Ok(())` iff some verified addition step adds the **empty
/// clause**, which proves the CNF unsatisfiable (checking stops there;
/// trailing steps are ignored). See the module docs for the soundness
/// theorem this function carries.
pub fn check_steps(cnf: &[Vec<i32>], steps: &[Step]) -> Result<(), CoreError> {
    // Load the original clauses as ids 1..=cnf.len(), validating literals
    // so that later negation (`-lit`) is always meaningful and safe.
    let mut clauses: Vec<Option<Vec<i32>>> = Vec::with_capacity(cnf.len());
    for (clause_index, clause) in cnf.iter().enumerate() {
        if clause.iter().any(|&lit| lit == 0 || lit == i32::MIN) {
            return Err(CoreError::InvalidCnfLiteral { clause_index });
        }
        clauses.push(Some(clause.clone()));
    }

    for (step_index, step) in steps.iter().enumerate() {
        match step {
            Step::Delete { ids } => {
                for &id in ids {
                    // Deleting an unknown or already-dead clause is rejected:
                    // the certificate and checker disagree about the clause set.
                    get_live(&clauses, id, step_index)?;
                    clauses[id - 1] = None;
                }
            }
            Step::Add { id, clause, hints } => {
                let expected = clauses.len() + 1;
                if *id != expected {
                    return Err(CoreError::NonSequentialId {
                        step: step_index,
                        expected,
                        found: *id,
                    });
                }
                check_rup(&clauses, clause, hints, step_index)?;
                let is_empty = clause.is_empty();
                clauses.push(Some(clause.clone()));
                if is_empty {
                    // A verified empty clause proves unsatisfiability;
                    // nothing after it can change that.
                    return Ok(());
                }
            }
        }
    }

    Err(CoreError::NoEmptyClause)
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
    fn rejects_exhausted_and_non_unit_hints() {
        let cnf = vec![vec![1, 2], vec![-1, 2], vec![-2, 1]];
        // Hints run out before a conflict.
        assert!(matches!(
            check_steps(&cnf, &[add(4, &[], &[1])]),
            Err(CoreError::HintNotUnit { .. }) | Err(CoreError::HintsExhausted { .. })
        ));
    }
}
