//! Ordeal's LRAT certificate checker — **the sole trusted component**.
//!
//! The ordeal solver is untrusted: an `Unsat` answer is believed only when
//! this checker has validated an LRAT certificate for it. This crate is
//! written to be translated to Lean 4 (via Aeneas) and formally verified, so
//! everything here is deliberately small, simple, and obviously correct:
//! no `unsafe`, no dependencies, no cleverness.
//!
//! # Supported dialect: textual LRAT, **RUP-only**
//!
//! **LOUD LIMITATION:** this checker supports only RUP (Reverse Unit
//! Propagation) addition steps. RAT steps — recognised by *negative* clause
//! ids in the hint list — are **rejected** with
//! [`CheckError::RatUnsupported`]. This is deliberate: ordeal's CDCL engine
//! emits RUP-only proofs, and rejecting is always sound (we may refuse a
//! valid certificate, we never accept an invalid one).
//!
//! Accepted line forms (whitespace-separated integers, one step per line;
//! blank lines and lines starting with `c` are skipped as comments):
//!
//! * Addition: `<id> <lit>* 0 <hint>* 0` — adds the clause `<lit>*` with id
//!   `<id>`, justified by unit propagation through the clauses named by
//!   `<hint>*`, in order.
//! * Deletion: `<id> d <id>* 0` — marks the named clauses dead. The leading
//!   `<id>` is informational (as emitted by drat-trim) and is not checked.
//!
//! Clause ids are 1-based: original clause `i` of the input CNF (0-based)
//! has id `i + 1`; each addition step must then use exactly the next
//! sequential id (this is what ordeal emits; sparse ids are rejected).
//!
//! # What "checked" means
//!
//! An addition step `C` with hints `h1..hk` is verified by assuming the
//! negation of every literal of `C` and then unit-propagating through the
//! hint clauses in order: each hint must be either *falsified* (conflict —
//! the step is verified, so CNF ∧ ¬C is unsat, i.e. CNF ⊨ C) or *unit*
//! (its single unassigned literal is assigned true). Anything else —
//! a satisfied hint, a hint with two or more unassigned literals, running
//! out of hints, a dead or unknown id — rejects the certificate.
//!
//! The whole certificate is accepted iff some verified addition step adds
//! the **empty clause** (checking stops there; trailing lines are ignored).

#![forbid(unsafe_code)]
#![warn(missing_docs)]

/// Why a certificate was rejected (or could not even be read).
///
/// Every variant carries the 1-based certificate line number where checking
/// stopped, except [`CheckError::NoEmptyClause`] (a property of the whole
/// certificate) and [`CheckError::InvalidCnfLiteral`] (a property of the
/// input CNF).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckError {
    /// The input CNF itself is malformed: a clause contains the literal `0`
    /// (or `i32::MIN`, whose negation would overflow).
    InvalidCnfLiteral {
        /// 0-based index of the offending clause in the input CNF.
        clause_index: usize,
    },
    /// A certificate line could not be parsed.
    Parse {
        /// 1-based line number in the certificate text.
        line: usize,
        /// Human-readable description of the parse failure.
        message: String,
    },
    /// An addition step did not use the next sequential clause id.
    NonSequentialId {
        /// 1-based line number in the certificate text.
        line: usize,
        /// The id this step was required to use.
        expected: usize,
        /// The id the step actually used.
        found: usize,
    },
    /// A hint or deletion referenced an id that was never assigned.
    UnknownId {
        /// 1-based line number in the certificate text.
        line: usize,
        /// The unknown clause id.
        id: usize,
    },
    /// A hint or deletion referenced a clause that was already deleted.
    DeletedId {
        /// 1-based line number in the certificate text.
        line: usize,
        /// The dead clause id.
        id: usize,
    },
    /// A negative hint id was found: a RAT step, which this RUP-only
    /// checker does not support (see the crate docs).
    RatUnsupported {
        /// 1-based line number in the certificate text.
        line: usize,
    },
    /// A hint clause was neither unit nor falsified under the current
    /// assignment (it was satisfied, or had two or more unassigned
    /// literals), so unit propagation cannot use it.
    HintNotUnit {
        /// 1-based line number in the certificate text.
        line: usize,
        /// The id of the offending hint clause.
        hint: usize,
    },
    /// The hint list ended before unit propagation reached a conflict, so
    /// the addition step is not justified.
    HintsExhausted {
        /// 1-based line number in the certificate text.
        line: usize,
    },
    /// The certificate ended without a verified addition of the empty
    /// clause, so unsatisfiability was not established.
    NoEmptyClause,
}

impl core::fmt::Display for CheckError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            CheckError::InvalidCnfLiteral { clause_index } => {
                write!(
                    f,
                    "input CNF clause {clause_index} contains an invalid literal"
                )
            }
            CheckError::Parse { line, message } => {
                write!(f, "line {line}: parse error: {message}")
            }
            CheckError::NonSequentialId {
                line,
                expected,
                found,
            } => {
                write!(
                    f,
                    "line {line}: expected clause id {expected}, found {found}"
                )
            }
            CheckError::UnknownId { line, id } => {
                write!(f, "line {line}: unknown clause id {id}")
            }
            CheckError::DeletedId { line, id } => {
                write!(f, "line {line}: clause id {id} was deleted")
            }
            CheckError::RatUnsupported { line } => {
                write!(
                    f,
                    "line {line}: RAT step (negative hint) — this checker is RUP-only"
                )
            }
            CheckError::HintNotUnit { line, hint } => {
                write!(
                    f,
                    "line {line}: hint clause {hint} is neither unit nor falsified"
                )
            }
            CheckError::HintsExhausted { line } => {
                write!(
                    f,
                    "line {line}: hints exhausted without reaching a conflict"
                )
            }
            CheckError::NoEmptyClause => {
                write!(f, "certificate contains no verified empty-clause addition")
            }
        }
    }
}

impl std::error::Error for CheckError {}

/// A partial assignment, mapping variables to `true`/`false`/unassigned.
///
/// `values[v]` is the value of variable `v` (index 0 is unused padding so
/// that variable numbers index directly). The vector grows on demand.
struct Assignment {
    values: Vec<Option<bool>>,
}

impl Assignment {
    fn new() -> Self {
        Assignment { values: Vec::new() }
    }

    /// The truth value of `lit` under this assignment, or `None` if the
    /// underlying variable is unassigned. `lit` must be nonzero and not
    /// `i32::MIN` (guaranteed by parsing / CNF validation).
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
fn get_live(clauses: &[Option<Vec<i32>>], id: usize, line: usize) -> Result<&[i32], CheckError> {
    if id == 0 || id > clauses.len() {
        return Err(CheckError::UnknownId { line, id });
    }
    match &clauses[id - 1] {
        Some(clause) => Ok(clause),
        None => Err(CheckError::DeletedId { line, id }),
    }
}

/// Verify one RUP addition step (see the crate docs for the definition).
///
/// `Ok(())` means the hint chain derived a conflict, i.e. the clause
/// `new_clause` is implied by the live clauses.
fn check_rup(
    clauses: &[Option<Vec<i32>>],
    new_clause: &[i32],
    hints: &[usize],
    line: usize,
) -> Result<(), CheckError> {
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
        let clause = get_live(clauses, hint_id, line)?;

        // Classify the hint clause under the current assignment. Duplicate
        // literals are collapsed so that e.g. [x, x] counts as unit on x.
        let mut unassigned: Vec<i32> = Vec::new();
        for &lit in clause {
            match assignment.value(lit) {
                // A satisfied hint can never become unit or falsified:
                // it is useless for propagation, so the hint is invalid.
                Some(true) => {
                    return Err(CheckError::HintNotUnit {
                        line,
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
                return Err(CheckError::HintNotUnit {
                    line,
                    hint: hint_id,
                });
            }
        }
    }

    Err(CheckError::HintsExhausted { line })
}

/// Parse one whitespace token as a clause id (a positive integer).
fn parse_id(token: &str, line: usize) -> Result<usize, CheckError> {
    match token.parse::<usize>() {
        Ok(id) if id >= 1 => Ok(id),
        _ => Err(CheckError::Parse {
            line,
            message: format!("expected a positive clause id, found {token:?}"),
        }),
    }
}

/// Parse one whitespace token as a DIMACS literal (nonzero, negatable i32).
fn parse_literal(token: &str, line: usize) -> Result<i32, CheckError> {
    match token.parse::<i32>() {
        // `i32::MIN` is rejected because `-lit` must not overflow.
        Ok(lit) if lit != 0 && lit != i32::MIN => Ok(lit),
        _ => Err(CheckError::Parse {
            line,
            message: format!("expected a nonzero literal, found {token:?}"),
        }),
    }
}

/// Handle a deletion line body (the tokens after `<id> d`): a list of live
/// clause ids terminated by `0`. Each named clause is marked dead.
fn delete(
    clauses: &mut [Option<Vec<i32>>],
    tokens: &[&str],
    line: usize,
) -> Result<(), CheckError> {
    let mut tokens = tokens.iter();
    loop {
        let Some(token) = tokens.next() else {
            return Err(CheckError::Parse {
                line,
                message: "deletion line missing terminating 0".to_string(),
            });
        };
        if *token == "0" {
            break;
        }
        let id = parse_id(token, line)?;
        // Deleting an unknown or already-dead clause is rejected: it means
        // the certificate and the checker disagree about the clause set.
        get_live(clauses, id, line)?;
        clauses[id - 1] = None;
    }
    if tokens.next().is_some() {
        return Err(CheckError::Parse {
            line,
            message: "trailing tokens after deletion terminator".to_string(),
        });
    }
    Ok(())
}

/// Handle an addition line body (the tokens after `<id>`): the new clause's
/// literals terminated by `0`, then the RUP hints terminated by `0`.
///
/// On success the verified clause has been appended; returns `true` iff the
/// added clause is the empty clause (the certificate's goal).
fn addition(
    clauses: &mut Vec<Option<Vec<i32>>>,
    id: usize,
    tokens: &[&str],
    line: usize,
) -> Result<bool, CheckError> {
    let expected = clauses.len() + 1;
    if id != expected {
        return Err(CheckError::NonSequentialId {
            line,
            expected,
            found: id,
        });
    }

    let mut tokens = tokens.iter();

    // The new clause: literals up to the first `0`.
    let mut new_clause: Vec<i32> = Vec::new();
    loop {
        let Some(token) = tokens.next() else {
            return Err(CheckError::Parse {
                line,
                message: "missing terminating 0 after clause literals".to_string(),
            });
        };
        if *token == "0" {
            break;
        }
        new_clause.push(parse_literal(token, line)?);
    }

    // The hints: clause ids up to the second `0`. A negative id marks a RAT
    // step, which this RUP-only checker rejects (see the crate docs).
    let mut hints: Vec<usize> = Vec::new();
    loop {
        let Some(token) = tokens.next() else {
            return Err(CheckError::Parse {
                line,
                message: "missing terminating 0 after hints".to_string(),
            });
        };
        if *token == "0" {
            break;
        }
        if token.starts_with('-') {
            return Err(CheckError::RatUnsupported { line });
        }
        hints.push(parse_id(token, line)?);
    }
    if tokens.next().is_some() {
        return Err(CheckError::Parse {
            line,
            message: "trailing tokens after hint terminator".to_string(),
        });
    }

    check_rup(clauses, &new_clause, &hints, line)?;
    let is_empty = new_clause.is_empty();
    clauses.push(Some(new_clause));
    Ok(is_empty)
}

/// Check a textual LRAT `certificate` against the input `cnf`.
///
/// `cnf` is the clause list in DIMACS literal convention (variable `v` is
/// the literal `v`, its negation `-v`; `0` is not a literal). Clause ids in
/// the certificate are 1-based: original clause `i` (0-based) has id
/// `i + 1`, and added clauses take sequential ids after that.
///
/// Returns `Ok(())` iff the certificate contains a verified addition of the
/// **empty clause**, which proves the CNF unsatisfiable. Any other outcome —
/// including certificates that are merely *not understood* (parse errors,
/// RAT steps) — is a rejection. Rejection never means "satisfiable"; it
/// only means "not proven unsatisfiable by this certificate".
pub fn check(cnf: &[Vec<i32>], certificate: &str) -> Result<(), CheckError> {
    // Load the original clauses as ids 1..=cnf.len(), validating literals
    // so that later negation (`-lit`) is always meaningful and safe.
    let mut clauses: Vec<Option<Vec<i32>>> = Vec::with_capacity(cnf.len());
    for (clause_index, clause) in cnf.iter().enumerate() {
        if clause.iter().any(|&lit| lit == 0 || lit == i32::MIN) {
            return Err(CheckError::InvalidCnfLiteral { clause_index });
        }
        clauses.push(Some(clause.clone()));
    }

    for (line_index, raw_line) in certificate.lines().enumerate() {
        let line = line_index + 1; // 1-based, for error reporting
        let tokens: Vec<&str> = raw_line.split_whitespace().collect();
        match tokens.first() {
            None => continue,                                  // blank line
            Some(first) if first.starts_with('c') => continue, // comment
            Some(first) => {
                let id = parse_id(first, line)?;
                if tokens.get(1) == Some(&"d") {
                    delete(&mut clauses, &tokens[2..], line)?;
                } else if addition(&mut clauses, id, &tokens[1..], line)? {
                    // A verified empty clause proves unsatisfiability;
                    // nothing after it can change that.
                    return Ok(());
                }
            }
        }
    }

    Err(CheckError::NoEmptyClause)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The 2-clause contradiction: (x1) ∧ (¬x1).
    fn tiny_cnf() -> Vec<Vec<i32>> {
        vec![vec![1], vec![-1]]
    }

    /// The 4-clause full contradiction over x1, x2:
    /// ids 1..=4 are [1,2], [-1,2], [1,-2], [-1,-2].
    fn quad_cnf() -> Vec<Vec<i32>> {
        vec![vec![1, 2], vec![-1, 2], vec![1, -2], vec![-1, -2]]
    }

    // ── Hand-verified ACCEPT cases (UV-011) ─────────────────────────────

    /// (a) Empty clause directly from the two unit clauses: assuming
    /// nothing, hint 1 = [1] is unit (assign x1), hint 2 = [-1] is
    /// falsified — conflict, step verified.
    #[test]
    fn accepts_two_unit_contradiction() {
        assert_eq!(check(&tiny_cnf(), "3 0 1 2 0"), Ok(()));
    }

    /// (b) Hand-derived RUP chain: first add [2] (assume ¬x2; hint 1 =
    /// [1,2] is unit on x1; hint 2 = [-1,2] is falsified). Then the empty
    /// clause (hint 5 = [2] is unit on x2; hint 3 = [1,-2] is unit on x1;
    /// hint 4 = [-1,-2] is falsified).
    #[test]
    fn accepts_quad_cnf_rup_chain() {
        let cert = "5 2 0 1 2 0\n6 0 5 3 4 0";
        assert_eq!(check(&quad_cnf(), cert), Ok(()));
    }

    /// (c) Same proof with a deletion line in the middle: clauses 1 and 2
    /// are dead by the final step, which only uses 5, 3, 4.
    #[test]
    fn accepts_proof_with_deletion() {
        let cert = "5 2 0 1 2 0\n5 d 1 2 0\n6 0 5 3 4 0";
        assert_eq!(check(&quad_cnf(), cert), Ok(()));
    }

    // ── Mutation REJECT cases (UV-011) ──────────────────────────────────

    /// Dropped hint: without hint 4 the final chain propagates but never
    /// reaches a conflict.
    #[test]
    fn rejects_dropped_hint() {
        let cert = "5 2 0 1 2 0\n6 0 5 3 0";
        assert_eq!(
            check(&quad_cnf(), cert),
            Err(CheckError::HintsExhausted { line: 2 })
        );
    }

    /// Wrong hint order: hint 3 = [1,-2] comes first, but with nothing
    /// assigned it has two unassigned literals — not unit, not falsified.
    #[test]
    fn rejects_wrong_hint_order() {
        let cert = "5 2 0 1 2 0\n6 0 3 4 5 0";
        assert_eq!(
            check(&quad_cnf(), cert),
            Err(CheckError::HintNotUnit { line: 2, hint: 3 })
        );
    }

    /// Reference to a deleted clause: clause 3 is deleted, then used.
    #[test]
    fn rejects_deleted_clause_reference() {
        let cert = "5 2 0 1 2 0\n5 d 3 0\n6 0 5 3 4 0";
        assert_eq!(
            check(&quad_cnf(), cert),
            Err(CheckError::DeletedId { line: 3, id: 3 })
        );
    }

    /// Reference to an id that was never assigned.
    #[test]
    fn rejects_unknown_id() {
        assert_eq!(
            check(&tiny_cnf(), "3 0 1 9 0"),
            Err(CheckError::UnknownId { line: 1, id: 9 })
        );
    }

    /// Truncated certificate: a valid step, but no empty clause ever.
    #[test]
    fn rejects_truncated_certificate() {
        assert_eq!(
            check(&quad_cnf(), "5 2 0 1 2 0"),
            Err(CheckError::NoEmptyClause)
        );
    }

    /// Certificate whose final (and only) added clause is non-empty: the
    /// step itself verifies, but unsatisfiability is never established.
    #[test]
    fn rejects_final_clause_non_empty() {
        // Adding [1]: assume ¬x1; hint 1 = [1] is falsified — verified.
        assert_eq!(
            check(&tiny_cnf(), "3 1 0 1 0"),
            Err(CheckError::NoEmptyClause)
        );
    }

    /// RAT-style negative hint: rejected as unsupported, never checked.
    #[test]
    fn rejects_rat_negative_hint() {
        assert_eq!(
            check(&tiny_cnf(), "3 0 1 -2 0"),
            Err(CheckError::RatUnsupported { line: 1 })
        );
    }

    /// Garbage text is a parse error, not a panic and not an accept.
    #[test]
    fn rejects_garbage_text() {
        assert!(matches!(
            check(&tiny_cnf(), "hello world"),
            Err(CheckError::Parse { line: 1, .. })
        ));
    }

    /// An addition step must use the next sequential id.
    #[test]
    fn rejects_non_sequential_id() {
        assert_eq!(
            check(&tiny_cnf(), "7 0 1 2 0"),
            Err(CheckError::NonSequentialId {
                line: 1,
                expected: 3,
                found: 7
            })
        );
    }

    // ── Dependency-graph guard (UV-011) ─────────────────────────────────

    /// TRUST BOUNDARY GUARD: this crate must depend on nothing — in
    /// particular not on the untrusted `ordeal` crate. The fact that this
    /// test compiled at all already proves the crate builds without
    /// `ordeal`; this assertion additionally pins the manifest to having
    /// no `[dependencies]` table whatsoever.
    #[test]
    fn manifest_declares_no_dependencies() {
        let manifest = include_str!("../Cargo.toml");
        assert!(
            !manifest.contains("[dependencies]"),
            "ordeal-lrat must remain dependency-free: it is the trust boundary"
        );
        assert!(
            !manifest.contains("ordeal\"") && !manifest.contains("ordeal ="),
            "ordeal-lrat must not depend on the untrusted ordeal crate"
        );
    }
}
