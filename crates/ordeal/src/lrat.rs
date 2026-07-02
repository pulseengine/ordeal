//! LRAT certificate emission from the CDCL proof trace (DES-013).
//!
//! The CDCL core (DES-004) records every learned clause as a
//! [`LearnedStep`] whose antecedents already form a reverse-unit-propagation
//! chain, so emission is pure formatting into the textual LRAT dialect the
//! `ordeal-lrat` checker consumes:
//!
//! - the `k`-th learned step becomes addition line `n + k + 1` over `n`
//!   input clauses (ids strictly sequential, matching the checker);
//! - hints are the step's antecedent indices, shifted to 1-based clause ids
//!   in their recorded RUP order;
//! - no deletion lines are emitted (the CDCL keeps learned clauses);
//! - an UNSAT trace ends with the empty-clause step, which is exactly the
//!   line that makes the checker accept.
//!
//! The emitted certificate is UNTRUSTED output of an untrusted solver: the
//! pipeline (DES-013 wiring in `solver.rs`) returns `Unsat` only after the
//! checker accepts it.

use crate::sat::LearnedStep;
use std::fmt::Write as _;

/// Format a proof trace as a textual LRAT certificate.
///
/// `n_orig` is the number of input clauses (the trace's antecedent indices
/// `< n_orig` refer to them; `n_orig + k` refers to the `k`-th step).
pub fn emit_lrat(n_orig: usize, trace: &[LearnedStep]) -> String {
    let mut out = String::new();
    for (k, step) in trace.iter().enumerate() {
        let id = n_orig + k + 1;
        // `<id> <lit>* 0 <hint>* 0`
        let _ = write!(out, "{id}");
        for lit in &step.clause {
            let _ = write!(out, " {lit}");
        }
        out.push_str(" 0");
        for &ante in &step.antecedents {
            let _ = write!(out, " {}", ante + 1);
        }
        out.push_str(" 0\n");
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cnf::CnfFormula;
    use crate::sat::{SatResult, SatSolver};

    /// Solve a CNF expected UNSAT, emit the certificate, and return it
    /// together with the clause list the checker needs.
    fn unsat_cert(clauses: Vec<Vec<i32>>, num_vars: u32) -> (Vec<Vec<i32>>, String) {
        let formula = CnfFormula {
            num_vars,
            clauses: clauses.clone(),
        };
        let mut solver = SatSolver::new();
        assert_eq!(solver.solve(&formula), SatResult::Unsat, "expected UNSAT");
        let cert = emit_lrat(clauses.len(), solver.proof_trace());
        (clauses, cert)
    }

    #[test]
    fn two_units_certificate_is_accepted() {
        let (clauses, cert) = unsat_cert(vec![vec![1], vec![-1]], 1);
        assert!(!cert.is_empty());
        ordeal_lrat::check(&clauses, &cert).expect("checker must accept");
    }

    #[test]
    fn four_clause_contradiction_certificate_is_accepted() {
        let (clauses, cert) =
            unsat_cert(vec![vec![1, 2], vec![-1, 2], vec![1, -2], vec![-1, -2]], 2);
        ordeal_lrat::check(&clauses, &cert).expect("checker must accept");
    }

    #[test]
    fn pigeonhole_certificate_is_accepted() {
        // PHP(4,3): pigeon i in {1..4} gets hole in {1..3}; var(i,h) = 3(i-1)+h.
        let v = |i: i32, h: i32| 3 * (i - 1) + h;
        let mut clauses: Vec<Vec<i32>> = (1..=4)
            .map(|i| (1..=3).map(|h| v(i, h)).collect())
            .collect();
        for h in 1..=3 {
            for i in 1..=4 {
                for j in (i + 1)..=4 {
                    clauses.push(vec![-v(i, h), -v(j, h)]);
                }
            }
        }
        let (clauses, cert) = unsat_cert(clauses, 12);
        ordeal_lrat::check(&clauses, &cert).expect("checker must accept PHP(4,3)");
    }

    #[test]
    fn random_unsat_certificates_are_accepted() {
        // Deterministic random 3-SAT at high clause/var ratio: keep the UNSAT
        // ones (verified by the solver) and check every emitted certificate.
        let mut s: u64 = 0x1DA7_CE27_0000_0001;
        let mut next = move || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        };
        let mut unsat_seen = 0;
        for _ in 0..60 {
            let n_vars = 6 + (next() % 5) as u32; // 6..=10
            let n_clauses = (n_vars as u64 * 5) as usize;
            let clauses: Vec<Vec<i32>> = (0..n_clauses)
                .map(|_| {
                    (0..3)
                        .map(|_| {
                            let v = (next() % n_vars as u64) as i32 + 1;
                            if next() % 2 == 0 { v } else { -v }
                        })
                        .collect()
                })
                .collect();
            let formula = CnfFormula {
                num_vars: n_vars,
                clauses: clauses.clone(),
            };
            let mut solver = SatSolver::new();
            if solver.solve(&formula) == SatResult::Unsat {
                unsat_seen += 1;
                let cert = emit_lrat(clauses.len(), solver.proof_trace());
                ordeal_lrat::check(&clauses, &cert)
                    .unwrap_or_else(|e| panic!("checker rejected a real certificate: {e:?}"));
            }
        }
        assert!(
            unsat_seen >= 10,
            "corpus produced too few UNSAT instances: {unsat_seen}"
        );
    }

    #[test]
    fn mutated_certificates_are_rejected() {
        let (clauses, cert) =
            unsat_cert(vec![vec![1, 2], vec![-1, 2], vec![1, -2], vec![-1, -2]], 2);
        // Dropping the final (empty-clause) line must be rejected.
        let mut lines: Vec<&str> = cert.lines().collect();
        let last = lines.pop().expect("certificate has lines");
        let truncated = lines.join("\n");
        assert!(ordeal_lrat::check(&clauses, &truncated).is_err());
        // Reversing the hint order of the final step must be rejected
        // (the RUP chain is order-sensitive) — unless it is a single hint.
        let mut parts: Vec<&str> = last.split_whitespace().collect();
        let second_zero = parts.len() - 1;
        let first_zero = parts
            .iter()
            .position(|&p| p == "0")
            .expect("lit terminator");
        if second_zero - first_zero > 2 {
            parts[first_zero + 1..second_zero].reverse();
            let mut mutated_lines = lines.clone();
            let mutated_last = parts.join(" ");
            mutated_lines.push(&mutated_last);
            let mutated = mutated_lines.join("\n");
            assert!(
                ordeal_lrat::check(&clauses, &mutated).is_err(),
                "reordered hints must not verify"
            );
        }
    }
}
