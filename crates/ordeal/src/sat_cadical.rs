//! The optional CaDiCaL SAT backend (TR-004) — accelerator, never load-bearing.
//!
//! This module is compiled **only** when the `cadical` feature is enabled and
//! never on wasm targets. When the feature is off it is entirely absent, so
//! the default build has zero external dependencies and always compiles.
//!
//! # Role
//!
//! ordeal's primary SAT engine is the in-tree pure-Rust CDCL core
//! ([`crate::sat`]) on **every** target — that never changes. CaDiCaL
//! (C++ 2.1.3, vendored by `cadical-sys`, built hermetically at compile time)
//! is an optional native **accelerator and benchmark yardstick**: callers may
//! use it to solve a CNF faster, but nothing in the production pipeline
//! depends on it, and it is held to the identical soundness contract:
//!
//! > Never return an `Unsat` the verified checker has not validated.
//!
//! [`solve`] configures CaDiCaL to trace an ASCII LRAT proof (`lrat=1`,
//! `binary=0`), and on UNSAT feeds that proof to `ordeal_lrat::check` **before
//! returning**. A proof the checker rejects surfaces as
//! [`CadicalError::ProofRejected`], never as a bare `Unsat`. On SAT the model
//! is self-checked against the input formula — a failing model surfaces as
//! [`CadicalError::ModelSelfCheckFailed`].
//!
//! # LRAT dialect — why the CNF goes in as a DIMACS file
//!
//! `ordeal_lrat::check` requires the standard LRAT numbering: original
//! clauses are ids `1..=n` in input order, additions strictly sequential from
//! `n + 1`. CaDiCaL only guarantees that numbering when it knows the clause
//! count up front: its DIMACS parser calls `Internal::reserve_ids (clauses)`,
//! pinning ids `1..=n` to the originals. The incremental `add()` API never
//! reserves, so there CaDiCaL interleaves derived-clause ids with original
//! ids (e.g. a unit derived while ingesting clause 2 takes id 3, shifting
//! every later original) — proofs in that dialect reference CaDiCaL's private
//! numbering and are unusable against the input clause list. Hence [`solve`]
//! writes the formula to a temporary DIMACS file and loads it via
//! `read_dimacs`, with the proof tracer attached first. Should CaDiCaL still
//! emit a non-conforming proof, the checker rejects it and the caller gets
//! [`CadicalError::ProofRejected`] — the conservative outcome for an
//! untrusted backend, never a wrong `Unsat`.
//!
//! # Temp-file plumbing
//!
//! Both the DIMACS input and the LRAT proof go through the system temp
//! directory, unique per process + call, and are removed before returning
//! (this backend is native-only, so `std::env::temp_dir` is always
//! available).

use crate::cnf::CnfFormula;
use cadical_sys::{CaDiCal, Status};
use std::sync::atomic::{AtomicU64, Ordering};

/// The verdict of a CaDiCaL solve, mirroring [`crate::sat::SatResult`] but
/// carrying the checker-validated LRAT proof on UNSAT.
#[derive(Clone, Debug)]
pub enum CadicalVerdict {
    /// Satisfiable; `assignment[v-1]` gives variable `v`'s value. The model
    /// has already been self-checked against the input formula.
    Sat(Vec<bool>),
    /// Unsatisfiable, with the ASCII LRAT proof CaDiCaL emitted — already
    /// accepted by `ordeal_lrat::check` against the input clauses.
    Unsat {
        /// The checker-validated LRAT certificate text.
        lrat: String,
    },
}

/// Why a CaDiCaL solve produced no verdict. Every variant is conservative:
/// callers treat all of them like `Unknown`, never as a verdict.
#[derive(Clone, Debug)]
pub enum CadicalError {
    /// CaDiCaL returned neither SAT nor UNSAT (interrupted / limited).
    Inconclusive,
    /// Configuring the solver (options / proof tracing) failed.
    Configuration(&'static str),
    /// The proof file could not be created, read back, or removed.
    ProofIo(String),
    /// CaDiCaL said UNSAT but the verified checker rejected its LRAT proof.
    /// Per the soundness contract this is never surfaced as `Unsat`.
    ProofRejected(ordeal_lrat::CheckError),
    /// CaDiCaL said SAT but the model does not satisfy the input formula.
    ModelSelfCheckFailed,
}

/// Solve `formula` with CaDiCaL, holding it to the ordeal soundness contract.
///
/// Returns [`CadicalVerdict::Unsat`] only with an LRAT proof the verified
/// checker accepted, and [`CadicalVerdict::Sat`] only with a model that
/// evaluates the formula to true. Everything else is a [`CadicalError`],
/// which callers must treat as no-verdict (the same posture as `Unknown`).
pub fn solve(formula: &CnfFormula) -> Result<CadicalVerdict, CadicalError> {
    solve_inner(formula, None)
}

/// Like [`solve`], but caps CaDiCaL's search at `max_conflicts` conflicts.
/// Exhaustion surfaces as [`CadicalError::Inconclusive`] — the same
/// conservative no-verdict posture as the own core's bounded solves.
pub fn solve_with_conflict_limit(
    formula: &CnfFormula,
    max_conflicts: i32,
) -> Result<CadicalVerdict, CadicalError> {
    solve_inner(formula, Some(max_conflicts))
}

fn solve_inner(
    formula: &CnfFormula,
    max_conflicts: Option<i32>,
) -> Result<CadicalVerdict, CadicalError> {
    static CALL: AtomicU64 = AtomicU64::new(0);
    let stamp = format!(
        "{}-{}",
        std::process::id(),
        CALL.fetch_add(1, Ordering::Relaxed)
    );
    let proof_path = std::env::temp_dir().join(format!("ordeal-cadical-{stamp}.lrat"));
    let dimacs_path = std::env::temp_dir().join(format!("ordeal-cadical-{stamp}.cnf"));
    let cleanup = || {
        let _ = std::fs::remove_file(&proof_path);
        let _ = std::fs::remove_file(&dimacs_path);
    };
    let proof_path_str = proof_path
        .to_str()
        .ok_or(CadicalError::Configuration("non-UTF-8 temp path"))?
        .to_string();
    let dimacs_path_str = dimacs_path
        .to_str()
        .ok_or(CadicalError::Configuration("non-UTF-8 temp path"))?
        .to_string();

    // Serialize to DIMACS: the file's `p cnf` header is what makes CaDiCaL
    // reserve ids 1..=n for the originals (see module docs).
    let mut dimacs = format!("p cnf {} {}\n", formula.num_vars, formula.clauses.len());
    for clause in &formula.clauses {
        for &lit in clause {
            dimacs.push_str(&lit.to_string());
            dimacs.push(' ');
        }
        dimacs.push_str("0\n");
    }
    std::fs::write(&dimacs_path, dimacs).map_err(|e| {
        cleanup();
        CadicalError::ProofIo(e.to_string())
    })?;

    let mut solver = CaDiCal::new();
    for (option, value, err) in [
        ("lrat", 1, "lrat option rejected"),
        ("binary", 0, "binary option rejected"),
    ] {
        if !solver.set(option.to_string(), value) {
            cleanup();
            return Err(CadicalError::Configuration(err));
        }
    }
    // Tracer before parsing, so the id reservation lands in the proof state.
    if !solver.trace_proof2(proof_path_str) {
        cleanup();
        return Err(CadicalError::Configuration("trace_proof rejected"));
    }
    let mut vars: i32 = 0;
    // CaDiCaL's `read_dimacs` returns NULL on success; the cadical-sys cxx
    // bridge stringifies that NULL as the literal "Null".
    let parse_err = solver.read_dimacs2(dimacs_path_str, &mut vars, 1);
    if parse_err != "Null" {
        cleanup();
        return Err(CadicalError::ProofIo(format!("DIMACS parse: {parse_err}")));
    }
    if let Some(conflicts) = max_conflicts {
        if !solver.limit("conflicts".to_string(), conflicts) {
            cleanup();
            return Err(CadicalError::Configuration("conflicts limit rejected"));
        }
    }
    let status = solver.solve();
    match status {
        Status::UNSATISFIABLE => {
            // Flush the tracer (conclude + drop closes the proof file), then
            // read the proof back and hold it to the verified checker.
            solver.conclude();
            drop(solver);
            let lrat = std::fs::read_to_string(&proof_path).map_err(|e| {
                cleanup();
                CadicalError::ProofIo(e.to_string())
            })?;
            cleanup();
            match ordeal_lrat::check(&formula.clauses, &lrat) {
                Ok(()) => Ok(CadicalVerdict::Unsat { lrat }),
                Err(e) => Err(CadicalError::ProofRejected(e)),
            }
        }
        Status::SATISFIABLE => {
            let assignment: Vec<bool> = (1..=formula.num_vars)
                .map(|v| solver.val(v as i32) > 0)
                .collect();
            drop(solver);
            cleanup();
            if formula.eval(&assignment) {
                Ok(CadicalVerdict::Sat(assignment))
            } else {
                Err(CadicalError::ModelSelfCheckFailed)
            }
        }
        _ => {
            drop(solver);
            cleanup();
            Err(CadicalError::Inconclusive)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat::{SatResult, SatSolver};

    /// Deterministic xorshift so the corpus is reproducible (no `rand` dep).
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }
    }

    /// Random k-SAT-ish CNF near the phase transition so both verdicts occur.
    fn random_cnf(rng: &mut Rng, num_vars: u32, num_clauses: usize) -> CnfFormula {
        let mut clauses = Vec::with_capacity(num_clauses);
        for _ in 0..num_clauses {
            let len = 1 + (rng.next() % 3) as usize;
            let mut clause = Vec::with_capacity(len);
            for _ in 0..len {
                let var = 1 + (rng.next() % u64::from(num_vars)) as i32;
                let lit = if rng.next() & 1 == 0 { var } else { -var };
                clause.push(lit);
            }
            clauses.push(clause);
        }
        CnfFormula { num_vars, clauses }
    }

    /// VER-008 (CNF level): CaDiCaL agrees with the own pure-Rust core on a
    /// seeded random corpus; every CaDiCaL UNSAT carries a checker-accepted
    /// LRAT proof (enforced inside `solve`), every SAT a self-checked model.
    #[test]
    fn cadical_agrees_with_own_core_on_random_cnfs() {
        let mut rng = Rng(0x0DEA1_5EED);
        let (mut sats, mut unsats) = (0u32, 0u32);
        for round in 0..200 {
            let num_vars = 4 + (round % 12) as u32;
            let num_clauses = (f64::from(num_vars) * 4.3) as usize;
            let formula = random_cnf(&mut rng, num_vars, num_clauses);
            let own = SatSolver::new().solve(&formula);
            let cadical = solve(&formula).expect("CaDiCaL produced no verdict");
            match (own, cadical) {
                (SatResult::Sat(_), CadicalVerdict::Sat(_)) => sats += 1,
                (SatResult::Unsat, CadicalVerdict::Unsat { .. }) => unsats += 1,
                (own, cadical) => {
                    panic!("backend disagreement on round {round}: own={own:?} cadical={cadical:?}")
                }
            }
        }
        // The corpus must exercise both verdicts or the parity is vacuous.
        assert!(
            sats > 0 && unsats > 0,
            "one-sided corpus: {sats} sat / {unsats} unsat"
        );
    }

    /// The soundness plumbing: a hand-built UNSAT instance yields a proof the
    /// checker accepts, and the proof text is carried in the verdict.
    #[test]
    fn cadical_unsat_carries_checker_validated_lrat() {
        // x1 & !x1 via three clauses (forces at least one resolution).
        let formula = CnfFormula {
            num_vars: 2,
            clauses: vec![vec![1, 2], vec![1, -2], vec![-1]],
        };
        match solve(&formula).expect("verdict") {
            CadicalVerdict::Unsat { lrat } => {
                assert!(!lrat.is_empty());
                // Re-check independently: the verdict's own validation is not
                // taken on faith here.
                ordeal_lrat::check(&formula.clauses, &lrat)
                    .expect("checker must re-accept the carried proof");
            }
            v => panic!("expected Unsat, got {v:?}"),
        }
    }
}
