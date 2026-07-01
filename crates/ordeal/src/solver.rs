//! The one-shot solver interface.
//!
//! Callers (loom, synth) build a conjunction of asserted [`BoolTerm`]s and call
//! [`Solver::check`]. The result is one of:
//!
//! - [`CheckResult::Unsat`] — the assertions are unsatisfiable, carrying an
//!   (eventually machine-checkable) [`Certificate`]. For an equivalence query
//!   this is the "equivalence holds" verdict.
//! - [`CheckResult::Sat`] — the assertions are satisfiable, carrying a
//!   counterexample [`Model`].
//! - [`CheckResult::Unknown`] — the solver could not decide.
//!
//! # Soundness contract for callers
//!
//! `Unknown` MUST be treated **conservatively**: loom/synth must NOT apply the
//! optimization / accept the codegen when they receive `Unknown`. Only a
//! checked `Unsat` certificate authorizes a transformation. This mirrors
//! loom's existing "conservative-over-fast" philosophy: if we cannot *prove*
//! equivalence, we keep the original.

use crate::term::BoolTerm;

/// A machine-checkable UNSAT certificate.
///
/// The solver (untrusted) emits an LRAT proof; the formally-verified checker
/// (the only trusted component) validates it. Empty until phase P2 wires up
/// the SAT backend and LRAT emission — see `ROADMAP.md`.
#[derive(Clone, Debug, Default)]
pub struct Certificate {
    /// The LRAT proof bytes. Empty in the phase-0 skeleton.
    pub lrat: Vec<u8>,
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
    /// Unsatisfiable, with a certificate the verified checker can validate.
    Unsat(Certificate),
    /// Satisfiable, with a counterexample model.
    Sat(Model),
    /// Undecided.
    ///
    /// Callers MUST treat this conservatively: do NOT optimize / do NOT accept
    /// the transformation. See the module-level soundness contract.
    Unknown,
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

    /// Decide satisfiability of the conjunction of all asserted terms.
    ///
    /// # Phase-0 behavior
    ///
    /// This skeleton conservatively returns [`CheckResult::Unknown`] for every
    /// query. This is **sound by construction**: a caller that honors the
    /// `Unknown`-is-conservative contract can never be misled by the skeleton,
    /// because `Unknown` never authorizes a transformation.
    ///
    /// This method is replaced op-by-op by the real pipeline — term graph →
    /// bit-blast → AIG → CNF (Tseitin) → SAT → LRAT → verified checker — as
    /// each fragment operation gains a proven bit-blasting rule. Until an
    /// operation is provably handled, the solver stays conservative rather than
    /// guess.
    pub fn check(&self) -> CheckResult {
        CheckResult::Unknown
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::{BvTerm, Sort};

    #[test]
    fn phase0_check_is_conservatively_unknown() {
        // Build a trivially-unsat query: x == x+1 over 32-bit bitvectors.
        // A real engine would return Unsat; the phase-0 skeleton must return
        // Unknown (sound-by-construction), never a bogus Unsat/Sat.
        let bv32 = Sort::new(32);
        let x = BvTerm::Var {
            name: "x".to_string(),
            sort: bv32,
        };
        let x_plus_1 = BvTerm::Add(
            Box::new(x.clone()),
            Box::new(BvTerm::Const {
                value: 1,
                sort: bv32,
            }),
        );

        let mut solver = Solver::new();
        solver.assert(BoolTerm::Eq(Box::new(x), Box::new(x_plus_1)));
        assert_eq!(solver.num_assertions(), 1);

        match solver.check() {
            CheckResult::Unknown => {}
            other => panic!("phase-0 skeleton must return Unknown, got {other:?}"),
        }
    }

    #[test]
    fn empty_solver_is_unknown() {
        let solver = Solver::new();
        assert!(matches!(solver.check(), CheckResult::Unknown));
    }
}
