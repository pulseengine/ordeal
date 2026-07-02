//! The pure-Rust CDCL SAT core (DES-004) — primary engine on every target.
//!
//! CONTRACT (wave-1 agent fills the implementation; this interface is fixed):
//! two-watched-literal propagation, first-UIP learning, VSIDS-style
//! decisions, Luby restarts. Every learned clause records its resolution
//! antecedents so LRAT emission (P2, TR-005) is a formatting step.

use crate::cnf::CnfFormula;

/// The verdict of a SAT solve.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SatResult {
    /// Satisfiable, with `assignment[v-1]` giving variable `v`'s value.
    Sat(Vec<bool>),
    /// Unsatisfiable.
    Unsat,
}

/// The CDCL solver.
#[derive(Debug, Default)]
pub struct SatSolver {}

impl SatSolver {
    /// Create a solver.
    pub fn new() -> Self {
        SatSolver {}
    }

    /// Decide satisfiability of the formula.
    pub fn solve(&mut self, formula: &CnfFormula) -> SatResult {
        // Wave-1 (DES-004/UV-004): CDCL implementation replaces this stub.
        let _ = formula;
        unimplemented!("DES-004: CDCL core lands in wave 1")
    }
}
