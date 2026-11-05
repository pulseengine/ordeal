//! The independently re-checkable SAT witness (TR-038 / #133). Since
//! TR-075 the witness type and its trusted recheck live in the
//! solver-free `ordeal-cert` crate (`ordeal_cert::witness`), re-exported
//! here unchanged; the solver's verdict type stays.

pub use ordeal_cert::witness::*;

use crate::solver::Certificate;

/// The result of [`crate::Solver::check_with_witness`] (TR-038): like
/// [`crate::CheckResult`] but `Sat` carries an independently
/// re-checkable [`SatCertificate`] instead of a bare model.
#[derive(Clone, Debug)]
pub enum WitnessCheckResult {
    /// Satisfiable, with a witness the trusted crate already validated.
    Sat(SatCertificate),
    /// Unsatisfiable, with the LRAT certificate the checker validated.
    Unsat(Certificate),
    /// No claim (identical semantics to [`crate::CheckResult::Unknown`]).
    Unknown,
}
