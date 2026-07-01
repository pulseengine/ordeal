//! The differential oracle: Z3 as a cross-check, not the production engine.
//!
//! This module is compiled **only** when the `oracle` feature is enabled. When
//! the feature is off it is entirely absent, so the default build has zero
//! external dependencies and always compiles.
//!
//! # Role
//!
//! `ordeal`'s production engine is an untrusted solver plus a formally-verified
//! LRAT checker (see `ARCHITECTURE.md`). Z3 is deliberately **demoted** to two
//! non-production roles:
//!
//! 1. A **differential oracle** — during development and CI, every query can be
//!    sent to Z3 as well, and any disagreement between `ordeal` and Z3 is a bug
//!    to investigate. This is a safety net, not part of the soundness argument.
//! 2. A **benchmark rival** — we compare integration latency against Z3. The
//!    honest win is amortized *per-op* latency (in-process, no SMT-LIB parse,
//!    no theory combination), NOT out-solving Z3's SAT engine.
//!
//! Note that the oracle is NOT part of the trust story: soundness rests on the
//! verified checker alone. A later roadmap phase (P4) drops Z3 from the
//! soundness argument entirely.
//!
//! # Status
//!
//! Stub. Enabling `oracle` does not yet pull in a `z3` dependency; the real
//! cross-check is wired up once the solver produces certificates worth checking
//! (ROADMAP phase P1+).

use crate::solver::CheckResult;
use crate::term::BoolTerm;

/// Outcome of cross-checking an `ordeal` result against the Z3 oracle.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OracleVerdict {
    /// `ordeal` and the oracle agree (or the oracle was not consulted).
    Agree,
    /// `ordeal` and the oracle disagree — this indicates a bug in `ordeal`.
    Disagree,
    /// The oracle could not be run (not yet implemented in this phase).
    Unavailable,
}

/// Cross-check an `ordeal` [`CheckResult`] against Z3 for the given assertions.
///
/// Stub: always returns [`OracleVerdict::Unavailable`] until the Z3 backend is
/// wired up. The signature is fixed now so the call sites in loom/synth CI can
/// be written against a stable API.
pub fn cross_check(_assertions: &[BoolTerm], _result: &CheckResult) -> OracleVerdict {
    OracleVerdict::Unavailable
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn oracle_stub_is_unavailable() {
        let result = CheckResult::Unknown;
        assert_eq!(cross_check(&[], &result), OracleVerdict::Unavailable);
    }
}
