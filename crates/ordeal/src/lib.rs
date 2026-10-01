//! # Ordeal
//!
//! `ordeal` (meaning "verdict / judgment") is a specialized,
//! **certificate-checked** QF_BV SMT solver for the [PulseEngine] toolchain. It
//! exists to replace the Z3 static-link build pain that loom (verified WASM
//! optimizer) and synth (verified WASM→ARM codegen) carry today — grounding:
//! loom issue #246.
//!
//! ## Design in one paragraph
//!
//! An **untrusted solver** emits a machine-checkable **LRAT UNSAT
//! certificate**; a small **formally-verified checker** validates it. Only the
//! checker is trusted (the CompCert certifying-algorithm pattern; blueprint =
//! Lean 4 `bv_decide`, OOPSLA 2025). Z3 is demoted to a differential *oracle*
//! and benchmark *rival*, not the production engine. The pipeline is: term
//! graph → bit-blast → AIG → CNF (Tseitin) → SAT → LRAT → verified checker.
//!
//! ## Modules
//!
//! - [`term`] — the closed QF_BV fragment (the exact loom #246 op set).
//! - [`lowering`] — blessed derived-op constructors (`bvnot`, `bvneg`,
//!   `bvrotl`, `bvurem`, `bvsdiv`, `bvsrem`) built over the closed core, for
//!   the ops synth-verify emits but the fragment omits (DES-018).
//! - [`solver`] — the one-shot `check-sat` interface and result types.
//! - [`eval`] — the concrete evaluator (executable SMT-LIB semantics; the
//!   test oracle for every blasting rule and the SAT-model self-check).
//! - [`aig`] — the And-Inverter Graph arena (structural hashing, folding).
//! - [`blast`] — per-op-family bit-blasting rules (term → AIG).
//! - [`cnf`] — CNF types and the Tseitin encoder (AIG → CNF).
//! - [`sat`] — the pure-Rust CDCL core (primary engine on every target).
//! - [`lrat`] — LRAT certificate emission from the CDCL proof trace; the
//!   `ordeal-lrat` crate (the sole trusted component) validates it before
//!   any `Unsat` is returned.
//! - [`oracle`] — the Z3 differential oracle (behind the `oracle` feature).
//! - [`smtlib`] — a minimal QF_BV SMT-LIB2 reader for the standalone CLI /
//!   differential harness (not the production interface; that stays the API).
//!
//! [PulseEngine]: https://github.com/pulseengine

pub mod aig;
pub mod blast;
/// The proven lowering the solver runs (issue #68 / #192): since phase 4
/// a re-export of `ordeal_lrat::blast_kernel` (the Aeneas translation
/// target lives in the trusted crate so `check_query` re-encodes with the
/// same code), plus the solver-side differential tests. Kept out of the
/// public API surface.
#[doc(hidden)]
pub mod blast_kernel;
/// The TR-031 BMC-shaped benchmark corpus (spar#350). Not API — exists for
/// benches/bmc.rs and its tests; spar owns the real encoding.
#[doc(hidden)]
pub mod bmc_corpus;
pub mod canon;
/// `ordeal-cert/v1` bundle serialization (issue #91 / TR-025). Behind the
/// `cert-bundle` feature: the default build stays dependency-free.
#[cfg(feature = "cert-bundle")]
pub mod cert_bundle;
pub mod cnf;
/// The term DAG the proven encoder consumes (issue #192 phase 3): the
/// hash-consed builder from assertions and the structural-hashing hints
/// for `blast_kernel::compact`. Untrusted glue; not API.
#[doc(hidden)]
pub mod dag;
pub mod eval;
pub mod layout;
pub mod lowering;
pub mod lrat;
/// The certificate-carried query (#192 phase 4, `ordeal-cert/v2`) — always
/// compiled; the JSON envelope is in `cert_bundle`.
pub mod query;
pub mod sat;
/// In-tree SHA-256 for `ordeal-cert/v1` content hashes (#162 / TR-045):
/// integrity only, never part of the soundness argument.
pub mod sha256;
pub mod sliver;
pub mod smtlib;
pub mod solver;
pub mod term;
pub mod trap;
pub mod verus;
/// The re-checkable SAT witness (TR-038) — always compiled.
pub mod witness;

#[cfg(feature = "oracle")]
pub mod oracle;

#[cfg(all(feature = "cadical", not(target_family = "wasm")))]
pub mod sat_cadical;

pub use query::{QueryCertificate, QueryCheckResult, QueryDag, QueryRecheckError};
pub use solver::{Certificate, CertificateError, CheckResult, Model, Solver};
pub use term::{BoolTerm, BvTerm, Sort};
pub use witness::{SatCertificate, SatRecheckError, WitnessCheckResult};
