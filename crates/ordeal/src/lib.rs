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
/// The Aeneas translation target for the bit-blaster's correctness proof
/// (issue #68, v0.15.0). Not the production blaster — a self-contained,
/// Charon-translatable *model* whose Aeneas-generated Lean (`lean/Blaster.lean`)
/// is proven equal to the formal `BitVec` semantics for all widths, replacing
/// the Kani-bounded evidence with an unbounded proof. Kept out of the public
/// API surface: it exists to be translated, not called.
#[doc(hidden)]
pub mod blast_kernel;
pub mod canon;
pub mod cnf;
pub mod eval;
pub mod layout;
pub mod lowering;
pub mod lrat;
pub mod sat;
pub mod sliver;
pub mod smtlib;
pub mod solver;
pub mod term;
pub mod trap;
pub mod verus;

#[cfg(feature = "oracle")]
pub mod oracle;

pub use solver::{Certificate, CertificateError, CheckResult, Model, Solver};
pub use term::{BoolTerm, BvTerm, Sort};
