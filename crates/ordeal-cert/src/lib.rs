//! `ordeal-cert` — the ordeal certificate data types, their trusted
//! re-checks, and (behind the `json` feature) the `ordeal-cert/v1`..`v4`
//! bundle encoder and hash-verifying decoder (TR-075).
//!
//! This is the half of ordeal an auditor needs to re-check a certificate
//! bundle WITHOUT the solver: it depends on the trusted `ordeal-lrat`
//! crate only (plus `serde` / `serde_json` for the envelope), never on
//! `ordeal`. Every `recheck` here calls the same `ordeal_lrat` functions,
//! in the same way, as the solver does before it returns a verdict — the
//! code moved verbatim from `ordeal`, which re-exports all of it at the
//! paths it always had (`ordeal::Certificate`, `ordeal::query::*`,
//! `ordeal::cert_bundle::*`, …).
//!
//! What is trusted in a re-check is `ordeal-lrat` (proven in Lean 4 over
//! its Aeneas translation) and the toolchain. The code here is the
//! untrusted glue that decodes the bundle and hands its contents to the
//! trusted checks: a bug here can make a valid bundle be rejected, or a
//! re-check be run on different data than the bundle carries — which is
//! why the decoders verify the content hashes before anything is
//! returned, and why the `ordeal-recheck` binary runs the full recheck
//! of the strongest certificate the bundle's `format` names.

/// The `ordeal-cert` JSON envelopes (`v1`..`v4`): emit and hash-verified
/// parse. Behind the `json` feature (serde): the default build is
/// dependency-free beyond `ordeal-lrat`.
#[cfg(feature = "json")]
pub mod cert_bundle;
/// The v1 certificate pair ([`Certificate`]) and the model type
/// ([`Model`]).
pub mod certificate;
/// The certificate-carried query, term and extended query, and their
/// trusted re-checks.
pub mod query;
/// In-tree SHA-256 for the content hashes (integrity only, never part of
/// the soundness argument).
pub mod sha256;
/// The extended query as asked and the extended model (TR-072).
pub mod sliver;
/// The re-checkable SAT witness (TR-038).
pub mod witness;

pub use certificate::{Certificate, CertificateError, Model};
pub use query::{
    QueryCertificate, QueryDag, QueryInputs, QueryModelRecheckError, QueryRecheckError,
    QuerySatCertificate, QueryTerm, SliverBlock, SliverCertificate, SliverModelRecheckError,
    SliverRecheckError, SliverSatCertificate, TermCertificate, TermModelRecheckError,
    TermRecheckError, TermSatCertificate,
};
pub use witness::{SatCertificate, SatRecheckError};

// Dev-dependency-free on purpose (Bazel's rust_test compiles these without
// Cargo dev-deps); the solver-produced corpus is exercised end to end by
// crates/ordeal-recheck/tests/recheck_cli.rs.
#[cfg(test)]
mod tests {
    use super::*;

    /// `x ∧ ¬x`, refuted in one RUP step: the trusted checker accepts the
    /// pair, and rejects it once the proof is gone, the CNF is no longer
    /// contradictory, or the proof bytes are not text.
    #[test]
    fn hand_built_certificate_rechecks_and_tampering_is_rejected() {
        let good = Certificate {
            cnf: vec![vec![1], vec![-1]],
            lrat: b"3 0 1 2 0\n".to_vec(),
        };
        good.recheck().expect("x and not-x is refuted");
        let no_proof = Certificate {
            lrat: Vec::new(),
            ..good.clone()
        };
        assert!(no_proof.recheck().is_err());
        let sat_cnf = Certificate {
            cnf: vec![vec![1], vec![1]],
            ..good.clone()
        };
        assert!(sat_cnf.recheck().is_err());
        let not_text = Certificate {
            lrat: vec![0xff],
            ..good
        };
        assert!(matches!(not_text.recheck(), Err(CertificateError::NotText)));
    }

    /// Every node spelling round-trips, and an unknown one is refused.
    #[test]
    fn node_spelling_round_trips() {
        use ordeal_lrat::blast_kernel::DagNode as N;
        for n in [
            N::Var(8),
            N::Const(0, 8),
            N::Add(0, 1),
            N::Extract(7, 0, 2),
            N::Ite(0, 1, 2),
            N::Sdiv(0, 1),
            N::Not(3),
        ] {
            let (op, args) = query::node_op(&n);
            assert!(query::node_from_op(op, &args) == Some(n), "{op}");
        }
        assert!(query::node_from_op("frobnicate", &[0, 1]).is_none());
        assert!(query::node_from_op("add", &[0]).is_none());
    }

    /// The portable index spelling (the wasm32 re-checker reads 64-bit
    /// bundles): the sentinel is `u64::MAX` on every target and round-trips,
    /// an ordinary index is its value.
    #[test]
    fn no_image_has_one_spelling_on_every_target() {
        assert_eq!(query::wire_usize(query::NO_IMAGE), u64::MAX);
        assert_eq!(query::unwire_usize(u64::MAX), Some(query::NO_IMAGE));
        assert_eq!(query::wire_usize(7), 7);
        assert_eq!(query::unwire_usize(7), Some(7));
        let t = QueryTerm {
            map: vec![0, query::NO_IMAGE],
            ..QueryTerm::default()
        };
        assert!(t.canonical_text().contains("map 0 18446744073709551615\n"));
    }

    /// The SAT witness recheck: a satisfying assignment with a consistent
    /// binding is accepted; a falsified clause or a wrong value is not.
    #[test]
    fn sat_witness_rechecks() {
        let w = SatCertificate {
            model: Model {
                assignments: vec![("a".into(), 1)],
            },
            cnf: vec![vec![1], vec![-2, 1]],
            assignment: vec![true, false],
            bit_map: vec![("a".into(), 1, vec![1])],
        };
        w.recheck().expect("satisfied, binding consistent");
        let mut bad = w.clone();
        bad.assignment[0] = false;
        assert!(bad.recheck().is_err());
        let mut lie = w;
        lie.model.assignments[0].1 = 0;
        assert!(lie.recheck().is_err());
    }
}
