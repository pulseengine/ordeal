//! `ordeal-cert/v1` — the stable certificate bundle (issue #91 / TR-025,
//! ordeal half of the FEAT-011 evidence spine).
//!
//! Implements the envelope **pinned on issue #67 and built against by rivet**
//! (rivet#693): a JSON wrapper around the trusted payload —
//! [`Certificate`]'s DIMACS CNF + LRAT proof — adding provenance, an
//! `attests` block tying the certificate to the transform it proves, sha256
//! content addressing, and a `recheck` contract naming the trusted checker.
//! rivet ingests a bundle and treats **"re-checks OK" as a verification
//! link**, not a claimed status.
//!
//! Compiled only with the `cert-bundle` feature (serde_json + sha2): the
//! default build stays dependency-free.
//!
//! v1 scope, per the pinned contract:
//! - **UNSAT** bundles carry the full re-checkable pair (`problem` + `proof`)
//!   inline. (`*_ref` external blobs are in the contract for MB-class proofs;
//!   deferred until a consumer needs them — flagged, not silently dropped.)
//! - **SAT** bundles carry the self-checked model (`verdict: "sat"`), with
//!   the recheck note the contract specifies.
//! - Parsing verifies the content hashes BEFORE returning, and
//!   [`UnsatBundle::recheck`] re-runs the trusted checker — a tampered or
//!   internally-inconsistent bundle never yields a usable [`Certificate`].

use crate::solver::{Certificate, Model};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

/// The `attests` block: what this certificate is evidence *of*.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct Attests {
    /// `"qf_bv_validity"` | `"propositional_consistency"` | `"equivalence"`.
    pub kind: String,
    /// What this proves — free text or a structured reference.
    pub claim: String,
    /// Standard clauses this evidence serves (e.g. `"DO-178C:6.4"`).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub standards: Vec<String>,
}

/// Tool identification for `produced_by` / `checked_by`.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct Tool {
    /// Tool name (`"ordeal"` / `"ordeal-lrat"`).
    pub name: String,
    /// Tool version.
    pub version: String,
}

fn sha256_hex(bytes: &[u8]) -> String {
    let mut h = Sha256::new();
    h.update(bytes);
    let d = h.finalize();
    let mut out = String::with_capacity(64);
    for b in d {
        out.push_str(&format!("{b:02x}"));
    }
    out
}

/// Canonical text form of the CNF for hashing and the `problem` block:
/// DIMACS clause lines (`lit* 0`), one per clause, `\n`-separated.
fn cnf_text(cnf: &[Vec<i32>]) -> String {
    let mut s = String::new();
    for clause in cnf {
        for lit in clause {
            s.push_str(&lit.to_string());
            s.push(' ');
        }
        s.push_str("0\n");
    }
    s
}

#[derive(Serialize, Deserialize)]
struct ProblemBlock {
    encoding: String,
    num_clauses: usize,
    clauses: Vec<Vec<i32>>,
}

#[derive(Serialize, Deserialize)]
struct ProofBlock {
    encoding: String,
    body: String,
}

#[derive(Serialize, Deserialize)]
struct RecheckBlock {
    tool: String,
    min_version: String,
    cmd: String,
    problem_sha256: String,
    proof_sha256: String,
}

#[derive(Serialize, Deserialize)]
struct UnsatEnvelope {
    format: String,
    verdict: String,
    produced_by: Tool,
    checked_by: Tool,
    attests: Attests,
    problem: ProblemBlock,
    proof: ProofBlock,
    recheck: RecheckBlock,
}

/// A parsed, hash-verified `ordeal-cert/v1` UNSAT bundle.
#[derive(Debug)]
pub struct UnsatBundle {
    /// The re-checkable pair, reconstructed.
    pub certificate: Certificate,
    /// What the bundle claims to attest.
    pub attests: Attests,
    /// Producer identification, as recorded.
    pub produced_by: Tool,
}

impl UnsatBundle {
    /// Re-run the trusted checker over the reconstructed pair — the operation
    /// rivet performs to turn this bundle into a verification link.
    pub fn recheck(&self) -> Result<(), crate::solver::CertificateError> {
        self.certificate.recheck()
    }
}

/// Why a bundle failed to parse or verify.
#[derive(Debug)]
pub enum BundleError {
    /// Not valid JSON, or not the expected envelope shape.
    Malformed(String),
    /// The `format` field is not `ordeal-cert/v1`.
    WrongFormat(String),
    /// The `verdict` field does not match the requested reading.
    WrongVerdict(String),
    /// A content hash does not match its payload — the bundle was altered
    /// (or assembled inconsistently) and must not be trusted.
    HashMismatch(&'static str),
    /// An encoding this v1 reader does not support (e.g. `*_ref` external
    /// blobs — in the contract, deferred until a consumer needs them).
    Unsupported(String),
}

impl std::fmt::Display for BundleError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BundleError::Malformed(m) => write!(f, "malformed bundle: {m}"),
            BundleError::WrongFormat(g) => write!(f, "not ordeal-cert/v1 (format: {g})"),
            BundleError::WrongVerdict(g) => write!(f, "unexpected verdict: {g}"),
            BundleError::HashMismatch(which) => {
                write!(
                    f,
                    "content hash mismatch on {which} — bundle not trustworthy"
                )
            }
            BundleError::Unsupported(m) => write!(f, "unsupported by this reader: {m}"),
        }
    }
}

impl std::error::Error for BundleError {}

impl Certificate {
    /// Serialize this checker-validated certificate as an `ordeal-cert/v1`
    /// UNSAT bundle (the pinned #67 contract; inline payloads).
    #[allow(clippy::missing_panics_doc)] // serde_json on our own structs
    pub fn to_cert_v1(&self, attests: &Attests) -> String {
        let problem_text = cnf_text(&self.cnf);
        let proof_text = self.lrat_text().unwrap_or_default().to_string();
        let env = UnsatEnvelope {
            format: "ordeal-cert/v1".into(),
            verdict: "unsat".into(),
            produced_by: Tool {
                name: "ordeal".into(),
                version: env!("CARGO_PKG_VERSION").into(),
            },
            checked_by: Tool {
                name: "ordeal-lrat".into(),
                version: env!("CARGO_PKG_VERSION").into(),
            },
            attests: attests.clone(),
            problem: ProblemBlock {
                encoding: "dimacs-cnf".into(),
                num_clauses: self.cnf.len(),
                clauses: self.cnf.clone(),
            },
            proof: ProofBlock {
                encoding: "lrat".into(),
                body: proof_text.clone(),
            },
            recheck: RecheckBlock {
                tool: "ordeal-lrat".into(),
                min_version: "0.9.0".into(),
                cmd: "ordeal-lrat check <problem> <proof>".into(),
                problem_sha256: sha256_hex(problem_text.as_bytes()),
                proof_sha256: sha256_hex(proof_text.as_bytes()),
            },
        };
        serde_json::to_string_pretty(&env).expect("own-struct serialization")
    }

    /// Parse an `ordeal-cert/v1` UNSAT bundle, verifying the content hashes
    /// before returning. The caller then runs [`UnsatBundle::recheck`] — the
    /// hash check proves integrity, the recheck proves the mathematics.
    pub fn from_cert_v1(json: &str) -> Result<UnsatBundle, BundleError> {
        let env: UnsatEnvelope =
            serde_json::from_str(json).map_err(|e| BundleError::Malformed(e.to_string()))?;
        if env.format != "ordeal-cert/v1" {
            return Err(BundleError::WrongFormat(env.format));
        }
        if env.verdict != "unsat" {
            return Err(BundleError::WrongVerdict(env.verdict));
        }
        if env.problem.encoding != "dimacs-cnf" {
            return Err(BundleError::Unsupported(format!(
                "problem encoding {}",
                env.problem.encoding
            )));
        }
        if env.proof.encoding != "lrat" {
            return Err(BundleError::Unsupported(format!(
                "proof encoding {}",
                env.proof.encoding
            )));
        }
        // Integrity first: both hashes must match their payloads.
        let problem_text = cnf_text(&env.problem.clauses);
        if sha256_hex(problem_text.as_bytes()) != env.recheck.problem_sha256 {
            return Err(BundleError::HashMismatch("problem"));
        }
        if sha256_hex(env.proof.body.as_bytes()) != env.recheck.proof_sha256 {
            return Err(BundleError::HashMismatch("proof"));
        }
        Ok(UnsatBundle {
            certificate: Certificate {
                lrat: env.proof.body.into_bytes(),
                cnf: env.problem.clauses,
            },
            attests: env.attests,
            produced_by: env.produced_by,
        })
    }
}

/// Serialize a SAT verdict's self-checked model as the contract's `sat`
/// bundle shape (the evidence for "config is consistent"; a fully
/// independently re-checkable SAT witness is future work, per the contract).
pub fn model_to_cert_v1(model: &Model, attests: &Attests) -> String {
    #[derive(Serialize)]
    struct SatEnvelope<'a> {
        format: &'a str,
        verdict: &'a str,
        produced_by: Tool,
        attests: &'a Attests,
        model: SatModel,
        recheck: SatRecheck<'a>,
    }
    #[derive(Serialize)]
    struct SatModel {
        encoding: &'static str,
        assignments: Vec<(String, u128)>,
    }
    #[derive(Serialize)]
    struct SatRecheck<'a> {
        note: &'a str,
    }
    let env = SatEnvelope {
        format: "ordeal-cert/v1",
        verdict: "sat",
        produced_by: Tool {
            name: "ordeal".into(),
            version: env!("CARGO_PKG_VERSION").into(),
        },
        attests,
        model: SatModel {
            encoding: "assignment",
            assignments: model.assignments.clone(),
        },
        recheck: SatRecheck {
            note: "model self-checked against all constraints at solve time; \
                   an independently re-checkable SAT witness is future work",
        },
    };
    serde_json::to_string_pretty(&env).expect("own-struct serialization")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cnf::CnfFormula;
    use crate::{CheckResult, Solver};

    fn a_real_certificate() -> Certificate {
        // A feature-model conflict through the propositional front-end —
        // exactly the query class rivet will bundle (rivet#693).
        let f = CnfFormula {
            num_vars: 3,
            clauses: vec![vec![1], vec![-2, -3], vec![2], vec![3]],
        };
        match Solver::check_cnf(&f) {
            CheckResult::Unsat(cert) => cert,
            other => panic!("expected UNSAT, got {other:?}"),
        }
    }

    fn attests() -> Attests {
        Attests {
            kind: "propositional_consistency".into(),
            claim: "variant tls+nomalloc inconsistent with feature model".into(),
            standards: vec!["EU-AI-Act:Art12".into()],
        }
    }

    /// Round trip: emit → parse → hashes verify → the reconstructed pair
    /// re-checks with the trusted checker.
    #[test]
    fn bundle_round_trips_and_rechecks() {
        let cert = a_real_certificate();
        let json = cert.to_cert_v1(&attests());
        let bundle = Certificate::from_cert_v1(&json).expect("bundle must parse");
        assert_eq!(bundle.attests, attests());
        bundle.recheck().expect("reconstructed pair must re-check");
    }

    /// Integrity: tampering with the PROOF body must be caught by the hash
    /// check — before the checker even runs.
    #[test]
    fn tampered_proof_is_rejected_by_hash() {
        let cert = a_real_certificate();
        let json = cert.to_cert_v1(&attests());
        // Flip a digit inside the LRAT body (JSON-safe edit).
        let tampered = json.replacen("\"body\": \"", "\"body\": \"9 ", 1);
        match Certificate::from_cert_v1(&tampered) {
            Err(BundleError::HashMismatch("proof")) => {}
            other => panic!("tampered proof must be a proof-hash mismatch, got {other:?}"),
        }
    }

    /// Integrity: tampering with the PROBLEM (the CNF the proof refutes) must
    /// be caught — otherwise a valid proof could be presented against a
    /// different formula.
    #[test]
    fn tampered_problem_is_rejected_by_hash() {
        let cert = a_real_certificate();
        let json = cert.to_cert_v1(&attests());
        // Mutate structurally (string surgery on pretty-printed JSON is
        // brittle): negate the first literal of the first clause.
        let mut v: serde_json::Value = serde_json::from_str(&json).unwrap();
        let lit = &mut v["problem"]["clauses"][0][0];
        *lit = serde_json::json!(-lit.as_i64().unwrap());
        let tampered = serde_json::to_string(&v).unwrap();
        match Certificate::from_cert_v1(&tampered) {
            Err(BundleError::HashMismatch("problem")) => {}
            other => panic!("tampered problem must be a problem-hash mismatch, got {other:?}"),
        }
    }

    /// A wrong format or verdict is refused, not guessed at.
    #[test]
    fn wrong_format_and_verdict_are_refused() {
        let cert = a_real_certificate();
        let json = cert.to_cert_v1(&attests());
        let wrong_fmt = json.replacen("ordeal-cert/v1", "other-cert/v9", 1);
        assert!(matches!(
            Certificate::from_cert_v1(&wrong_fmt),
            Err(BundleError::WrongFormat(_))
        ));
        let wrong_verdict = json.replacen("\"verdict\": \"unsat\"", "\"verdict\": \"sat\"", 1);
        assert!(matches!(
            Certificate::from_cert_v1(&wrong_verdict),
            Err(BundleError::WrongVerdict(_))
        ));
    }

    /// The SAT shape emits per the contract (spot-check the envelope fields).
    #[test]
    fn sat_model_bundle_has_the_contract_shape() {
        let f = CnfFormula {
            num_vars: 2,
            clauses: vec![vec![-1, 2], vec![1]],
        };
        let model = match Solver::check_cnf(&f) {
            CheckResult::Sat(m) => m,
            other => panic!("expected SAT, got {other:?}"),
        };
        let json = model_to_cert_v1(&model, &attests());
        let v: serde_json::Value = serde_json::from_str(&json).unwrap();
        assert_eq!(v["format"], "ordeal-cert/v1");
        assert_eq!(v["verdict"], "sat");
        assert_eq!(v["model"]["encoding"], "assignment");
        assert!(
            v["recheck"]["note"]
                .as_str()
                .unwrap()
                .contains("self-checked")
        );
    }
}
