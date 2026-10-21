//! `ordeal-cert/v1` — the stable certificate bundle (issue #91 / TR-025,
//! ordeal half of the FEAT-011 evidence spine) — and, since #192 phase 4,
//! `ordeal-cert/v2`: the same envelope plus a `query` block, so a reader
//! certifies the QUERY (`QueryCertificate::from_cert_v2` + `recheck`,
//! through the trusted `ordeal_lrat::check_query`) and not only the CNF.
//! v1 bundles are untouched: `Certificate::to_cert_v1` / `from_cert_v1`
//! emit and read exactly what they did; v2 is opt-in and carries its own
//! `format` string, so a v1 reader refuses it rather than silently
//! ignoring the query.
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

use crate::query::{
    QUERY_ENCODING, QUERY_ENCODING_V2, QueryCertificate, QueryDag, QueryInputs,
    QueryModelRecheckError, QueryRecheckError, QuerySatCertificate, QueryTerm, TERM_ENCODING,
    TermCertificate, TermModelRecheckError, TermRecheckError, TermSatCertificate, bits_from_string,
    bits_string, encoding_supported, node_from_op, node_op,
};
use crate::sha256::sha256_hex;
use crate::solver::{Certificate, Model};
use crate::witness::{assignment_bitstring, bit_map_canonical_text, cnf_text};
use serde::{Deserialize, Serialize};
// Re-exported so 0.20.0 paths (`cert_bundle::SatCertificate`, …) keep working;
// the types live in `crate::witness` (always compiled) since #162 / TR-045.
pub use crate::witness::{SatCertificate, SatRecheckError, WitnessCheckResult};

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
    /// The `format` field is not the one this reader accepts
    /// (`ordeal-cert/v1` for `from_cert_v1`, `ordeal-cert/v2` for
    /// `from_cert_v2`).
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
            BundleError::WrongFormat(g) => write!(f, "unexpected bundle format: {g}"),
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

// ── ordeal-cert/v2: the query-carrying UNSAT bundle (#192 phase 4) ──────

/// The `query` block of an `ordeal-cert/v2` UNSAT bundle: the lowered term
/// DAG the certificate refutes, in the [`QUERY_ENCODING`] spelling, with
/// its own content hash. Everything the trusted `ordeal_lrat::check_query`
/// consumes, nothing else.
#[derive(Serialize, Deserialize)]
struct QueryBlock {
    encoding: String,
    num_nodes: usize,
    /// `["op", arg, …]` per node (see `query::node_op`).
    nodes: Vec<serde_json::Value>,
    /// The constant table as a `0`/`1` string.
    bits: String,
    roots: Vec<usize>,
    hints: Vec<usize>,
    /// `sha256` of `QueryDag::canonical_text`.
    sha256: String,
}

#[derive(Serialize, Deserialize)]
struct RecheckBlockV2 {
    tool: String,
    min_version: String,
    cmd: String,
    problem_sha256: String,
    proof_sha256: String,
}

/// The v2 envelope: v1's fields plus `query`. Field order is the v1 order
/// with `query` after `proof`, so a v2 bundle reads as a v1 bundle with
/// one more block and a different `format`.
#[derive(Serialize, Deserialize)]
struct UnsatEnvelopeV2 {
    format: String,
    verdict: String,
    produced_by: Tool,
    checked_by: Tool,
    attests: Attests,
    problem: ProblemBlock,
    proof: ProofBlock,
    query: QueryBlock,
    recheck: RecheckBlockV2,
}

/// A parsed, hash-verified `ordeal-cert/v2` UNSAT bundle: the v1 pair plus
/// the query it refutes.
#[derive(Debug)]
pub struct QueryBundle {
    /// The certificate with its query, reconstructed.
    pub certificate: QueryCertificate,
    /// What the bundle claims to attest.
    pub attests: Attests,
    /// Producer identification, as recorded.
    pub produced_by: Tool,
}

impl QueryBundle {
    /// Re-run the trusted QUERY re-check (`ordeal_lrat::check_query`) over
    /// the reconstructed DAG and proof — the operation a v2-aware consumer
    /// performs to turn this bundle into a verification link about the
    /// query. The v1 (CNF-level) recheck stays available as
    /// `certificate.certificate.recheck()`.
    pub fn recheck(&self) -> Result<(), QueryRecheckError> {
        self.certificate.recheck()
    }
}

fn node_to_json(node: &ordeal_lrat::blast_kernel::DagNode) -> serde_json::Value {
    let (op, args) = node_op(node);
    let mut v = Vec::with_capacity(1 + args.len());
    v.push(serde_json::Value::String(op.into()));
    v.extend(args.into_iter().map(serde_json::Value::from));
    serde_json::Value::Array(v)
}

fn node_from_json(
    v: &serde_json::Value,
) -> Result<ordeal_lrat::blast_kernel::DagNode, BundleError> {
    let malformed = || BundleError::Malformed(format!("query node {v} is not [\"op\", arg…]"));
    let items = v.as_array().ok_or_else(malformed)?;
    let op = items
        .first()
        .and_then(|o| o.as_str())
        .ok_or_else(malformed)?;
    let mut args = Vec::with_capacity(items.len().saturating_sub(1));
    for a in &items[1..] {
        let n = a.as_u64().ok_or_else(malformed)?;
        args.push(usize::try_from(n).map_err(|_| malformed())?);
    }
    node_from_op(op, &args).ok_or_else(malformed)
}

/// Decode a `query` block into the DAG, verifying its node count, its
/// encoding-tag discipline and its content hash (under the DECLARED tag).
/// Shared by the UNSAT and the SAT v2 readers.
fn query_from_block(block: QueryBlock) -> Result<QueryDag, BundleError> {
    if !encoding_supported(&block.encoding) {
        return Err(BundleError::Unsupported(format!(
            "query encoding {}",
            block.encoding
        )));
    }
    let mut nodes = Vec::with_capacity(block.nodes.len());
    for n in &block.nodes {
        nodes.push(node_from_json(n)?);
    }
    if nodes.len() != block.num_nodes {
        return Err(BundleError::Malformed(format!(
            "query.num_nodes {} but {} nodes",
            block.num_nodes,
            nodes.len()
        )));
    }
    let bits = bits_from_string(&block.bits).ok_or_else(|| {
        BundleError::Malformed("query bits contain a character other than '0'/'1'".into())
    })?;
    let query = QueryDag {
        nodes,
        bits,
        roots: block.roots,
        hints: block.hints,
    };
    // A block tagged `ordeal-dag/v1` must not carry a node kind that
    // tag cannot express (a v0.27.0 reader would have refused the node;
    // this reader refuses the lie about the tag).
    if block.encoding == QUERY_ENCODING && query.has_derived() {
        return Err(BundleError::Malformed(format!(
            "query encoding {} carries a derived-op node ({} is required)",
            QUERY_ENCODING, QUERY_ENCODING_V2
        )));
    }
    // The hash covers the DECLARED tag.
    if query.sha256_tagged(&block.encoding) != block.sha256 {
        return Err(BundleError::HashMismatch("query"));
    }
    Ok(query)
}

/// The `query` block as emitted (the lowest tag that expresses the DAG,
/// #192 phase 5: `ordeal-dag/v1` unless a derived-op node is present).
fn query_to_block(q: &QueryDag) -> QueryBlock {
    QueryBlock {
        encoding: q.encoding().into(),
        num_nodes: q.nodes.len(),
        nodes: q.nodes.iter().map(node_to_json).collect(),
        bits: bits_string(&q.bits),
        roots: q.roots.clone(),
        hints: q.hints.clone(),
        sha256: q.sha256(),
    }
}

impl QueryCertificate {
    /// Serialize this trusted-rechecked certificate as an `ordeal-cert/v2`
    /// UNSAT bundle: the v1 envelope (same `problem` and `proof` blocks,
    /// same hashes) plus the `query` block, `format: "ordeal-cert/v2"`.
    /// A v1 reader rejects it by format (opt-in, no silent downgrade);
    /// `Certificate::to_cert_v1` on `self.certificate` still produces the
    /// v1 bundle unchanged.
    #[allow(clippy::missing_panics_doc)] // serde_json on our own structs
    pub fn to_cert_v2(&self, attests: &Attests) -> String {
        let cert = &self.certificate;
        let problem_text = cnf_text(&cert.cnf);
        let proof_text = cert.lrat_text().unwrap_or_default().to_string();
        let q = &self.query;
        let env = UnsatEnvelopeV2 {
            format: "ordeal-cert/v2".into(),
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
                num_clauses: cert.cnf.len(),
                clauses: cert.cnf.clone(),
            },
            proof: ProofBlock {
                encoding: "lrat".into(),
                body: proof_text.clone(),
            },
            query: query_to_block(q),
            recheck: RecheckBlockV2 {
                tool: "ordeal-lrat".into(),
                // A derived-op node needs the phase-5 `check_query`.
                min_version: if q.has_derived() { "0.28.0" } else { "0.27.0" }.into(),
                cmd: "ordeal_lrat::check_query(query.nodes, query.bits, query.roots, \
                      query.hints, proof.body) == Ok(problem.clauses)"
                    .into(),
                problem_sha256: sha256_hex(problem_text.as_bytes()),
                proof_sha256: sha256_hex(proof_text.as_bytes()),
            },
        };
        serde_json::to_string_pretty(&env).expect("own-struct serialization")
    }

    /// Parse an `ordeal-cert/v2` UNSAT bundle, verifying all three content
    /// hashes (problem, proof, query) BEFORE returning. The caller then
    /// runs [`QueryBundle::recheck`] — the hash check proves integrity,
    /// the recheck proves the mathematics about the query. A v1 bundle
    /// (no `query` block) is [`BundleError::WrongFormat`]: read it with
    /// `Certificate::from_cert_v1`.
    pub fn from_cert_v2(json: &str) -> Result<QueryBundle, BundleError> {
        // Format first, so a v1 bundle is reported as such rather than as
        // "missing field query".
        let head: serde_json::Value =
            serde_json::from_str(json).map_err(|e| BundleError::Malformed(e.to_string()))?;
        match head.get("format").and_then(|f| f.as_str()) {
            Some("ordeal-cert/v2") => {}
            Some(other) => return Err(BundleError::WrongFormat(other.into())),
            None => return Err(BundleError::Malformed("missing format".into())),
        }
        // Verdict next, before the envelope: a v2 SAT bundle (#192 phase
        // 6, different blocks) is reported as the wrong verdict rather
        // than as "missing field proof".
        match head.get("verdict").and_then(|f| f.as_str()) {
            Some("unsat") => {}
            Some(other) => return Err(BundleError::WrongVerdict(other.into())),
            None => return Err(BundleError::Malformed("missing verdict".into())),
        }
        let env: UnsatEnvelopeV2 =
            serde_json::from_str(json).map_err(|e| BundleError::Malformed(e.to_string()))?;
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
        if !encoding_supported(&env.query.encoding) {
            return Err(BundleError::Unsupported(format!(
                "query encoding {}",
                env.query.encoding
            )));
        }
        // Integrity first: all three hashes must match their payloads.
        let problem_text = cnf_text(&env.problem.clauses);
        if sha256_hex(problem_text.as_bytes()) != env.recheck.problem_sha256 {
            return Err(BundleError::HashMismatch("problem"));
        }
        if sha256_hex(env.proof.body.as_bytes()) != env.recheck.proof_sha256 {
            return Err(BundleError::HashMismatch("proof"));
        }
        let query = query_from_block(env.query)?;
        Ok(QueryBundle {
            certificate: QueryCertificate {
                certificate: Certificate {
                    lrat: env.proof.body.into_bytes(),
                    cnf: env.problem.clauses,
                },
                query,
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

impl SatCertificate {
    /// Serialize as an `ordeal-cert/v1` SAT bundle carrying the OPTIONAL
    /// `witness` block (verified tolerable by released rivet readers —
    /// rivet 0.32.0 reports an unknown field as INFO and passes; see
    /// docs/design/sat-witness.md). Content sha256s cover the clause
    /// text, the assignment bitstring, and the canonical bit-map text.
    #[allow(clippy::missing_panics_doc)] // serde_json on our own structs
    pub fn to_cert_v1(&self, attests: &Attests) -> String {
        let problem_text = cnf_text(&self.cnf);
        let assignment_text = assignment_bitstring(&self.assignment);
        let bit_map_text = bit_map_canonical_text(&self.bit_map);
        let env = SatWitnessEnvelope {
            format: "ordeal-cert/v1".into(),
            verdict: "sat".into(),
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
            model: SatModelBlock {
                encoding: "assignments".into(),
                assignments: self.model.assignments.clone(),
            },
            witness: WitnessBlock {
                encoding: "bitstring-lsb-var1".into(),
                assignment: assignment_text.clone(),
                bit_map: self
                    .bit_map
                    .iter()
                    .map(|(name, width, bits)| BitMapEntry {
                        name: name.clone(),
                        width: *width,
                        bits: bits.clone(),
                    })
                    .collect(),
                assignment_sha256: sha256_hex(assignment_text.as_bytes()),
                bit_map_sha256: sha256_hex(bit_map_text.as_bytes()),
            },
            recheck: SatWitnessRecheck {
                tool: "ordeal-lrat".into(),
                min_version: env!("CARGO_PKG_VERSION").into(),
                cmd: "ordeal_lrat::check_sat(problem, witness.assignment) + \
                      ordeal_lrat::check_binding per model binding"
                    .into(),
                problem_sha256: sha256_hex(problem_text.as_bytes()),
            },
        };
        serde_json::to_string_pretty(&env).expect("own-struct serialization")
    }

    /// Parse a witness-carrying `ordeal-cert/v1` SAT bundle, verifying
    /// all three content hashes BEFORE returning (integrity before
    /// mathematics — the caller then runs [`SatCertificate::recheck`]).
    /// A SAT bundle without a `witness` block is the legacy self-checked
    /// shape and is reported as [`BundleError::Unsupported`].
    pub fn from_cert_v1(json: &str) -> Result<SatCertificate, BundleError> {
        let env: SatWitnessEnvelopeIn =
            serde_json::from_str(json).map_err(|e| BundleError::Malformed(e.to_string()))?;
        if env.format != "ordeal-cert/v1" {
            return Err(BundleError::WrongFormat(env.format));
        }
        if env.verdict != "sat" {
            return Err(BundleError::WrongVerdict(env.verdict));
        }
        let Some(witness) = env.witness else {
            return Err(BundleError::Unsupported(
                "sat bundle without a witness block (legacy self-checked shape)".into(),
            ));
        };
        sat_witness_from_blocks(env.problem, env.model, witness, &env.recheck)
    }

    /// The `witness` block as emitted (and the texts its hashes cover).
    fn witness_block(&self) -> WitnessBlock {
        let assignment_text = assignment_bitstring(&self.assignment);
        let bit_map_text = bit_map_canonical_text(&self.bit_map);
        WitnessBlock {
            encoding: "bitstring-lsb-var1".into(),
            assignment: assignment_text.clone(),
            bit_map: self
                .bit_map
                .iter()
                .map(|(name, width, bits)| BitMapEntry {
                    name: name.clone(),
                    width: *width,
                    bits: bits.clone(),
                })
                .collect(),
            assignment_sha256: sha256_hex(assignment_text.as_bytes()),
            bit_map_sha256: sha256_hex(bit_map_text.as_bytes()),
        }
    }
}

/// Decode the `problem` / `model` / `witness` blocks of a SAT bundle into
/// the v1 witness, verifying the three content hashes BEFORE returning.
/// Shared by the v1 and the v2 (#192 phase 6) SAT readers.
fn sat_witness_from_blocks(
    problem: ProblemBlock,
    model: SatModelBlock,
    witness: WitnessBlock,
    recheck: &SatWitnessRecheck,
) -> Result<SatCertificate, BundleError> {
    if problem.encoding != "dimacs-cnf" {
        return Err(BundleError::Unsupported(format!(
            "problem encoding {}",
            problem.encoding
        )));
    }
    if witness.encoding != "bitstring-lsb-var1" {
        return Err(BundleError::Unsupported(format!(
            "witness encoding {}",
            witness.encoding
        )));
    }
    // Integrity first: all three hashes must match their payloads.
    let problem_text = cnf_text(&problem.clauses);
    if sha256_hex(problem_text.as_bytes()) != recheck.problem_sha256 {
        return Err(BundleError::HashMismatch("problem"));
    }
    if sha256_hex(witness.assignment.as_bytes()) != witness.assignment_sha256 {
        return Err(BundleError::HashMismatch("witness-assignment"));
    }
    let bit_map: Vec<(String, u32, Vec<i32>)> = witness
        .bit_map
        .iter()
        .map(|e| (e.name.clone(), e.width, e.bits.clone()))
        .collect();
    if sha256_hex(bit_map_canonical_text(&bit_map).as_bytes()) != witness.bit_map_sha256 {
        return Err(BundleError::HashMismatch("witness-bit-map"));
    }
    let mut assignment = Vec::with_capacity(witness.assignment.len());
    for c in witness.assignment.chars() {
        match c {
            '0' => assignment.push(false),
            '1' => assignment.push(true),
            other => {
                return Err(BundleError::Malformed(format!(
                    "witness assignment contains '{other}' (expected '0'/'1')"
                )));
            }
        }
    }
    Ok(SatCertificate {
        model: Model {
            assignments: model.assignments,
        },
        cnf: problem.clauses,
        assignment,
        bit_map,
    })
}

// ── ordeal-cert/v2: the query-carrying SAT bundle (#192 phase 6) ────────

/// The `inputs` block of an `ordeal-cert/v2` SAT bundle: the DAG's
/// primary-input assignment the trusted `ordeal_lrat::check_query_model`
/// consumes, the model-to-node map a reader confirms the model with, and
/// the block's content hash (`QueryInputs::canonical_text`).
#[derive(Serialize, Deserialize)]
struct InputsBlock {
    encoding: String,
    /// The assignment as a `0`/`1` string, input 0 first.
    bits: String,
    vars: Vec<InputVarEntry>,
    sha256: String,
}

#[derive(Serialize, Deserialize)]
struct InputVarEntry {
    name: String,
    width: u32,
    node: usize,
}

/// The v2 SAT envelope: the v1 witness envelope's fields plus `query` and
/// `inputs` after `witness`, so it reads as the v1 bundle with two more
/// blocks and a different `format`.
#[derive(Serialize)]
struct SatEnvelopeV2 {
    format: String,
    verdict: String,
    produced_by: Tool,
    checked_by: Tool,
    attests: Attests,
    problem: ProblemBlock,
    model: SatModelBlock,
    witness: WitnessBlock,
    query: QueryBlock,
    inputs: InputsBlock,
    recheck: SatWitnessRecheck,
}

#[derive(Deserialize)]
struct SatEnvelopeV2In {
    format: String,
    verdict: String,
    attests: Attests,
    produced_by: Tool,
    problem: ProblemBlock,
    model: SatModelBlock,
    witness: WitnessBlock,
    query: QueryBlock,
    inputs: InputsBlock,
    recheck: SatWitnessRecheck,
}

/// A parsed, hash-verified `ordeal-cert/v2` SAT bundle: the v1 witness
/// plus the query it satisfies and the DAG's input assignment.
#[derive(Debug)]
pub struct QuerySatBundle {
    /// The witness with its query and inputs, reconstructed.
    pub certificate: QuerySatCertificate,
    /// What the bundle claims to attest.
    pub attests: Attests,
    /// Producer identification, as recorded.
    pub produced_by: Tool,
}

impl QuerySatBundle {
    /// Re-run the trusted MODEL re-check (`ordeal_lrat::check_query_model`)
    /// over the reconstructed DAG and inputs — the operation a v2-aware
    /// consumer performs to turn this bundle into a verification link about
    /// the query being satisfiable. The v1 (CNF-level) recheck stays
    /// available as `certificate.witness.recheck()`.
    pub fn recheck(&self) -> Result<(), QueryModelRecheckError> {
        self.certificate.recheck()
    }
}

impl QuerySatCertificate {
    /// Serialize this trusted-rechecked certificate as an `ordeal-cert/v2`
    /// SAT bundle: the v1 witness envelope (same `problem`, `model` and
    /// `witness` blocks, same hashes) plus the `query` and `inputs`
    /// blocks, `format: "ordeal-cert/v2"`. A v1 reader rejects it by
    /// format (opt-in, no silent downgrade); `SatCertificate::to_cert_v1`
    /// on `self.witness` still produces the v1 bundle unchanged.
    #[allow(clippy::missing_panics_doc)] // serde_json on our own structs
    pub fn to_cert_v2(&self, attests: &Attests) -> String {
        let w = &self.witness;
        let problem_text = cnf_text(&w.cnf);
        let env = SatEnvelopeV2 {
            format: "ordeal-cert/v2".into(),
            verdict: "sat".into(),
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
                num_clauses: w.cnf.len(),
                clauses: w.cnf.clone(),
            },
            model: SatModelBlock {
                encoding: "assignments".into(),
                assignments: w.model.assignments.clone(),
            },
            witness: w.witness_block(),
            query: query_to_block(&self.query),
            inputs: InputsBlock {
                encoding: crate::query::INPUTS_ENCODING.into(),
                bits: bits_string(&self.inputs.bits),
                vars: self
                    .inputs
                    .vars
                    .iter()
                    .map(|(name, width, node)| InputVarEntry {
                        name: name.clone(),
                        width: *width,
                        node: *node,
                    })
                    .collect(),
                sha256: self.inputs.sha256(),
            },
            recheck: SatWitnessRecheck {
                tool: "ordeal-lrat".into(),
                min_version: "0.29.0".into(),
                cmd: "ordeal_lrat::check_sat(problem, witness.assignment) + \
                      ordeal_lrat::check_binding per model binding + \
                      ordeal_lrat::check_query_model(query.nodes, query.bits, query.roots, \
                      inputs.bits) == Ok(())"
                    .into(),
                problem_sha256: sha256_hex(problem_text.as_bytes()),
            },
        };
        serde_json::to_string_pretty(&env).expect("own-struct serialization")
    }

    /// Parse an `ordeal-cert/v2` SAT bundle, verifying all five content
    /// hashes (problem, witness assignment, bit map, query, inputs) BEFORE
    /// returning. The caller then runs [`QuerySatBundle::recheck`] — the
    /// hash check proves integrity, the recheck proves the mathematics
    /// about the query. A v1 bundle is [`BundleError::WrongFormat`]: read
    /// it with `SatCertificate::from_cert_v1`; an UNSAT v2 bundle is
    /// [`BundleError::WrongVerdict`]: read it with
    /// `QueryCertificate::from_cert_v2`.
    pub fn from_cert_v2(json: &str) -> Result<QuerySatBundle, BundleError> {
        let head: serde_json::Value =
            serde_json::from_str(json).map_err(|e| BundleError::Malformed(e.to_string()))?;
        match head.get("format").and_then(|f| f.as_str()) {
            Some("ordeal-cert/v2") => {}
            Some(other) => return Err(BundleError::WrongFormat(other.into())),
            None => return Err(BundleError::Malformed("missing format".into())),
        }
        match head.get("verdict").and_then(|f| f.as_str()) {
            Some("sat") => {}
            Some(other) => return Err(BundleError::WrongVerdict(other.into())),
            None => return Err(BundleError::Malformed("missing verdict".into())),
        }
        let env: SatEnvelopeV2In =
            serde_json::from_str(json).map_err(|e| BundleError::Malformed(e.to_string()))?;
        if env.format != "ordeal-cert/v2" {
            return Err(BundleError::WrongFormat(env.format));
        }
        if env.verdict != "sat" {
            return Err(BundleError::WrongVerdict(env.verdict));
        }
        let witness = sat_witness_from_blocks(env.problem, env.model, env.witness, &env.recheck)?;
        let query = query_from_block(env.query)?;
        if env.inputs.encoding != crate::query::INPUTS_ENCODING {
            return Err(BundleError::Unsupported(format!(
                "inputs encoding {}",
                env.inputs.encoding
            )));
        }
        let bits = bits_from_string(&env.inputs.bits).ok_or_else(|| {
            BundleError::Malformed("inputs bits contain a character other than '0'/'1'".into())
        })?;
        let inputs = QueryInputs {
            bits,
            vars: env
                .inputs
                .vars
                .iter()
                .map(|e| (e.name.clone(), e.width, e.node))
                .collect(),
        };
        if inputs.sha256() != env.inputs.sha256 {
            return Err(BundleError::HashMismatch("inputs"));
        }
        Ok(QuerySatBundle {
            certificate: QuerySatCertificate {
                witness,
                query,
                inputs,
            },
            attests: env.attests,
            produced_by: env.produced_by,
        })
    }
}

#[derive(Serialize)]
struct SatWitnessEnvelope {
    format: String,
    verdict: String,
    produced_by: Tool,
    checked_by: Tool,
    attests: Attests,
    problem: ProblemBlock,
    model: SatModelBlock,
    witness: WitnessBlock,
    recheck: SatWitnessRecheck,
}

#[derive(Deserialize)]
struct SatWitnessEnvelopeIn {
    format: String,
    verdict: String,
    problem: ProblemBlock,
    model: SatModelBlock,
    witness: Option<WitnessBlock>,
    recheck: SatWitnessRecheck,
}

#[derive(Serialize, Deserialize)]
struct SatModelBlock {
    encoding: String,
    assignments: Vec<(String, u128)>,
}

#[derive(Serialize, Deserialize)]
struct WitnessBlock {
    encoding: String,
    assignment: String,
    bit_map: Vec<BitMapEntry>,
    assignment_sha256: String,
    bit_map_sha256: String,
}

#[derive(Serialize, Deserialize)]
struct BitMapEntry {
    name: String,
    width: u32,
    bits: Vec<i32>,
}

#[derive(Serialize, Deserialize)]
struct SatWitnessRecheck {
    tool: String,
    min_version: String,
    cmd: String,
    problem_sha256: String,
}

// ── ordeal-cert/v3: the term-carrying bundles (#192 phase 7) ─────────────

/// The `term` block of an `ordeal-cert/v3` bundle (`QueryTerm`): the
/// caller's assertions flattened as asked, in the `query` block's node
/// spelling, the variable names, the untrusted map to the `query` block's
/// nodes, and the block's content hash (`QueryTerm::canonical_text`).
#[derive(Serialize, Deserialize)]
struct TermBlock {
    encoding: String,
    num_nodes: usize,
    /// `["op", arg, …]` per node (see `query::node_op`).
    nodes: Vec<serde_json::Value>,
    bits: String,
    roots: Vec<usize>,
    vars: Vec<InputVarEntry>,
    /// Term node → `query` node; `usize::MAX` for a node with no image.
    map: Vec<usize>,
    sha256: String,
}

fn term_to_block(t: &QueryTerm) -> TermBlock {
    TermBlock {
        encoding: t.encoding().into(),
        num_nodes: t.nodes.len(),
        nodes: t.nodes.iter().map(node_to_json).collect(),
        bits: bits_string(&t.bits),
        roots: t.roots.clone(),
        vars: t
            .vars
            .iter()
            .map(|(name, width, node)| InputVarEntry {
                name: name.clone(),
                width: *width,
                node: *node,
            })
            .collect(),
        map: t.map.clone(),
        sha256: t.sha256(),
    }
}

fn term_from_block(block: TermBlock) -> Result<QueryTerm, BundleError> {
    let shared = match block.encoding.as_str() {
        TERM_ENCODING => false,
        crate::query::TERM_ENCODING_V2 => true,
        other => {
            return Err(BundleError::Unsupported(format!("term encoding {other}")));
        }
    };
    let mut nodes = Vec::with_capacity(block.nodes.len());
    for n in &block.nodes {
        nodes.push(node_from_json(n)?);
    }
    if nodes.len() != block.num_nodes {
        return Err(BundleError::Malformed(format!(
            "term.num_nodes {} but {} nodes",
            block.num_nodes,
            nodes.len()
        )));
    }
    let bits = bits_from_string(&block.bits).ok_or_else(|| {
        BundleError::Malformed("term bits contain a character other than '0'/'1'".into())
    })?;
    let term = QueryTerm {
        nodes,
        bits,
        roots: block.roots,
        vars: block
            .vars
            .iter()
            .map(|v| (v.name.clone(), v.width, v.node))
            .collect(),
        map: block.map,
        shared,
    };
    if term.sha256() != block.sha256 {
        return Err(BundleError::HashMismatch("term"));
    }
    Ok(term)
}

/// The v3 UNSAT envelope: v2's fields plus `term` after `query`.
#[derive(Serialize, Deserialize)]
struct UnsatEnvelopeV3 {
    format: String,
    verdict: String,
    produced_by: Tool,
    checked_by: Tool,
    attests: Attests,
    problem: ProblemBlock,
    proof: ProofBlock,
    query: QueryBlock,
    term: TermBlock,
    recheck: RecheckBlockV2,
}

/// A parsed, hash-verified `ordeal-cert/v3` UNSAT bundle: the v2 bundle
/// plus the term the query was lowered from.
#[derive(Debug)]
pub struct TermBundle {
    /// The certificate with its query and term, reconstructed.
    pub certificate: TermCertificate,
    /// What the bundle claims to attest.
    pub attests: Attests,
    /// Producer identification, as recorded.
    pub produced_by: Tool,
}

impl TermBundle {
    /// Re-run the trusted TERM re-check (`ordeal_lrat::check_term_dag`,
    /// then `ordeal_lrat::check_query`) over the reconstructed term, map,
    /// DAG and proof — the operation a v3-aware consumer performs to turn
    /// this bundle into a verification link about the TERM. The v2 recheck
    /// stays available as `certificate.query.recheck()`.
    pub fn recheck(&self) -> Result<(), TermRecheckError> {
        self.certificate.recheck()
    }
}

/// The `recheck.cmd` of a v3 bundle.
const V3_UNSAT_CMD: &str = "ordeal_lrat::check_term_dag(term.nodes, term.bits, term.roots, term.map, \
     query.nodes, query.bits, query.roots) == Ok(()) && \
     ordeal_lrat::check_query(query.nodes, query.bits, query.roots, query.hints, proof.body) \
     == Ok(problem.clauses)";

/// Readers from this version on decode `ordeal-cert/v3`.
const V3_MIN_VERSION: &str = "0.31.0";

impl TermCertificate {
    /// Serialize this trusted-rechecked certificate as an `ordeal-cert/v3`
    /// UNSAT bundle: the v2 envelope (same `problem`, `proof` and `query`
    /// blocks, same hashes) plus the `term` block, `format:
    /// "ordeal-cert/v3"`. A v1 or v2 reader rejects it by format (no silent
    /// downgrade); `to_cert_v2` on `self.query` still produces the v2
    /// bundle unchanged.
    #[allow(clippy::missing_panics_doc)] // serde_json on our own structs
    pub fn to_cert_v3(&self, attests: &Attests) -> String {
        let cert = &self.query.certificate;
        let problem_text = cnf_text(&cert.cnf);
        let proof_text = cert.lrat_text().unwrap_or_default().to_string();
        let env = UnsatEnvelopeV3 {
            format: "ordeal-cert/v3".into(),
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
                num_clauses: cert.cnf.len(),
                clauses: cert.cnf.clone(),
            },
            proof: ProofBlock {
                encoding: "lrat".into(),
                body: proof_text.clone(),
            },
            query: query_to_block(&self.query.query),
            term: term_to_block(&self.term),
            recheck: RecheckBlockV2 {
                tool: "ordeal-lrat".into(),
                min_version: V3_MIN_VERSION.into(),
                cmd: V3_UNSAT_CMD.into(),
                problem_sha256: sha256_hex(problem_text.as_bytes()),
                proof_sha256: sha256_hex(proof_text.as_bytes()),
            },
        };
        serde_json::to_string_pretty(&env).expect("own-struct serialization")
    }

    /// Parse an `ordeal-cert/v3` UNSAT bundle, verifying all four content
    /// hashes (problem, proof, query, term) BEFORE returning. The caller
    /// then runs [`TermBundle::recheck`]. A v1 or v2 bundle is
    /// [`BundleError::WrongFormat`]: read it with its own reader.
    pub fn from_cert_v3(json: &str) -> Result<TermBundle, BundleError> {
        let head: serde_json::Value =
            serde_json::from_str(json).map_err(|e| BundleError::Malformed(e.to_string()))?;
        match head.get("format").and_then(|f| f.as_str()) {
            Some("ordeal-cert/v3") => {}
            Some(other) => return Err(BundleError::WrongFormat(other.into())),
            None => return Err(BundleError::Malformed("missing format".into())),
        }
        match head.get("verdict").and_then(|f| f.as_str()) {
            Some("unsat") => {}
            Some(other) => return Err(BundleError::WrongVerdict(other.into())),
            None => return Err(BundleError::Malformed("missing verdict".into())),
        }
        let env: UnsatEnvelopeV3 =
            serde_json::from_str(json).map_err(|e| BundleError::Malformed(e.to_string()))?;
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
        if !encoding_supported(&env.query.encoding) {
            return Err(BundleError::Unsupported(format!(
                "query encoding {}",
                env.query.encoding
            )));
        }
        let problem_text = cnf_text(&env.problem.clauses);
        if sha256_hex(problem_text.as_bytes()) != env.recheck.problem_sha256 {
            return Err(BundleError::HashMismatch("problem"));
        }
        if sha256_hex(env.proof.body.as_bytes()) != env.recheck.proof_sha256 {
            return Err(BundleError::HashMismatch("proof"));
        }
        let query = query_from_block(env.query)?;
        let term = term_from_block(env.term)?;
        Ok(TermBundle {
            certificate: TermCertificate {
                query: QueryCertificate {
                    certificate: Certificate {
                        lrat: env.proof.body.into_bytes(),
                        cnf: env.problem.clauses,
                    },
                    query,
                },
                term,
            },
            attests: env.attests,
            produced_by: env.produced_by,
        })
    }
}

/// The v3 SAT envelope: v2's fields plus `term` after `inputs`.
#[derive(Serialize)]
struct SatEnvelopeV3 {
    format: String,
    verdict: String,
    produced_by: Tool,
    checked_by: Tool,
    attests: Attests,
    problem: ProblemBlock,
    model: SatModelBlock,
    witness: WitnessBlock,
    query: QueryBlock,
    inputs: InputsBlock,
    term: TermBlock,
    recheck: SatWitnessRecheck,
}

#[derive(Deserialize)]
struct SatEnvelopeV3In {
    format: String,
    verdict: String,
    attests: Attests,
    produced_by: Tool,
    problem: ProblemBlock,
    model: SatModelBlock,
    witness: WitnessBlock,
    query: QueryBlock,
    inputs: InputsBlock,
    term: TermBlock,
    recheck: SatWitnessRecheck,
}

/// A parsed, hash-verified `ordeal-cert/v3` SAT bundle: the v2 SAT bundle
/// plus the term the query was lowered from.
#[derive(Debug)]
pub struct TermSatBundle {
    /// The witness with its query, inputs and term, reconstructed.
    pub certificate: TermSatCertificate,
    /// What the bundle claims to attest.
    pub attests: Attests,
    /// Producer identification, as recorded.
    pub produced_by: Tool,
}

impl TermSatBundle {
    /// Re-run the trusted TERM re-check: `check_term_dag`, the v2 model
    /// recheck, and every model binding through the term's variable map
    /// (`var_offset` / `check_input_value`).
    pub fn recheck(&self) -> Result<(), TermModelRecheckError> {
        self.certificate.recheck()
    }
}

fn inputs_from_block(block: InputsBlock) -> Result<QueryInputs, BundleError> {
    if block.encoding != crate::query::INPUTS_ENCODING {
        return Err(BundleError::Unsupported(format!(
            "inputs encoding {}",
            block.encoding
        )));
    }
    let bits = bits_from_string(&block.bits).ok_or_else(|| {
        BundleError::Malformed("inputs bits contain a character other than '0'/'1'".into())
    })?;
    let inputs = QueryInputs {
        bits,
        vars: block
            .vars
            .iter()
            .map(|v| (v.name.clone(), v.width, v.node))
            .collect(),
    };
    if inputs.sha256() != block.sha256 {
        return Err(BundleError::HashMismatch("inputs"));
    }
    Ok(inputs)
}

impl TermSatCertificate {
    /// Serialize this trusted-rechecked certificate as an `ordeal-cert/v3`
    /// SAT bundle: the v2 SAT envelope (same blocks, same hashes) plus the
    /// `term` block, `format: "ordeal-cert/v3"`.
    #[allow(clippy::missing_panics_doc)] // serde_json on our own structs
    pub fn to_cert_v3(&self, attests: &Attests) -> String {
        let w = &self.query.witness;
        let problem_text = cnf_text(&w.cnf);
        let env = SatEnvelopeV3 {
            format: "ordeal-cert/v3".into(),
            verdict: "sat".into(),
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
                num_clauses: w.cnf.len(),
                clauses: w.cnf.clone(),
            },
            model: SatModelBlock {
                encoding: "assignments".into(),
                assignments: w.model.assignments.clone(),
            },
            witness: w.witness_block(),
            query: query_to_block(&self.query.query),
            inputs: InputsBlock {
                encoding: crate::query::INPUTS_ENCODING.into(),
                bits: bits_string(&self.query.inputs.bits),
                vars: self
                    .query
                    .inputs
                    .vars
                    .iter()
                    .map(|(name, width, node)| InputVarEntry {
                        name: name.clone(),
                        width: *width,
                        node: *node,
                    })
                    .collect(),
                sha256: self.query.inputs.sha256(),
            },
            term: term_to_block(&self.term),
            recheck: SatWitnessRecheck {
                tool: "ordeal-lrat".into(),
                min_version: V3_MIN_VERSION.into(),
                cmd: "ordeal_lrat::check_term_dag(term.nodes, term.bits, term.roots, term.map, \
                      query.nodes, query.bits, query.roots) == Ok(()) + \
                      ordeal_lrat::check_sat(problem, witness.assignment) + \
                      ordeal_lrat::check_binding per model binding + \
                      ordeal_lrat::check_query_model(query.nodes, query.bits, query.roots, \
                      inputs.bits) == Ok(()) + ordeal_lrat::check_input_value(inputs.bits, \
                      ordeal_lrat::var_offset(query.nodes, term.map[term.vars[name].node]), \
                      width, value) per model binding"
                    .into(),
                problem_sha256: sha256_hex(problem_text.as_bytes()),
            },
        };
        serde_json::to_string_pretty(&env).expect("own-struct serialization")
    }

    /// Parse an `ordeal-cert/v3` SAT bundle, verifying all six content
    /// hashes (problem, witness assignment, bit map, query, inputs, term)
    /// BEFORE returning. The caller then runs [`TermSatBundle::recheck`].
    pub fn from_cert_v3(json: &str) -> Result<TermSatBundle, BundleError> {
        let head: serde_json::Value =
            serde_json::from_str(json).map_err(|e| BundleError::Malformed(e.to_string()))?;
        match head.get("format").and_then(|f| f.as_str()) {
            Some("ordeal-cert/v3") => {}
            Some(other) => return Err(BundleError::WrongFormat(other.into())),
            None => return Err(BundleError::Malformed("missing format".into())),
        }
        match head.get("verdict").and_then(|f| f.as_str()) {
            Some("sat") => {}
            Some(other) => return Err(BundleError::WrongVerdict(other.into())),
            None => return Err(BundleError::Malformed("missing verdict".into())),
        }
        let env: SatEnvelopeV3In =
            serde_json::from_str(json).map_err(|e| BundleError::Malformed(e.to_string()))?;
        if env.format != "ordeal-cert/v3" {
            return Err(BundleError::WrongFormat(env.format));
        }
        if env.verdict != "sat" {
            return Err(BundleError::WrongVerdict(env.verdict));
        }
        let witness = sat_witness_from_blocks(env.problem, env.model, env.witness, &env.recheck)?;
        let query = query_from_block(env.query)?;
        let inputs = inputs_from_block(env.inputs)?;
        let term = term_from_block(env.term)?;
        Ok(TermSatBundle {
            certificate: TermSatCertificate {
                query: QuerySatCertificate {
                    witness,
                    query,
                    inputs,
                },
                term,
            },
            attests: env.attests,
            produced_by: env.produced_by,
        })
    }
}

// ── ordeal-cert/v4: the extended-query bundles (TR-072) ──────────────────

use crate::query::{
    EXT_ENCODING, SliverBlock, SliverCertificate, SliverModelRecheckError, SliverRecheckError,
    SliverSatCertificate, ext_node_from_op, ext_node_op,
};
use crate::sliver::{ExtQuery, SliverModel};

/// The `ext` block of an `ordeal-cert/v4` bundle ([`SliverBlock`]): the
/// extended query as asked — nodes in the `query` block's spelling plus
/// `["select", aid, idx, s, n]` / `["call", fid, w, s, n]`, the side
/// table, the roots, the variable, array and function names — the
/// untrusted map onto the `term` block's nodes, the read and call tables,
/// and the block's content hash (`SliverBlock::canonical_text`).
#[derive(Serialize, Deserialize)]
struct ExtBlock {
    encoding: String,
    num_nodes: usize,
    nodes: Vec<serde_json::Value>,
    bits: String,
    side: Vec<usize>,
    roots: Vec<usize>,
    vars: Vec<InputVarEntry>,
    arrays: Vec<String>,
    funcs: Vec<FuncEntry>,
    /// Extended node → `term` node; `usize::MAX` for a node with no image.
    map: Vec<usize>,
    /// 3 per entry: read var node, array id, index node.
    reads: Vec<usize>,
    /// 4 per entry: result var node, function id, first arg, arity.
    calls: Vec<usize>,
    cargs: Vec<usize>,
    sha256: String,
}

/// A function of the `ext` block: its name and result width, by id.
#[derive(Serialize, Deserialize, Clone, PartialEq, Eq, Debug)]
struct FuncEntry {
    name: String,
    width: u32,
}

/// The extended model of a v4 SAT bundle: the pullback of the core model.
#[derive(Serialize, Deserialize)]
struct ExtModelBlock {
    encoding: String,
    /// The query variables' bindings, sorted by name.
    assignments: Vec<(String, u128)>,
    /// Per array, the cells the reads touched: `(index, byte)`, sorted.
    arrays: Vec<ArrayCells>,
    /// Per function, the tuples the calls touched, sorted.
    calls: Vec<CallEntryBlock>,
}

#[derive(Serialize, Deserialize)]
struct ArrayCells {
    name: String,
    cells: Vec<(u32, u8)>,
}

#[derive(Serialize, Deserialize)]
struct CallEntryBlock {
    name: String,
    args: Vec<u128>,
    value: u128,
}

fn ext_node_to_json(n: &ordeal_lrat::ExtNode) -> serde_json::Value {
    let (op, args) = ext_node_op(n);
    let mut arr = vec![serde_json::Value::String(op.into())];
    arr.extend(args.into_iter().map(|a| serde_json::Value::from(a as u64)));
    serde_json::Value::Array(arr)
}

fn ext_node_from_json(v: &serde_json::Value) -> Result<ordeal_lrat::ExtNode, BundleError> {
    let malformed = || BundleError::Malformed(format!("ext node {v} is not [\"op\", arg…]"));
    let arr = v.as_array().ok_or_else(malformed)?;
    let op = arr.first().and_then(|o| o.as_str()).ok_or_else(malformed)?;
    let args = arr[1..]
        .iter()
        .map(|a| a.as_u64().map(|x| x as usize).ok_or_else(malformed))
        .collect::<Result<Vec<_>, _>>()?;
    ext_node_from_op(op, &args).ok_or_else(|| {
        BundleError::Unsupported(format!("ext node operation {op} with {} args", args.len()))
    })
}

fn ext_to_block(b: &SliverBlock) -> ExtBlock {
    ExtBlock {
        encoding: EXT_ENCODING.into(),
        num_nodes: b.ext.nodes.len(),
        nodes: b.ext.nodes.iter().map(ext_node_to_json).collect(),
        bits: bits_string(&b.ext.bits),
        side: b.ext.side.clone(),
        roots: b.ext.roots.clone(),
        vars: b
            .ext
            .vars
            .iter()
            .map(|(name, width, node)| InputVarEntry {
                name: name.clone(),
                width: *width,
                node: *node,
            })
            .collect(),
        arrays: b.ext.arrays.clone(),
        funcs: b
            .ext
            .funcs
            .iter()
            .map(|(name, width)| FuncEntry {
                name: name.clone(),
                width: *width,
            })
            .collect(),
        map: b.map.clone(),
        reads: b.reads.clone(),
        calls: b.calls.clone(),
        cargs: b.cargs.clone(),
        sha256: b.sha256(),
    }
}

fn ext_from_block(block: ExtBlock) -> Result<SliverBlock, BundleError> {
    if block.encoding != EXT_ENCODING {
        return Err(BundleError::Unsupported(format!(
            "ext encoding {}",
            block.encoding
        )));
    }
    let mut nodes = Vec::with_capacity(block.nodes.len());
    for n in &block.nodes {
        nodes.push(ext_node_from_json(n)?);
    }
    if nodes.len() != block.num_nodes {
        return Err(BundleError::Malformed(format!(
            "ext.num_nodes {} but {} nodes",
            block.num_nodes,
            nodes.len()
        )));
    }
    let bits = bits_from_string(&block.bits).ok_or_else(|| {
        BundleError::Malformed("ext bits contain a character other than '0'/'1'".into())
    })?;
    let sliver = SliverBlock {
        ext: ExtQuery {
            nodes,
            bits,
            side: block.side,
            roots: block.roots,
            vars: block
                .vars
                .iter()
                .map(|v| (v.name.clone(), v.width, v.node))
                .collect(),
            arrays: block.arrays,
            funcs: block
                .funcs
                .iter()
                .map(|f| (f.name.clone(), f.width))
                .collect(),
        },
        map: block.map,
        reads: block.reads,
        calls: block.calls,
        cargs: block.cargs,
    };
    if sliver.sha256() != block.sha256 {
        return Err(BundleError::HashMismatch("ext"));
    }
    Ok(sliver)
}

fn ext_model_to_block(m: &SliverModel) -> ExtModelBlock {
    let mut assignments: Vec<(String, u128)> = m.env.iter().map(|(k, v)| (k.clone(), *v)).collect();
    assignments.sort();
    ExtModelBlock {
        encoding: "ext-model".into(),
        assignments,
        arrays: m
            .arrays
            .iter()
            .map(|(name, cells)| ArrayCells {
                name: name.clone(),
                cells: cells.iter().map(|(i, b)| (*i, *b)).collect(),
            })
            .collect(),
        calls: m
            .calls
            .iter()
            .map(|((name, args), value)| CallEntryBlock {
                name: name.clone(),
                args: args.clone(),
                value: *value,
            })
            .collect(),
    }
}

fn ext_model_from_block(block: ExtModelBlock) -> Result<SliverModel, BundleError> {
    if block.encoding != "ext-model" {
        return Err(BundleError::Unsupported(format!(
            "ext model encoding {}",
            block.encoding
        )));
    }
    let mut m = SliverModel::default();
    for (k, v) in block.assignments {
        m.env.insert(k, v);
    }
    for a in block.arrays {
        m.arrays.entry(a.name).or_default().extend(a.cells);
    }
    for c in block.calls {
        m.calls.insert((c.name, c.args), c.value);
    }
    Ok(m)
}

/// The v4 UNSAT envelope: v3's fields plus `ext` after `term`.
#[derive(Serialize, Deserialize)]
struct UnsatEnvelopeV4 {
    format: String,
    verdict: String,
    produced_by: Tool,
    checked_by: Tool,
    attests: Attests,
    problem: ProblemBlock,
    proof: ProofBlock,
    query: QueryBlock,
    term: TermBlock,
    ext: ExtBlock,
    recheck: RecheckBlockV2,
}

/// A parsed, hash-verified `ordeal-cert/v4` UNSAT bundle: the v3 bundle
/// plus the extended query the core was lowered from.
#[derive(Debug)]
pub struct SliverBundle {
    /// The certificate with its query, term and ext block, reconstructed.
    pub certificate: SliverCertificate,
    /// What the bundle claims to attest.
    pub attests: Attests,
    /// Producer identification, as recorded.
    pub produced_by: Tool,
}

impl SliverBundle {
    /// Re-run the trusted EXTENDED re-check (`check_sliver_lowering`,
    /// then `check_term_dag`, then `check_query`) — the operation a
    /// v4-aware consumer performs to turn this bundle into a verification
    /// link about the extended query. The v3 recheck stays available as
    /// `certificate.term.recheck()`.
    pub fn recheck(&self) -> Result<(), SliverRecheckError> {
        self.certificate.recheck()
    }
}

/// The `recheck.cmd` of a v4 UNSAT bundle.
const V4_UNSAT_CMD: &str = "ordeal_lrat::check_sliver_lowering(ext.nodes, ext.bits, ext.side, ext.roots, \
     ext.map, ext.reads, ext.calls, ext.cargs, term.nodes, term.bits, term.roots) == Ok(()) && \
     ordeal_lrat::check_term_dag(term.nodes, term.bits, term.roots, term.map, \
     query.nodes, query.bits, query.roots) == Ok(()) && \
     ordeal_lrat::check_query(query.nodes, query.bits, query.roots, query.hints, proof.body) \
     == Ok(problem.clauses)";

/// Readers from this version on decode `ordeal-cert/v4`.
const V4_MIN_VERSION: &str = "0.33.0";

impl SliverCertificate {
    /// Serialize this trusted-rechecked certificate as an `ordeal-cert/v4`
    /// UNSAT bundle: the v3 envelope (same `problem`, `proof`, `query` and
    /// `term` blocks, same hashes) plus the `ext` block, `format:
    /// "ordeal-cert/v4"`. A v1, v2 or v3 reader rejects it by format (no
    /// silent downgrade); `to_cert_v3` on `self.term` still produces the
    /// v3 bundle about the lowered core.
    #[allow(clippy::missing_panics_doc)] // serde_json on our own structs
    pub fn to_cert_v4(&self, attests: &Attests) -> String {
        let cert = &self.term.query.certificate;
        let problem_text = cnf_text(&cert.cnf);
        let proof_text = cert.lrat_text().unwrap_or_default().to_string();
        let env = UnsatEnvelopeV4 {
            format: "ordeal-cert/v4".into(),
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
                num_clauses: cert.cnf.len(),
                clauses: cert.cnf.clone(),
            },
            proof: ProofBlock {
                encoding: "lrat".into(),
                body: proof_text.clone(),
            },
            query: query_to_block(&self.term.query.query),
            term: term_to_block(&self.term.term),
            ext: ext_to_block(&self.sliver),
            recheck: RecheckBlockV2 {
                tool: "ordeal-lrat".into(),
                min_version: V4_MIN_VERSION.into(),
                cmd: V4_UNSAT_CMD.into(),
                problem_sha256: sha256_hex(problem_text.as_bytes()),
                proof_sha256: sha256_hex(proof_text.as_bytes()),
            },
        };
        serde_json::to_string_pretty(&env).expect("own-struct serialization")
    }

    /// Parse an `ordeal-cert/v4` UNSAT bundle, verifying all five content
    /// hashes (problem, proof, query, term, ext) BEFORE returning. The
    /// caller then runs [`SliverBundle::recheck`]. A v1, v2 or v3 bundle
    /// is [`BundleError::WrongFormat`]: read it with its own reader.
    pub fn from_cert_v4(json: &str) -> Result<SliverBundle, BundleError> {
        let head: serde_json::Value =
            serde_json::from_str(json).map_err(|e| BundleError::Malformed(e.to_string()))?;
        match head.get("format").and_then(|f| f.as_str()) {
            Some("ordeal-cert/v4") => {}
            Some(other) => return Err(BundleError::WrongFormat(other.into())),
            None => return Err(BundleError::Malformed("missing format".into())),
        }
        match head.get("verdict").and_then(|f| f.as_str()) {
            Some("unsat") => {}
            Some(other) => return Err(BundleError::WrongVerdict(other.into())),
            None => return Err(BundleError::Malformed("missing verdict".into())),
        }
        let env: UnsatEnvelopeV4 =
            serde_json::from_str(json).map_err(|e| BundleError::Malformed(e.to_string()))?;
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
        if !encoding_supported(&env.query.encoding) {
            return Err(BundleError::Unsupported(format!(
                "query encoding {}",
                env.query.encoding
            )));
        }
        let problem_text = cnf_text(&env.problem.clauses);
        if sha256_hex(problem_text.as_bytes()) != env.recheck.problem_sha256 {
            return Err(BundleError::HashMismatch("problem"));
        }
        if sha256_hex(env.proof.body.as_bytes()) != env.recheck.proof_sha256 {
            return Err(BundleError::HashMismatch("proof"));
        }
        let query = query_from_block(env.query)?;
        let term = term_from_block(env.term)?;
        let sliver = ext_from_block(env.ext)?;
        Ok(SliverBundle {
            certificate: SliverCertificate {
                term: TermCertificate {
                    query: QueryCertificate {
                        certificate: Certificate {
                            lrat: env.proof.body.into_bytes(),
                            cnf: env.problem.clauses,
                        },
                        query,
                    },
                    term,
                },
                sliver,
            },
            attests: env.attests,
            produced_by: env.produced_by,
        })
    }
}

/// The v4 SAT envelope: v3's fields plus `ext` and `ext_model` after
/// `term`.
#[derive(Serialize)]
struct SatEnvelopeV4 {
    format: String,
    verdict: String,
    produced_by: Tool,
    checked_by: Tool,
    attests: Attests,
    problem: ProblemBlock,
    model: SatModelBlock,
    witness: WitnessBlock,
    query: QueryBlock,
    inputs: InputsBlock,
    term: TermBlock,
    ext: ExtBlock,
    ext_model: ExtModelBlock,
    recheck: SatWitnessRecheck,
}

#[derive(Deserialize)]
struct SatEnvelopeV4In {
    format: String,
    verdict: String,
    attests: Attests,
    produced_by: Tool,
    problem: ProblemBlock,
    model: SatModelBlock,
    witness: WitnessBlock,
    query: QueryBlock,
    inputs: InputsBlock,
    term: TermBlock,
    ext: ExtBlock,
    ext_model: ExtModelBlock,
    recheck: SatWitnessRecheck,
}

/// A parsed, hash-verified `ordeal-cert/v4` SAT bundle: the v3 SAT bundle
/// plus the extended query and the extended model.
#[derive(Debug)]
pub struct SliverSatBundle {
    /// The witness with its query, inputs, term, ext block and extended
    /// model, reconstructed.
    pub certificate: SliverSatCertificate,
    /// What the bundle claims to attest.
    pub attests: Attests,
    /// Producer identification, as recorded.
    pub produced_by: Tool,
}

impl SliverSatBundle {
    /// Re-run the trusted EXTENDED re-check: `check_sliver_lowering`, the
    /// v3 SAT recheck, and that the extended model is the pullback of the
    /// core model.
    pub fn recheck(&self) -> Result<(), SliverModelRecheckError> {
        self.certificate.recheck()
    }
}

impl SliverSatCertificate {
    /// Serialize this trusted-rechecked certificate as an `ordeal-cert/v4`
    /// SAT bundle: the v3 SAT envelope (same blocks, same hashes) plus the
    /// `ext` and `ext_model` blocks, `format: "ordeal-cert/v4"`.
    #[allow(clippy::missing_panics_doc)] // serde_json on our own structs
    pub fn to_cert_v4(&self, attests: &Attests) -> String {
        let w = &self.term.query.witness;
        let problem_text = cnf_text(&w.cnf);
        let env = SatEnvelopeV4 {
            format: "ordeal-cert/v4".into(),
            verdict: "sat".into(),
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
                num_clauses: w.cnf.len(),
                clauses: w.cnf.clone(),
            },
            model: SatModelBlock {
                encoding: "assignments".into(),
                assignments: w.model.assignments.clone(),
            },
            witness: w.witness_block(),
            query: query_to_block(&self.term.query.query),
            inputs: InputsBlock {
                encoding: crate::query::INPUTS_ENCODING.into(),
                bits: bits_string(&self.term.query.inputs.bits),
                vars: self
                    .term
                    .query
                    .inputs
                    .vars
                    .iter()
                    .map(|(name, width, node)| InputVarEntry {
                        name: name.clone(),
                        width: *width,
                        node: *node,
                    })
                    .collect(),
                sha256: self.term.query.inputs.sha256(),
            },
            term: term_to_block(&self.term.term),
            ext: ext_to_block(&self.sliver),
            ext_model: ext_model_to_block(&self.model),
            recheck: SatWitnessRecheck {
                tool: "ordeal-lrat".into(),
                min_version: V4_MIN_VERSION.into(),
                cmd:
                    "ordeal_lrat::check_sliver_lowering(ext.nodes, ext.bits, ext.side, ext.roots, \
                      ext.map, ext.reads, ext.calls, ext.cargs, term.nodes, term.bits, term.roots) \
                      == Ok(()) + ordeal_lrat::check_term_dag(term.nodes, term.bits, term.roots, \
                      term.map, query.nodes, query.bits, query.roots) == Ok(()) + \
                      ordeal_lrat::check_sat(problem, witness.assignment) + \
                      ordeal_lrat::check_binding per model binding + \
                      ordeal_lrat::check_query_model(query.nodes, query.bits, query.roots, \
                      inputs.bits) == Ok(()) + ordeal_lrat::check_input_value(inputs.bits, \
                      ordeal_lrat::var_offset(query.nodes, term.map[term.vars[name].node]), \
                      width, value) per model binding + ext_model is the pullback of model \
                      through ext.reads / ext.calls"
                        .into(),
                problem_sha256: sha256_hex(problem_text.as_bytes()),
            },
        };
        serde_json::to_string_pretty(&env).expect("own-struct serialization")
    }

    /// Parse an `ordeal-cert/v4` SAT bundle, verifying all seven content
    /// hashes (problem, witness assignment, bit map, query, inputs, term,
    /// ext) BEFORE returning. The caller then runs
    /// [`SliverSatBundle::recheck`].
    pub fn from_cert_v4(json: &str) -> Result<SliverSatBundle, BundleError> {
        let head: serde_json::Value =
            serde_json::from_str(json).map_err(|e| BundleError::Malformed(e.to_string()))?;
        match head.get("format").and_then(|f| f.as_str()) {
            Some("ordeal-cert/v4") => {}
            Some(other) => return Err(BundleError::WrongFormat(other.into())),
            None => return Err(BundleError::Malformed("missing format".into())),
        }
        match head.get("verdict").and_then(|f| f.as_str()) {
            Some("sat") => {}
            Some(other) => return Err(BundleError::WrongVerdict(other.into())),
            None => return Err(BundleError::Malformed("missing verdict".into())),
        }
        let env: SatEnvelopeV4In =
            serde_json::from_str(json).map_err(|e| BundleError::Malformed(e.to_string()))?;
        if env.format != "ordeal-cert/v4" {
            return Err(BundleError::WrongFormat(env.format));
        }
        if env.verdict != "sat" {
            return Err(BundleError::WrongVerdict(env.verdict));
        }
        let witness = sat_witness_from_blocks(env.problem, env.model, env.witness, &env.recheck)?;
        let query = query_from_block(env.query)?;
        let inputs = inputs_from_block(env.inputs)?;
        let term = term_from_block(env.term)?;
        let sliver = ext_from_block(env.ext)?;
        let model = ext_model_from_block(env.ext_model)?;
        Ok(SliverSatBundle {
            certificate: SliverSatCertificate {
                term: TermSatCertificate {
                    query: QuerySatCertificate {
                        witness,
                        query,
                        inputs,
                    },
                    term,
                },
                sliver,
                model,
            },
            attests: env.attests,
            produced_by: env.produced_by,
        })
    }
}

// rivet: verifies VER-027
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

    // ── TR-038: the independently re-checkable SAT witness ──────────────

    fn a_sat_query() -> Solver {
        use crate::{BoolTerm, BvTerm, Sort};
        let mut s = Solver::new();
        let a = BvTerm::Var {
            name: "a".into(),
            sort: Sort::new(8),
        };
        let five = BvTerm::Const {
            value: 5,
            sort: Sort::new(8),
        };
        let three = BvTerm::Const {
            value: 3,
            sort: Sort::new(8),
        };
        s.assert(BoolTerm::Eq(
            Box::new(BvTerm::Urem(Box::new(a), Box::new(five))),
            Box::new(three),
        ));
        s
    }

    fn a_sat_witness() -> SatCertificate {
        match a_sat_query().check_with_witness() {
            WitnessCheckResult::Sat(cert) => cert,
            other => panic!("expected Sat with witness, got {other:?}"),
        }
    }

    // rivet: verifies VER-037
    #[test]
    fn sat_witness_rechecks_end_to_end() {
        let cert = a_sat_witness();
        cert.recheck().expect("fresh witness must re-check");
        // The model actually satisfies the query semantics.
        let (_, v) = cert
            .model
            .assignments
            .iter()
            .find(|(n, _)| n == "a")
            .unwrap();
        assert_eq!(v % 5, 3);
        // Round-trip through the v1 bundle, hash-verified, still re-checks.
        let json = cert.to_cert_v1(&attests());
        let back = SatCertificate::from_cert_v1(&json).expect("pristine bundle parses");
        back.recheck().expect("round-tripped witness must re-check");
        assert_eq!(back.model.assignments, cert.model.assignments);
    }

    // rivet: verifies VER-037
    #[test]
    fn sat_witness_is_deterministic() {
        let a = a_sat_witness().to_cert_v1(&attests());
        let b = a_sat_witness().to_cert_v1(&attests());
        assert_eq!(a, b, "witness bundles must be byte-identical run to run");
    }

    // rivet: verifies VER-037
    #[test]
    fn tampered_witness_assignment_is_rejected_at_ingestion() {
        let json = a_sat_witness().to_cert_v1(&attests());
        let mut v: serde_json::Value = serde_json::from_str(&json).unwrap();
        let bits = v["witness"]["assignment"].as_str().unwrap().to_string();
        let flipped: String = bits
            .chars()
            .enumerate()
            .map(|(i, c)| {
                if i == 0 {
                    if c == '0' { '1' } else { '0' }
                } else {
                    c
                }
            })
            .collect();
        v["witness"]["assignment"] = serde_json::Value::String(flipped);
        match SatCertificate::from_cert_v1(&v.to_string()) {
            Err(BundleError::HashMismatch("witness-assignment")) => {}
            other => panic!("expected witness-assignment hash mismatch, got {other:?}"),
        }
    }

    // rivet: verifies VER-037
    #[test]
    fn tampered_model_is_caught_by_recheck_not_parsing() {
        // The model block is deliberately not content-hashed: its guarantee
        // is SEMANTIC — every advertised binding is verified against the
        // assignment by the trusted crate. A lying model parses fine and
        // then fails recheck with a BindingMismatch.
        let json = a_sat_witness().to_cert_v1(&attests());
        let mut v: serde_json::Value = serde_json::from_str(&json).unwrap();
        let old = v["model"]["assignments"][0][1].as_u64().unwrap();
        v["model"]["assignments"][0][1] = serde_json::Value::from(old ^ 1);
        let cert = SatCertificate::from_cert_v1(&v.to_string())
            .expect("model tamper is not an integrity failure");
        match cert.recheck() {
            Err(SatRecheckError::Witness(ordeal_lrat::SatWitnessError::BindingMismatch {
                ..
            })) => {}
            other => panic!("expected BindingMismatch, got {other:?}"),
        }
    }

    // rivet: verifies VER-037
    #[test]
    fn truncated_assignment_fails_recheck() {
        let mut cert = a_sat_witness();
        cert.assignment.truncate(1);
        assert!(
            cert.recheck().is_err(),
            "truncated assignment must not re-check"
        );
    }

    // ── #192 phase 4: ordeal-cert/v2, the query-carrying bundle ─────────

    /// `(x + 5 = 3) ∧ (x ≠ 254)` at width 8: UNSAT, and every constant bit
    /// matters to the refutation.
    fn a_query_certificate() -> QueryCertificate {
        use crate::{BoolTerm, BvTerm, QueryCheckResult, Sort};
        let var = |name: &str| BvTerm::Var {
            name: name.into(),
            sort: Sort::new(8),
        };
        let konst = |v: u128| BvTerm::Const {
            value: v,
            sort: Sort::new(8),
        };
        let mut s = Solver::new();
        s.assert(BoolTerm::Eq(
            Box::new(BvTerm::Add(Box::new(var("x")), Box::new(konst(5)))),
            Box::new(konst(3)),
        ));
        s.assert(BoolTerm::Ne(Box::new(var("x")), Box::new(konst(254))));
        match s.check_with_query() {
            QueryCheckResult::Unsat(c) => c,
            other => panic!("expected Unsat with query, got {other:?}"),
        }
    }

    // rivet: verifies VER-062
    /// Round trip: emit v2 → parse → three hashes verify → the trusted
    /// QUERY re-check passes; the v1 pair inside still re-checks too, and
    /// the v1 serialization of the same certificate is the v1 bundle.
    #[test]
    fn v2_bundle_round_trips_and_rechecks_the_query() {
        let cert = a_query_certificate();
        let json = cert.to_cert_v2(&attests());
        let v: serde_json::Value = serde_json::from_str(&json).unwrap();
        assert_eq!(v["format"], "ordeal-cert/v2");
        assert_eq!(v["query"]["encoding"], QUERY_ENCODING);
        assert_eq!(v["query"]["sha256"], cert.query.sha256());
        assert_eq!(v["query"]["num_nodes"], cert.query.nodes.len());
        let bundle = QueryCertificate::from_cert_v2(&json).expect("v2 bundle parses");
        assert_eq!(bundle.attests, attests());
        assert!(bundle.certificate.query == cert.query);
        bundle.recheck().expect("query re-check passes");
        bundle
            .certificate
            .certificate
            .recheck()
            .expect("the v1 pair inside re-checks");
        // Same problem, proof and hashes as the v1 bundle of the same
        // certificate; v1 carries no query block.
        let v1: serde_json::Value =
            serde_json::from_str(&cert.certificate.to_cert_v1(&attests())).unwrap();
        assert_eq!(v1["problem"], v["problem"]);
        assert_eq!(v1["proof"], v["proof"]);
        assert_eq!(
            v1["recheck"]["problem_sha256"],
            v["recheck"]["problem_sha256"]
        );
        assert_eq!(v1["recheck"]["proof_sha256"], v["recheck"]["proof_sha256"]);
        assert!(v1.get("query").is_none());
    }

    // rivet: verifies VER-062
    /// The phase-4 acceptance criterion at the bundle level: flip ONE
    /// constant bit in the `query` block (hash recomputed, so integrity
    /// passes) — the CNF and the proof are untouched, and the recheck
    /// FAILS, because the trusted crate re-encodes the DAG it was given.
    #[test]
    fn v2_flipped_query_bit_fails_recheck_with_cnf_and_proof_untouched() {
        let cert = a_query_certificate();
        let json = cert.to_cert_v2(&attests());
        let mut v: serde_json::Value = serde_json::from_str(&json).unwrap();
        let bits = v["query"]["bits"].as_str().unwrap().to_string();
        assert!(!bits.is_empty());
        let flipped: String = bits
            .chars()
            .enumerate()
            .map(|(i, c)| {
                if i == 0 {
                    if c == '0' { '1' } else { '0' }
                } else {
                    c
                }
            })
            .collect();
        v["query"]["bits"] = serde_json::Value::String(flipped.clone());
        // Stale hash: integrity failure at parse, before any recheck.
        match QueryCertificate::from_cert_v2(&v.to_string()) {
            Err(BundleError::HashMismatch("query")) => {}
            other => panic!("stale query hash must be a query-hash mismatch, got {other:?}"),
        }
        // Recomputed hash: parses, then the trusted recheck rejects.
        let mut tampered_query = cert.query.clone();
        tampered_query.bits[0] = !tampered_query.bits[0];
        v["query"]["sha256"] = serde_json::Value::String(tampered_query.sha256());
        let bundle = QueryCertificate::from_cert_v2(&v.to_string())
            .expect("consistent tamper passes the integrity check");
        assert_eq!(bundle.certificate.certificate.cnf, cert.certificate.cnf);
        assert_eq!(bundle.certificate.certificate.lrat, cert.certificate.lrat);
        let r = bundle.recheck();
        assert!(
            r.is_err(),
            "flipped constant bit must fail the recheck: {r:?}"
        );
        // …while the v1 (CNF-level) recheck of the same bundle still passes:
        // this is precisely the gap v2 closes.
        bundle
            .certificate
            .certificate
            .recheck()
            .expect("the untouched CNF/proof pair still re-checks at the CNF level");
    }

    // rivet: verifies VER-062
    /// Tampering with the proof or the problem of a v2 bundle is caught by
    /// the v1 hashes exactly as before; a wrong query encoding, a malformed
    /// node and a wrong node count are refused at parse.
    #[test]
    fn v2_integrity_and_shape_checks() {
        let cert = a_query_certificate();
        let json = cert.to_cert_v2(&attests());
        let pristine: serde_json::Value = serde_json::from_str(&json).unwrap();

        let mut t = pristine.clone();
        t["proof"]["body"] =
            serde_json::Value::String(format!("9 {}", t["proof"]["body"].as_str().unwrap()));
        assert!(matches!(
            QueryCertificate::from_cert_v2(&t.to_string()),
            Err(BundleError::HashMismatch("proof"))
        ));

        let mut t = pristine.clone();
        let lit = t["problem"]["clauses"][0][0].as_i64().unwrap();
        t["problem"]["clauses"][0][0] = serde_json::json!(-lit);
        assert!(matches!(
            QueryCertificate::from_cert_v2(&t.to_string()),
            Err(BundleError::HashMismatch("problem"))
        ));

        let mut t = pristine.clone();
        t["query"]["encoding"] = serde_json::Value::String("other-dag/v9".into());
        assert!(matches!(
            QueryCertificate::from_cert_v2(&t.to_string()),
            Err(BundleError::Unsupported(_))
        ));

        let mut t = pristine.clone();
        t["query"]["nodes"][0] = serde_json::json!(["bvfoo", 1, 2]);
        assert!(matches!(
            QueryCertificate::from_cert_v2(&t.to_string()),
            Err(BundleError::Malformed(_))
        ));

        let mut t = pristine.clone();
        t["query"]["num_nodes"] = serde_json::json!(0);
        assert!(matches!(
            QueryCertificate::from_cert_v2(&t.to_string()),
            Err(BundleError::Malformed(_))
        ));

        let mut t = pristine.clone();
        t["verdict"] = serde_json::Value::String("sat".into());
        assert!(matches!(
            QueryCertificate::from_cert_v2(&t.to_string()),
            Err(BundleError::WrongVerdict(_))
        ));
    }

    // rivet: verifies VER-062
    /// Format discipline: a v2 bundle is refused by the v1 reader and a v1
    /// bundle by the v2 reader — nobody silently downgrades or upgrades.
    #[test]
    fn v1_and_v2_readers_refuse_each_others_format() {
        let cert = a_query_certificate();
        let v2 = cert.to_cert_v2(&attests());
        assert!(matches!(
            Certificate::from_cert_v1(&v2),
            Err(BundleError::WrongFormat(f)) if f == "ordeal-cert/v2"
        ));
        let v1 = cert.certificate.to_cert_v1(&attests());
        assert!(matches!(
            QueryCertificate::from_cert_v2(&v1),
            Err(BundleError::WrongFormat(f)) if f == "ordeal-cert/v1"
        ));
    }

    /// `(a sdiv b) ≠ rewrite(a sdiv b)` at width 8 through
    /// `check_with_query`: the DAG carries an `Sdiv` node (#192 phase 5).
    fn an_sdiv_query_certificate() -> QueryCertificate {
        use crate::{BoolTerm, BvTerm, QueryCheckResult, Sort};
        let var = |name: &str| BvTerm::Var {
            name: name.into(),
            sort: Sort::new(8),
        };
        let sdiv = BvTerm::Sdiv(Box::new(var("a")), Box::new(var("b")));
        let twin = crate::lowering::expand_bv(&sdiv).expect("sorted");
        let mut s = Solver::new();
        s.assert(BoolTerm::Ne(Box::new(sdiv), Box::new(twin)));
        match s.check_with_query() {
            QueryCheckResult::Unsat(c) => c,
            other => panic!("expected Unsat with query, got {other:?}"),
        }
    }

    // rivet: verifies VER-064
    /// #192 phase 5 at the bundle level: a v2 bundle whose `query` block
    /// carries an `sdiv` node is tagged `ordeal-dag/v2` with
    /// `recheck.min_version` 0.28.0, round-trips, and re-checks; the SAME
    /// bundle with that node changed to `udiv` (hash recomputed, so
    /// integrity passes; CNF and proof untouched) FAILS the recheck while
    /// its v1 pair still re-checks at the CNF level. A block that declares
    /// `ordeal-dag/v1` but carries a derived node is refused at parse, and
    /// a block tagged `ordeal-dag/v2` without one is accepted when its hash
    /// is computed under the declared tag.
    #[test]
    fn v2_sdiv_node_swapped_to_udiv_fails_recheck_with_cnf_and_proof_untouched() {
        let cert = an_sdiv_query_certificate();
        assert!(cert.query.has_derived());
        let json = cert.to_cert_v2(&attests());
        let v: serde_json::Value = serde_json::from_str(&json).unwrap();
        assert_eq!(v["query"]["encoding"], QUERY_ENCODING_V2);
        assert_eq!(v["recheck"]["min_version"], "0.28.0");
        let round =
            QueryCertificate::from_cert_v2(&json).expect("v2 bundle with an sdiv node parses");
        round
            .recheck()
            .expect("round-tripped sdiv bundle re-checks");
        assert_eq!(round.certificate.query, cert.query);

        // The control: sdiv → udiv in the JSON, hash recomputed.
        let mut t = v.clone();
        let nodes = t["query"]["nodes"].as_array_mut().unwrap();
        let i = nodes
            .iter()
            .position(|n| n[0] == "sdiv")
            .expect("an sdiv node in the block");
        nodes[i][0] = serde_json::Value::String("udiv".into());
        let mut tampered_query = cert.query.clone();
        let crate::blast_kernel::DagNode::Sdiv(a, b) = tampered_query.nodes[i] else {
            panic!("node {i} is the sdiv node");
        };
        tampered_query.nodes[i] = crate::blast_kernel::DagNode::Udiv(a, b);
        // Stale hash first: rejected at parse.
        assert!(matches!(
            QueryCertificate::from_cert_v2(&t.to_string()),
            Err(BundleError::HashMismatch("query"))
        ));
        // Recomputed hash under the declared (v2) tag: parses, recheck fails.
        t["query"]["sha256"] =
            serde_json::Value::String(tampered_query.sha256_tagged(QUERY_ENCODING_V2));
        let bundle = QueryCertificate::from_cert_v2(&t.to_string())
            .expect("consistent tamper passes the integrity check");
        assert_eq!(bundle.certificate.certificate.cnf, cert.certificate.cnf);
        assert_eq!(bundle.certificate.certificate.lrat, cert.certificate.lrat);
        let r = bundle.recheck();
        assert!(r.is_err(), "sdiv → udiv must fail the recheck: {r:?}");
        bundle
            .certificate
            .certificate
            .recheck()
            .expect("the untouched CNF/proof pair still re-checks at the CNF level");

        // A v1-tagged block carrying a derived node is a lie about the tag.
        let mut t = v.clone();
        t["query"]["encoding"] = serde_json::Value::String(QUERY_ENCODING.into());
        t["query"]["sha256"] = serde_json::Value::String(cert.query.sha256_tagged(QUERY_ENCODING));
        assert!(matches!(
            QueryCertificate::from_cert_v2(&t.to_string()),
            Err(BundleError::Malformed(m)) if m.contains("derived-op node")
        ));
        // A v2-tagged block WITHOUT a derived node is fine when hashed under
        // the declared tag (the writer would have chosen v1; a reader does
        // not insist).
        let plain = a_query_certificate();
        let mut t: serde_json::Value = serde_json::from_str(&plain.to_cert_v2(&attests())).unwrap();
        assert_eq!(t["query"]["encoding"], QUERY_ENCODING);
        t["query"]["encoding"] = serde_json::Value::String(QUERY_ENCODING_V2.into());
        t["query"]["sha256"] =
            serde_json::Value::String(plain.query.sha256_tagged(QUERY_ENCODING_V2));
        QueryCertificate::from_cert_v2(&t.to_string())
            .expect("v2-tagged block without derived nodes parses under its declared tag")
            .recheck()
            .expect("and re-checks");
        // An unknown tag is unsupported.
        t["query"]["encoding"] = serde_json::Value::String("ordeal-dag/v3".into());
        assert!(matches!(
            QueryCertificate::from_cert_v2(&t.to_string()),
            Err(BundleError::Unsupported(_))
        ));
    }

    // rivet: verifies VER-062
    /// v1 regression: the shipped v1 bundles under evidence/certs/ (emitted
    /// by v0.23.0) still parse and re-check through `from_cert_v1`
    /// unchanged, and the v2 reader reports them as v1 rather than
    /// misreading them.
    #[test]
    fn shipped_v1_bundles_still_parse_and_recheck() {
        for (name, json) in [
            (
                "rotl_decompose_w12",
                include_str!("../../../evidence/certs/rotl_decompose_w12.json"),
            ),
            (
                "shl_lshr_mask_w24",
                include_str!("../../../evidence/certs/shl_lshr_mask_w24.json"),
            ),
        ] {
            let bundle = Certificate::from_cert_v1(json).unwrap_or_else(|e| panic!("{name}: {e}"));
            bundle
                .recheck()
                .unwrap_or_else(|e| panic!("{name}: v1 recheck: {e}"));
            assert!(matches!(
                QueryCertificate::from_cert_v2(json),
                Err(BundleError::WrongFormat(f)) if f == "ordeal-cert/v1"
            ));
        }
    }

    // rivet: verifies VER-037
    #[test]
    fn witness_entry_reports_unsat_with_a_checked_certificate() {
        use crate::{BoolTerm, BvTerm, Sort};
        let mut s = Solver::new();
        let a = BvTerm::Var {
            name: "a".into(),
            sort: Sort::new(8),
        };
        let one = BvTerm::Const {
            value: 1,
            sort: Sort::new(8),
        };
        let zero = BvTerm::Const {
            value: 0,
            sort: Sort::new(8),
        };
        s.assert(BoolTerm::Ne(
            Box::new(BvTerm::Urem(Box::new(a), Box::new(one))),
            Box::new(zero),
        ));
        match s.check_with_witness() {
            WitnessCheckResult::Unsat(cert) => cert.recheck().expect("unsat leg re-checks"),
            other => panic!("expected Unsat, got {other:?}"),
        }
    }

    // ── #192 phase 6: ordeal-cert/v2, the query-carrying SAT bundle ─────

    fn a_query_sat_certificate() -> QuerySatCertificate {
        use crate::QueryCheckResult;
        match a_sat_query().check_with_query() {
            QueryCheckResult::Sat(c) => c,
            other => panic!("expected Sat with query, got {other:?}"),
        }
    }

    // rivet: verifies VER-065
    /// Round trip: emit the SAT v2 → parse → five hashes verify → the
    /// trusted MODEL re-check passes; the v1 witness inside still
    /// re-checks, the v1 serialization of the same witness is the v1
    /// bundle (same blocks and hashes, no `query` / `inputs`), and the
    /// readers refuse each other's shapes by format / verdict.
    #[test]
    fn v2_sat_bundle_round_trips_and_rechecks_the_model() {
        let cert = a_query_sat_certificate();
        let json = cert.to_cert_v2(&attests());
        let v: serde_json::Value = serde_json::from_str(&json).unwrap();
        assert_eq!(v["format"], "ordeal-cert/v2");
        assert_eq!(v["verdict"], "sat");
        assert_eq!(v["query"]["sha256"], cert.query.sha256());
        assert_eq!(v["inputs"]["encoding"], crate::query::INPUTS_ENCODING);
        assert_eq!(v["inputs"]["sha256"], cert.inputs.sha256());
        assert_eq!(v["inputs"]["bits"], bits_string(&cert.inputs.bits));
        assert_eq!(v["recheck"]["min_version"], "0.29.0");
        assert!(
            v["recheck"]["cmd"]
                .as_str()
                .unwrap()
                .contains("check_query_model")
        );
        let bundle = QuerySatCertificate::from_cert_v2(&json).expect("v2 sat bundle parses");
        assert_eq!(bundle.attests, attests());
        assert!(bundle.certificate.query == cert.query);
        assert!(bundle.certificate.inputs == cert.inputs);
        bundle.recheck().expect("model re-check passes");
        bundle
            .certificate
            .witness
            .recheck()
            .expect("the v1 witness inside re-checks");
        // Same problem / model / witness blocks and hashes as the v1 bundle
        // of the same witness; v1 carries neither query nor inputs.
        let v1: serde_json::Value =
            serde_json::from_str(&cert.witness.to_cert_v1(&attests())).unwrap();
        assert_eq!(v1["format"], "ordeal-cert/v1");
        assert_eq!(v1["problem"], v["problem"]);
        assert_eq!(v1["model"], v["model"]);
        assert_eq!(v1["witness"], v["witness"]);
        assert_eq!(
            v1["recheck"]["problem_sha256"],
            v["recheck"]["problem_sha256"]
        );
        assert!(v1.get("query").is_none() && v1.get("inputs").is_none());
        // Cross-reader refusals.
        assert!(matches!(
            SatCertificate::from_cert_v1(&json),
            Err(BundleError::WrongFormat(_))
        ));
        assert!(matches!(
            QueryCertificate::from_cert_v2(&json),
            Err(BundleError::WrongVerdict(_))
        ));
        assert!(matches!(
            QuerySatCertificate::from_cert_v2(&cert.witness.to_cert_v1(&attests())),
            Err(BundleError::WrongFormat(_))
        ));
        let unsat_v2 = a_query_certificate().to_cert_v2(&attests());
        assert!(matches!(
            QuerySatCertificate::from_cert_v2(&unsat_v2),
            Err(BundleError::WrongVerdict(_))
        ));
    }

    // rivet: verifies VER-065
    /// The phase-6 bundle-level negative control: flip ONE input bit of
    /// the `inputs` block. With the stale hash the parse fails on
    /// integrity; with the hash recomputed (so integrity passes) and the
    /// problem / model / witness blocks UNTOUCHED — the v1 witness keeps
    /// re-checking — the model re-check FAILS: the model is no longer the
    /// inputs, and the inputs are no longer a model of the query.
    #[test]
    fn v2_sat_bundle_flipped_input_bit_fails_recheck_with_witness_untouched() {
        let cert = a_query_sat_certificate();
        let json = cert.to_cert_v2(&attests());
        let mut v: serde_json::Value = serde_json::from_str(&json).unwrap();
        let bits = v["inputs"]["bits"].as_str().unwrap().to_string();
        let flipped: String = bits
            .chars()
            .enumerate()
            .map(|(i, c)| {
                if i == 0 {
                    if c == '0' { '1' } else { '0' }
                } else {
                    c
                }
            })
            .collect();
        v["inputs"]["bits"] = serde_json::Value::String(flipped.clone());
        match QuerySatCertificate::from_cert_v2(&v.to_string()) {
            Err(BundleError::HashMismatch("inputs")) => {}
            other => panic!("stale inputs hash must be an inputs-hash mismatch, got {other:?}"),
        }
        let mut tampered = cert.inputs.clone();
        tampered.bits[0] = !tampered.bits[0];
        v["inputs"]["sha256"] = serde_json::Value::String(tampered.sha256());
        let bundle = QuerySatCertificate::from_cert_v2(&v.to_string())
            .expect("integrity passes with the recomputed hash");
        assert_eq!(bundle.certificate.witness.cnf, cert.witness.cnf);
        assert_eq!(
            bundle.certificate.witness.assignment,
            cert.witness.assignment
        );
        assert_eq!(
            bundle.certificate.witness.model.assignments,
            cert.witness.model.assignments
        );
        bundle
            .certificate
            .witness
            .recheck()
            .expect("the v1 witness is untouched and re-checks");
        assert!(
            bundle.recheck().is_err(),
            "a flipped input bit must fail the model re-check"
        );
        // The trusted crate alone, on the tampered inputs: a false root.
        assert!(matches!(
            ordeal_lrat::check_query_model(
                &bundle.certificate.query.nodes,
                &bundle.certificate.query.bits,
                &bundle.certificate.query.roots,
                &bundle.certificate.inputs.bits
            ),
            Err(ordeal_lrat::ModelError::RootFalse { .. })
        ));
    }
}
