//! #192 phase 7 (TR-069): the `ordeal-cert/v3` bundles — round trips, the
//! term block's integrity, the cross-reader refusals (v1/v2 refuse v3 and
//! v3 refuses v1/v2, by `format`), and the tamper controls with the v2
//! blocks untouched.

use crate::cert_bundle::{Attests, BundleError};
use crate::query::{
    QueryCertificate, QuerySatCertificate, TermCertificate, TermCheckResult, TermModelRecheckError,
    TermRecheckError, TermSatCertificate,
};
use crate::{BoolTerm, BvTerm, SatCertificate, Solver, Sort};
use ordeal_lrat::TermError;

fn var(name: &str) -> BvTerm {
    BvTerm::Var {
        name: name.into(),
        sort: Sort::new(8),
    }
}

fn konst(value: u128) -> BvTerm {
    BvTerm::Const {
        value,
        sort: Sort::new(8),
    }
}

fn b<T>(t: T) -> Box<T> {
    Box::new(t)
}

fn attests() -> Attests {
    Attests {
        kind: "translation_validation".into(),
        claim: "the question as asked is refuted".into(),
        standards: vec!["ISO-26262:8-11".into()],
    }
}

/// `x + 2 * 3 > x + 6 ∧ a * b ≠ b * a`: a fold, a mirror, a swap, and
/// hash-consing, all UNSAT.
fn unsat_term_cert() -> TermCertificate {
    let mut s = Solver::new();
    s.assert(BoolTerm::Ugt(
        b(BvTerm::Add(
            b(var("x")),
            b(BvTerm::Mul(b(konst(2)), b(konst(3)))),
        )),
        b(BvTerm::Add(b(var("x")), b(konst(6)))),
    ));
    s.assert(BoolTerm::Ne(
        b(BvTerm::Mul(b(var("a")), b(var("b")))),
        b(BvTerm::Mul(b(var("b")), b(var("a")))),
    ));
    match s.check_with_term() {
        TermCheckResult::Unsat(c) => c,
        other => panic!("expected Unsat with term, got {other:?}"),
    }
}

/// `a + b = 9 ∧ b > a ∧ a * 2 = b`: the unique model `a = 3, b = 6`.
fn sat_term_cert() -> TermSatCertificate {
    let mut s = Solver::new();
    s.assert(BoolTerm::Eq(
        b(BvTerm::Add(b(var("a")), b(var("b")))),
        b(konst(9)),
    ));
    s.assert(BoolTerm::Ugt(b(var("b")), b(var("a"))));
    s.assert(BoolTerm::Eq(
        b(BvTerm::Mul(b(var("a")), b(konst(2)))),
        b(var("b")),
    ));
    match s.check_with_term() {
        TermCheckResult::Sat(c) => c,
        other => panic!("expected Sat with term, got {other:?}"),
    }
}

// rivet: verifies VER-069
/// Round trip: emit → parse (four hashes verified) → the reconstructed
/// certificate re-checks through the trusted term check; the v2 blocks and
/// hashes are byte-for-byte those of `to_cert_v2` on the same certificate.
#[test]
fn v3_bundle_round_trips_and_rechecks_the_term() {
    let cert = unsat_term_cert();
    let json = cert.to_cert_v3(&attests());
    let v: serde_json::Value = serde_json::from_str(&json).unwrap();
    assert_eq!(v["format"], "ordeal-cert/v3");
    assert_eq!(v["verdict"], "unsat");
    assert_eq!(v["term"]["encoding"], crate::query::TERM_ENCODING);
    assert_eq!(v["term"]["sha256"], cert.term.sha256());
    assert_eq!(v["term"]["num_nodes"], cert.term.nodes.len());
    assert_eq!(
        v["term"]["map"].as_array().unwrap().len(),
        cert.term.nodes.len()
    );
    assert_eq!(v["term"]["vars"].as_array().unwrap().len(), 3);
    assert_eq!(v["recheck"]["min_version"], "0.31.0");
    let cmd = v["recheck"]["cmd"].as_str().unwrap();
    assert!(cmd.contains("check_term_dag") && cmd.contains("check_query"));
    let bundle = TermCertificate::from_cert_v3(&json).expect("v3 bundle parses");
    assert_eq!(bundle.attests, attests());
    assert!(bundle.certificate.term == cert.term);
    assert!(bundle.certificate.query.query == cert.query.query);
    bundle.recheck().expect("term re-check passes");
    bundle
        .certificate
        .query
        .recheck()
        .expect("the v2 certificate inside re-checks");
    let v2: serde_json::Value = serde_json::from_str(&cert.query.to_cert_v2(&attests())).unwrap();
    assert_eq!(v2["format"], "ordeal-cert/v2");
    for key in ["problem", "proof", "query", "attests"] {
        assert_eq!(v2[key], v[key], "{key}");
    }
    assert_eq!(
        v2["recheck"]["problem_sha256"],
        v["recheck"]["problem_sha256"]
    );
    assert_eq!(v2["recheck"]["proof_sha256"], v["recheck"]["proof_sha256"]);
    assert!(v2.get("term").is_none(), "v2 carries no term block");
}

// rivet: verifies VER-069
/// The SAT round trip: six hashes, the term and model re-check, and the v2
/// SAT bundle of the same witness is the same minus the term block.
#[test]
fn v3_sat_bundle_round_trips_and_rechecks_the_model_and_term() {
    let cert = sat_term_cert();
    let json = cert.to_cert_v3(&attests());
    let v: serde_json::Value = serde_json::from_str(&json).unwrap();
    assert_eq!(v["format"], "ordeal-cert/v3");
    assert_eq!(v["verdict"], "sat");
    assert_eq!(v["term"]["sha256"], cert.term.sha256());
    assert_eq!(v["recheck"]["min_version"], "0.31.0");
    assert!(
        v["recheck"]["cmd"]
            .as_str()
            .unwrap()
            .contains("check_input_value")
    );
    let bundle = TermSatCertificate::from_cert_v3(&json).expect("v3 sat bundle parses");
    assert!(bundle.certificate.term == cert.term);
    assert!(bundle.certificate.query.query == cert.query.query);
    assert!(bundle.certificate.query.inputs == cert.query.inputs);
    bundle.recheck().expect("term + model re-check passes");
    let v2: serde_json::Value = serde_json::from_str(&cert.query.to_cert_v2(&attests())).unwrap();
    for key in ["problem", "model", "witness", "query", "inputs"] {
        assert_eq!(v2[key], v[key], "{key}");
    }
    assert!(v2.get("term").is_none());
}

// rivet: verifies VER-069
/// Nobody silently downgrades or upgrades: every older reader refuses a v3
/// bundle by its `format`, the v3 readers refuse v1 and v2 bundles, and the
/// two v3 readers refuse each other's verdict.
#[test]
fn v2_and_v3_readers_refuse_each_other() {
    let unsat = unsat_term_cert();
    let sat = sat_term_cert();
    let v3_unsat = unsat.to_cert_v3(&attests());
    let v3_sat = sat.to_cert_v3(&attests());
    let v2_unsat = unsat.query.to_cert_v2(&attests());
    let v2_sat = sat.query.to_cert_v2(&attests());
    let v1_unsat = unsat.query.certificate.to_cert_v1(&attests());
    let v1_sat = sat.query.witness.to_cert_v1(&attests());
    // Older readers on v3.
    assert!(matches!(
        QueryCertificate::from_cert_v2(&v3_unsat),
        Err(BundleError::WrongFormat(_))
    ));
    assert!(matches!(
        QuerySatCertificate::from_cert_v2(&v3_sat),
        Err(BundleError::WrongFormat(_))
    ));
    assert!(matches!(
        crate::solver::Certificate::from_cert_v1(&v3_unsat),
        Err(BundleError::WrongFormat(_))
    ));
    assert!(matches!(
        SatCertificate::from_cert_v1(&v3_sat),
        Err(BundleError::WrongFormat(_))
    ));
    // v3 readers on older bundles.
    for older in [&v2_unsat, &v1_unsat, &v2_sat, &v1_sat] {
        assert!(matches!(
            TermCertificate::from_cert_v3(older),
            Err(BundleError::WrongFormat(_))
        ));
        assert!(matches!(
            TermSatCertificate::from_cert_v3(older),
            Err(BundleError::WrongFormat(_))
        ));
    }
    // v3 readers on the other verdict.
    assert!(matches!(
        TermCertificate::from_cert_v3(&v3_sat),
        Err(BundleError::WrongVerdict(_))
    ));
    assert!(matches!(
        TermSatCertificate::from_cert_v3(&v3_unsat),
        Err(BundleError::WrongVerdict(_))
    ));
}

// rivet: verifies VER-069
/// Tamper controls with the `problem`, `proof` and `query` blocks UNTOUCHED
/// (the v2 recheck of the same pair still passes): a tampered map, two
/// variables aliased, and a wrong fold — each re-signed so integrity
/// passes — fail the v3 recheck; a stale term hash fails at parse.
#[test]
fn v3_tampered_term_fails_recheck_with_query_and_proof_untouched() {
    let fresh = unsat_term_cert();
    let dag = &fresh.query.query;
    let is_op = |n: &ordeal_lrat::blast_kernel::DagNode| {
        !matches!(
            n,
            ordeal_lrat::blast_kernel::DagNode::Var(_)
                | ordeal_lrat::blast_kernel::DagNode::Const(_, _)
        )
    };
    // A tampered map entry, re-signed by the writer.
    let mut cert = fresh.clone();
    let i = (0..cert.term.nodes.len())
        .find(|&i| is_op(&cert.term.nodes[i]) && cert.term.map[i] != crate::dag::NO_IMAGE)
        .unwrap();
    cert.term.map[i] = (cert.term.map[i] + 1) % dag.nodes.len();
    let json = cert.to_cert_v3(&attests());
    let bundle = TermCertificate::from_cert_v3(&json).expect("integrity passes: re-signed");
    assert!(matches!(bundle.recheck(), Err(TermRecheckError::Term(_))));
    bundle
        .certificate
        .query
        .recheck()
        .expect("the v2 pair inside still re-checks");
    // Two variables aliased.
    let mut cert = fresh.clone();
    let node_of = |name: &str| {
        cert.term
            .vars
            .iter()
            .find(|(n, _, _)| n == name)
            .map(|(_, _, node)| *node)
            .unwrap()
    };
    let (na, nb) = (node_of("a"), node_of("b"));
    cert.term.map[nb] = cert.term.map[na];
    let bundle = TermCertificate::from_cert_v3(&cert.to_cert_v3(&attests())).unwrap();
    assert!(matches!(
        bundle.recheck(),
        Err(TermRecheckError::Term(TermError::VarMismatch { .. }))
    ));
    // A wrong fold: the product replaced by a sum in the term.
    let mut cert = fresh.clone();
    let mul = (0..cert.term.nodes.len())
        .find(|&i| {
            matches!(
                cert.term.nodes[i],
                ordeal_lrat::blast_kernel::DagNode::Mul(_, _)
            ) && cert.term.map[i] != crate::dag::NO_IMAGE
                && matches!(
                    dag.nodes[cert.term.map[i]],
                    ordeal_lrat::blast_kernel::DagNode::Const(_, _)
                )
        })
        .unwrap();
    if let ordeal_lrat::blast_kernel::DagNode::Mul(x, y) = cert.term.nodes[mul] {
        cert.term.nodes[mul] = ordeal_lrat::blast_kernel::DagNode::Add(x, y);
    }
    let bundle = TermCertificate::from_cert_v3(&cert.to_cert_v3(&attests())).unwrap();
    assert!(matches!(
        bundle.recheck(),
        Err(TermRecheckError::Term(TermError::FoldMismatch { .. }))
    ));
    bundle.certificate.query.recheck().unwrap();
    // A stale term hash (the map edited in the JSON without re-signing).
    let json = fresh.to_cert_v3(&attests());
    let mut v: serde_json::Value = serde_json::from_str(&json).unwrap();
    let old = v["term"]["map"][i].as_u64().unwrap();
    v["term"]["map"][i] = serde_json::Value::from((old + 1) % dag.nodes.len() as u64);
    assert!(matches!(
        TermCertificate::from_cert_v3(&v.to_string()),
        Err(BundleError::HashMismatch("term"))
    ));
    // On `sat`: the term's variable map swapped — the proven binding
    // rejects the model, the v2 SAT bundle inside is untouched.
    let mut cert = sat_term_cert();
    let (ia, ib) = (
        cert.term
            .vars
            .iter()
            .position(|(n, _, _)| n == "a")
            .unwrap(),
        cert.term
            .vars
            .iter()
            .position(|(n, _, _)| n == "b")
            .unwrap(),
    );
    let (na, nb) = (cert.term.vars[ia].2, cert.term.vars[ib].2);
    cert.term.vars[ia].2 = nb;
    cert.term.vars[ib].2 = na;
    let bundle = TermSatCertificate::from_cert_v3(&cert.to_cert_v3(&attests())).unwrap();
    assert!(matches!(
        bundle.recheck(),
        Err(TermModelRecheckError::Binding(_))
    ));
    bundle.certificate.query.recheck().unwrap();
}
