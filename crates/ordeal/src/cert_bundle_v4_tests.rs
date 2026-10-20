//! TR-072: the `ordeal-cert/v4` bundles — round trips, the ext block's
//! integrity, the cross-reader refusals (v1/v2/v3 refuse v4 and v4
//! refuses v3, by `format`), a tampered ext block failing the recheck,
//! and the v3 bundle of a core query byte-for-byte unchanged.

use crate::cert_bundle::{Attests, BundleError};
use crate::query::{SliverCertificate, SliverCheckResult, SliverSatCertificate, TermCertificate};
use crate::sliver::{ArrayTerm, ExtBoolTerm, ExtBvTerm, ExtOp};
use crate::{BoolTerm, BvTerm, Solver, Sort};

fn v8(name: &str) -> ExtBvTerm {
    ExtBvTerm::Core(BvTerm::Var {
        name: name.into(),
        sort: Sort::new(8),
    })
}

fn v32(name: &str) -> ExtBvTerm {
    ExtBvTerm::Core(BvTerm::Var {
        name: name.into(),
        sort: Sort::new(32),
    })
}

fn c32(v: u128) -> ExtBvTerm {
    ExtBvTerm::Core(BvTerm::Const {
        value: v,
        sort: Sort::new(32),
    })
}

fn sel(a: ArrayTerm, i: ExtBvTerm) -> ExtBvTerm {
    ExtBvTerm::Select {
        array: Box::new(a),
        index: Box::new(i),
    }
}

fn store(a: ArrayTerm, i: ExtBvTerm, v: ExtBvTerm) -> ArrayTerm {
    ArrayTerm::Store {
        array: Box::new(a),
        index: Box::new(i),
        value: Box::new(v),
    }
}

fn mem() -> ArrayTerm {
    ArrayTerm::Var { name: "mem".into() }
}

fn attests() -> Attests {
    Attests {
        kind: "translation_validation".into(),
        claim: "the memory obligation as asked is refuted".into(),
        standards: vec!["ISO-26262:8-11".into()],
    }
}

/// loom's shape: `mem[b+1 := v1][b+0 := v0][b+0] ≠ v0`, UNSAT, with a
/// symbolic mux and a congruence root.
fn unsat_sliver_cert() -> SliverCertificate {
    let add = |a, b| ExtBvTerm::Op(Box::new(ExtOp::Add(a, b)));
    let m = store(
        store(mem(), add(v32("b"), c32(1)), v8("v1")),
        add(v32("b"), c32(0)),
        v8("v0"),
    );
    let q = [ExtBoolTerm::Ne(sel(m, add(v32("b"), c32(0))), v8("v0"))];
    match Solver::from_sliver(&q).unwrap().check_sliver_with_term() {
        SliverCheckResult::Unsat(c) => c,
        other => panic!("expected Unsat with ext, got {other:?}"),
    }
}

/// `mem[i] ≠ mem[j] ∧ f(mem[i]) = 3`: SAT, two reads and a call.
fn sat_sliver_cert() -> SliverSatCertificate {
    let q = [
        ExtBoolTerm::Ne(sel(mem(), v32("i")), sel(mem(), v32("j"))),
        ExtBoolTerm::Eq(
            ExtBvTerm::PureCall {
                name: "f".into(),
                args: vec![sel(mem(), v32("i"))],
                sort: Sort::new(8),
            },
            ExtBvTerm::Core(BvTerm::Const {
                value: 3,
                sort: Sort::new(8),
            }),
        ),
    ];
    match Solver::from_sliver(&q).unwrap().check_sliver_with_term() {
        SliverCheckResult::Sat(c) => c,
        other => panic!("expected Sat with ext, got {other:?}"),
    }
}

// rivet: verifies VER-072
/// Round trip: emit → parse (five hashes verified) → the reconstructed
/// certificate re-checks through the trusted sliver check; the v3 blocks
/// and hashes are byte-for-byte those of `to_cert_v3` on the term
/// certificate inside.
#[test]
fn v4_bundle_round_trips_and_rechecks_the_extended_query() {
    let cert = unsat_sliver_cert();
    let json = cert.to_cert_v4(&attests());
    let v: serde_json::Value = serde_json::from_str(&json).unwrap();
    assert_eq!(v["format"], "ordeal-cert/v4");
    assert_eq!(v["verdict"], "unsat");
    assert_eq!(v["ext"]["encoding"], crate::query::EXT_ENCODING);
    assert_eq!(v["ext"]["sha256"], cert.sliver.sha256());
    assert_eq!(v["ext"]["num_nodes"], cert.sliver.ext.nodes.len());
    assert_eq!(v["ext"]["arrays"].as_array().unwrap().len(), 1);
    assert_eq!(
        v["ext"]["reads"].as_array().unwrap().len(),
        cert.sliver.reads.len()
    );
    assert_eq!(v["term"]["encoding"], crate::query::TERM_ENCODING_V2);
    assert_eq!(v["recheck"]["min_version"], "0.33.0");
    let cmd = v["recheck"]["cmd"].as_str().unwrap();
    assert!(
        cmd.contains("check_sliver_lowering")
            && cmd.contains("check_term_dag")
            && cmd.contains("check_query")
    );
    let bundle = SliverCertificate::from_cert_v4(&json).expect("v4 bundle parses");
    assert_eq!(bundle.attests, attests());
    assert!(bundle.certificate.sliver == cert.sliver);
    assert!(bundle.certificate.term.term == cert.term.term);
    bundle.recheck().expect("extended re-check passes");
    bundle
        .certificate
        .term
        .recheck()
        .expect("the v3 certificate inside re-checks");
    let v3: serde_json::Value = serde_json::from_str(&cert.term.to_cert_v3(&attests())).unwrap();
    assert_eq!(v3["format"], "ordeal-cert/v3");
    for key in ["problem", "proof", "query", "term", "attests"] {
        assert_eq!(v3[key], v[key], "{key}");
    }
    assert!(v3.get("ext").is_none(), "v3 carries no ext block");
}

// rivet: verifies VER-072
/// The SAT round trip: the ext block, the extended model, and the
/// recheck through the pullback.
#[test]
fn v4_sat_bundle_round_trips_and_rechecks_the_extended_model() {
    let cert = sat_sliver_cert();
    let json = cert.to_cert_v4(&attests());
    let v: serde_json::Value = serde_json::from_str(&json).unwrap();
    assert_eq!(v["format"], "ordeal-cert/v4");
    assert_eq!(v["verdict"], "sat");
    assert_eq!(v["ext"]["sha256"], cert.sliver.sha256());
    assert_eq!(v["ext_model"]["encoding"], "ext-model");
    assert_eq!(v["recheck"]["min_version"], "0.33.0");
    let bundle = SliverSatCertificate::from_cert_v4(&json).expect("v4 SAT bundle parses");
    assert!(bundle.certificate.sliver == cert.sliver);
    assert_eq!(bundle.certificate.model.arrays, cert.model.arrays);
    assert_eq!(bundle.certificate.model.calls, cert.model.calls);
    bundle.recheck().expect("extended SAT re-check passes");
    // An extended model that is not the pullback is refused.
    let mut forged = bundle.certificate.clone();
    let cells = forged.model.arrays.get_mut("mem").expect("mem cells");
    let (&idx, &byte) = cells.iter().next().expect("a touched cell");
    cells.insert(idx, byte.wrapping_add(1));
    assert!(matches!(
        forged.recheck(),
        Err(crate::query::SliverModelRecheckError::Model)
    ));
}

// rivet: verifies VER-072
/// Readers refuse each other by `format`: v1, v2 and v3 refuse a v4
/// bundle; the v4 reader refuses a v3 (and a v1) bundle. No silent
/// downgrade either way.
#[test]
fn v4_and_earlier_readers_refuse_each_other() {
    let cert = unsat_sliver_cert();
    let v4 = cert.to_cert_v4(&attests());
    assert!(matches!(
        crate::Certificate::from_cert_v1(&v4),
        Err(BundleError::WrongFormat(f)) if f == "ordeal-cert/v4"
    ));
    assert!(matches!(
        crate::query::QueryCertificate::from_cert_v2(&v4),
        Err(BundleError::WrongFormat(f)) if f == "ordeal-cert/v4"
    ));
    assert!(matches!(
        TermCertificate::from_cert_v3(&v4),
        Err(BundleError::WrongFormat(f)) if f == "ordeal-cert/v4"
    ));
    let v3 = cert.term.to_cert_v3(&attests());
    assert!(matches!(
        SliverCertificate::from_cert_v4(&v3),
        Err(BundleError::WrongFormat(f)) if f == "ordeal-cert/v3"
    ));
    let v1 = cert.term.query.certificate.to_cert_v1(&attests());
    assert!(matches!(
        SliverCertificate::from_cert_v4(&v1),
        Err(BundleError::WrongFormat(f)) if f == "ordeal-cert/v1"
    ));
    let sat = sat_sliver_cert().to_cert_v4(&attests());
    assert!(matches!(
        crate::query::TermSatCertificate::from_cert_v3(&sat),
        Err(BundleError::WrongFormat(f)) if f == "ordeal-cert/v4"
    ));
    assert!(matches!(
        SliverCertificate::from_cert_v4(&sat),
        Err(BundleError::WrongVerdict(v)) if v == "sat"
    ));
}

// rivet: verifies VER-072
/// A tampered ext block: an edited map entry fails the hash; the same
/// edit with the hash recomputed fails the trusted recheck (the bundle
/// parses, the sliver check rejects). A wrong read share and a captured
/// name likewise, and the v3 recheck inside is untouched by all three.
#[test]
fn a_tampered_ext_block_fails_the_recheck() {
    let cert = unsat_sliver_cert();
    let json = cert.to_cert_v4(&attests());
    let mut v: serde_json::Value = serde_json::from_str(&json).unwrap();
    let sel_node = cert
        .sliver
        .ext
        .nodes
        .iter()
        .position(|n| matches!(n, ordeal_lrat::ExtNode::Select(..)))
        .expect("a select");
    let was = v["ext"]["map"][sel_node].as_u64().unwrap();
    v["ext"]["map"][sel_node] = serde_json::Value::from(if was == 0 { 1u64 } else { 0 });
    assert!(matches!(
        SliverCertificate::from_cert_v4(&v.to_string()),
        Err(BundleError::HashMismatch("ext"))
    ));
    // Recompute the hash over the tampered block: the recheck refuses.
    let mut tampered = cert.sliver.clone();
    tampered.map[sel_node] = if was == 0 { 1 } else { 0 };
    v["ext"]["sha256"] = serde_json::Value::String(tampered.sha256());
    let bundle = SliverCertificate::from_cert_v4(&v.to_string()).expect("hash agrees");
    assert!(matches!(
        bundle.recheck(),
        Err(crate::query::SliverRecheckError::Sliver(
            ordeal_lrat::SliverCheckError::ChainMismatch { .. }
        ))
    ));
    bundle
        .certificate
        .term
        .recheck()
        .expect("the v3 certificate inside is untouched");
    // A captured name: the first variable registered as the read.
    let mut captured = cert.sliver.clone();
    let (_, _, node) = captured.ext.vars[0].clone();
    captured.reads[0] = captured.map[node];
    let forged = SliverCertificate {
        term: cert.term.clone(),
        sliver: captured,
    };
    assert!(matches!(
        forged.recheck(),
        Err(crate::query::SliverRecheckError::Sliver(_))
    ));
    // A wrong read share needs two reads: the SAT fixture has them.
    let sat = sat_sliver_cert();
    let mut shared = sat.sliver.clone();
    shared.reads[3] = shared.reads[0];
    let forged = SliverSatCertificate {
        term: sat.term.clone(),
        sliver: shared,
        model: sat.model.clone(),
    };
    assert!(matches!(
        forged.recheck(),
        Err(crate::query::SliverModelRecheckError::Sliver(
            ordeal_lrat::SliverCheckError::ReadTable { entry: 1 }
        ))
    ));
}

// rivet: verifies VER-072
/// A core query's v3 bundle is unchanged by TR-072: `ordeal-term/v1`, no
/// ext block, the same hashes as before (the term block is not shared).
#[test]
fn core_queries_keep_their_v3_bundles() {
    let mut s = Solver::new();
    s.assert(BoolTerm::Ne(
        Box::new(BvTerm::Add(
            Box::new(BvTerm::Var {
                name: "x".into(),
                sort: Sort::new(8),
            }),
            Box::new(BvTerm::Var {
                name: "y".into(),
                sort: Sort::new(8),
            }),
        )),
        Box::new(BvTerm::Add(
            Box::new(BvTerm::Var {
                name: "y".into(),
                sort: Sort::new(8),
            }),
            Box::new(BvTerm::Var {
                name: "x".into(),
                sort: Sort::new(8),
            }),
        )),
    ));
    let cert = match s.check_with_term() {
        crate::query::TermCheckResult::Unsat(c) => c,
        other => panic!("expected Unsat, got {other:?}"),
    };
    assert!(!cert.term.shared);
    let v: serde_json::Value = serde_json::from_str(&cert.to_cert_v3(&attests())).unwrap();
    assert_eq!(v["format"], "ordeal-cert/v3");
    assert_eq!(v["term"]["encoding"], crate::query::TERM_ENCODING);
    assert!(v.get("ext").is_none());
    assert!(matches!(
        s.check_sliver_with_term(),
        SliverCheckResult::Unknown
    ));
}
