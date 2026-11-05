//! `ordeal-cert/v1`..`v4` — the stable certificate bundles (issue #91 /
//! TR-025 and successors). Since TR-075 the envelopes, their emitters
//! (`to_cert_v*`) and hash-verifying readers (`from_cert_v*`) live in
//! the solver-free `ordeal-cert` crate (`ordeal_cert::cert_bundle`,
//! its `json` feature), re-exported here unchanged.

pub use ordeal_cert::cert_bundle::*;
// 0.20.0 paths (`cert_bundle::WitnessCheckResult`) keep working.
pub use crate::witness::WitnessCheckResult;

// rivet: verifies VER-027
#[cfg(test)]
mod tests {
    use super::*;
    use crate::cnf::CnfFormula;
    use crate::query::*;
    use crate::solver::Certificate;
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
