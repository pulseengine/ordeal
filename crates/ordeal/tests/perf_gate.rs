// rivet: verifies VER-095
//! Self-tests of the performance and proof-size gate (#283, TR-081), in the
//! default run: the corpus manifest and the budgets agree as sets and carry
//! provenance; the gate's judgement goes red on every planted defect (slow,
//! larger proof, smaller proof, wrong verdict, unknown, empty corpus,
//! missing or extra budget); and the quick queries reproduce their pinned
//! proof sizes in this build too. The full timed run over the real corpus
//! is `tests/perf_gate_corpus.rs` (release build, its own CI job).

mod perf_gate_lib;

use perf_gate_lib::*;
use std::collections::{BTreeMap, BTreeSet};

fn corpus() -> (Manifest, BTreeMap<String, Budget>) {
    let dir = corpus_dir();
    let m = load_manifest(&dir).unwrap_or_else(|e| panic!("{e}"));
    let b = load_budgets(&dir.join("budgets.json")).unwrap_or_else(|e| panic!("{e}"));
    (m, b)
}

#[test]
fn manifest_and_budgets_agree_and_carry_provenance() {
    let (m, b) = corpus();
    assert_eq!(set_agreement(&m.entries, &b), Vec::<String>::new());
    // Real queries from these consumers; spar has none to give (no ordeal
    // dependency on its main) and is declared uncovered, not faked.
    let real: BTreeSet<&str> = m
        .entries
        .iter()
        .filter(|e| e.real)
        .map(|e| e.consumer.as_str())
        .collect();
    assert_eq!(real, BTreeSet::from(["gale", "loom", "synth"]));
    assert!(
        m.uncovered.iter().any(|r| r == "pulseengine/spar"),
        "spar must be declared uncovered"
    );
    assert!(
        m.entries
            .iter()
            .filter(|e| !e.real)
            .all(|e| e.consumer == "spar")
    );
    // #308's data point is in the corpus; #314's query is not.
    assert!(m.entries.iter().any(|e| e.id == "synth/i64_popcnt"));
    // Both verdict directions are exercised.
    assert!(m.entries.iter().any(|e| e.expect == Verdict::Sat));
    assert!(m.entries.iter().any(|e| e.expect == Verdict::Unsat));
}

fn entry(expect: Verdict) -> Entry {
    Entry {
        id: "planted/q".into(),
        consumer: "synth".into(),
        real: true,
        file: None,
        sha256: None,
        driver: Driver::ApiDag,
        expect,
    }
}

fn budget() -> Budget {
    Budget {
        time_ms: 1000,
        cnf_clauses: 500,
        lrat_bytes: Some(4000),
        lrat_lines: Some(40),
    }
}

fn meas(verdict: Verdict, time_ms: f64, lrat: u64) -> Measurement {
    Measurement {
        verdict,
        time_ms,
        cnf_clauses: 500,
        lrat_bytes: Some(lrat),
        lrat_lines: Some(40),
    }
}

#[test]
fn the_judgement_passes_a_query_on_budget() {
    assert!(
        judge(
            &entry(Verdict::Unsat),
            &budget(),
            &meas(Verdict::Unsat, 999.0, 4000)
        )
        .is_empty()
    );
}

#[test]
fn planted_slowdown_is_red() {
    let e = judge(
        &entry(Verdict::Unsat),
        &budget(),
        &meas(Verdict::Unsat, 1000.5, 4000),
    );
    assert!(
        e.len() == 1 && e[0].contains("exceeds the budget of 1000 ms"),
        "{e:?}"
    );
}

#[test]
fn planted_lrat_inflation_by_one_byte_is_red() {
    let e = judge(
        &entry(Verdict::Unsat),
        &budget(),
        &meas(Verdict::Unsat, 1.0, 4001),
    );
    assert!(
        e.len() == 1 && e[0].contains("lrat_bytes 4001 exceeds the budget 4000 (+1)"),
        "{e:?}"
    );
}

#[test]
fn a_smaller_proof_must_lower_its_budget() {
    let e = judge(
        &entry(Verdict::Unsat),
        &budget(),
        &meas(Verdict::Unsat, 1.0, 3999),
    );
    assert!(
        e.len() == 1 && e[0].contains("lower the budget to 3999"),
        "{e:?}"
    );
}

#[test]
fn a_changed_clause_count_is_red() {
    let mut m = meas(Verdict::Unsat, 1.0, 4000);
    m.cnf_clauses = 501;
    let e = judge(&entry(Verdict::Unsat), &budget(), &m);
    assert!(e.len() == 1 && e[0].contains("cnf_clauses 501"), "{e:?}");
}

#[test]
fn a_wrong_or_unknown_verdict_is_red() {
    let e = judge(
        &entry(Verdict::Unsat),
        &budget(),
        &meas(Verdict::Sat, 1.0, 4000),
    );
    assert!(
        e.iter()
            .any(|x| x.contains("verdict sat but the manifest expects unsat")),
        "{e:?}"
    );
    let e = judge(
        &entry(Verdict::Unsat),
        &budget(),
        &meas(Verdict::Unknown, 1.0, 4000),
    );
    assert!(e.iter().any(|x| x.contains("verdict unknown")), "{e:?}");
}

#[test]
fn an_empty_corpus_and_set_disagreement_are_red() {
    let e = set_agreement(&[], &BTreeMap::new());
    assert!(
        e.iter().any(|x| x.contains("0 queries is not a pass")),
        "{e:?}"
    );

    let (m, b) = corpus();
    let mut fewer = b.clone();
    let dropped = fewer.keys().next().unwrap().clone();
    fewer.remove(&dropped);
    let e = set_agreement(&m.entries, &fewer);
    assert_eq!(
        e,
        vec![format!("{dropped}: in manifest.json but has no budget")]
    );

    let mut more = b;
    more.insert("ghost/q".into(), budget());
    let e = set_agreement(&m.entries, &more);
    assert_eq!(
        e,
        vec!["ghost/q: has a budget but is not in manifest.json".to_string()]
    );
}

#[test]
fn budgets_are_parsed_strictly() {
    assert!(parse_budgets(r#"{"schema":"other","queries":{}}"#).is_err());
    assert!(
        parse_budgets(
            r#"{"schema":"ordeal-perf-budgets/v1","queries":{"a":{"time_ms":0,"cnf_clauses":1}}}"#
        )
        .is_err()
    );
    assert!(
        parse_budgets(r#"{"schema":"ordeal-perf-budgets/v1","queries":{"a":{"cnf_clauses":1}}}"#)
            .is_err()
    );
}

#[test]
fn the_published_time_policy() {
    assert_eq!(TIME_FACTOR, 5);
    assert_eq!(TIME_FLOOR_MS, 500);
    assert_eq!(time_budget(0.2), 600); // floor: 1 + 500, rounded up
    assert_eq!(time_budget(6830.0), 34200); // 5x
}

#[test]
fn every_api_dag_file_reads_back() {
    let (m, _) = corpus();
    let mut n = 0;
    for e in m
        .entries
        .iter()
        .filter(|e| matches!(e.driver, Driver::ApiDag))
    {
        let text = std::fs::read_to_string(e.file.as_ref().unwrap()).unwrap();
        let terms = read_dag(&text).unwrap_or_else(|err| panic!("{}: {err}", e.id));
        assert!(!terms.is_empty());
        n += 1;
    }
    assert!(n > 0);
}

/// The proof-size pins hold in this (debug) build too, for every query
/// whose release time is small: sizes do not depend on the profile.
#[test]
fn quick_queries_reproduce_their_pinned_proof_sizes() {
    let (m, b) = corpus();
    let quick: Vec<&Entry> = m
        .entries
        .iter()
        .filter(|e| b[&e.id].time_ms <= 600)
        .collect();
    assert!(quick.len() >= 10, "only {} quick queries", quick.len());
    let mut errs = Vec::new();
    for e in quick {
        let got = measure(
            e,
            Injection {
                slowdown: 1,
                inflate_lrat: 0,
            },
        )
        .unwrap_or_else(|x| panic!("{x}"));
        // Time is the release job's business; here only the pins and the verdict.
        let mut pin = b[&e.id].clone();
        pin.time_ms = u64::MAX;
        errs.extend(judge(e, &pin, &got));
    }
    assert!(errs.is_empty(), "{errs:#?}");
}
