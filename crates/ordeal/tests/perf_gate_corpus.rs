//! The real-consumer-query gate (#283, TR-081): every query in
//! `tests/perf_corpus/` is solved, its verdict re-checked, and its time and
//! proof size held to `tests/perf_corpus/budgets.json`.
//!
//! Ignored in the default (debug) run: debug-build times say nothing and
//! the synth I64Popcnt query alone takes minutes unoptimized. The
//! "Perf + proof-size gate (#283)" CI job runs it in the release build:
//!
//! ```text
//! cargo test --release -p ordeal --test perf_gate_corpus -- --ignored --exact real_consumer_queries_within_budgets --nocapture
//! ```
//!
//! The knobs (`ORDEAL_PERF_GATE_*`) are documented in `perf_gate_lib`.

mod perf_gate_lib;

use perf_gate_lib::*;
use std::collections::BTreeMap;

// rivet: verifies VER-095
#[test]
#[ignore = "release-build gate; run by the Perf + proof-size gate CI job"]
fn real_consumer_queries_within_budgets() {
    let dir = corpus_dir();
    let manifest = load_manifest(&dir).unwrap_or_else(|e| panic!("{e}"));
    let budget_path = std::env::var_os("ORDEAL_PERF_GATE_BUDGETS")
        .map(Into::into)
        .unwrap_or_else(|| dir.join("budgets.json"));
    let budgets = load_budgets(&budget_path).unwrap_or_else(|e| panic!("{e}"));
    let mut failures = set_agreement(&manifest.entries, &budgets);

    let only: Option<Vec<String>> = std::env::var("ORDEAL_PERF_GATE_ONLY").ok().map(|v| {
        v.split(',')
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty())
            .collect()
    });
    let selected: Vec<&Entry> = manifest
        .entries
        .iter()
        .filter(|e| only.as_ref().is_none_or(|o| o.contains(&e.id)))
        .collect();
    if let Some(o) = &only {
        eprintln!(
            "perf gate: SUBSET RUN ({} of {} queries) — not a gate pass",
            selected.len(),
            manifest.entries.len()
        );
        for id in o {
            if !manifest.entries.iter().any(|e| &e.id == id) {
                failures.push(format!("ORDEAL_PERF_GATE_ONLY names unknown query {id}"));
            }
        }
    }
    if selected.is_empty() {
        failures.push("0 queries checked: an empty run is not a pass".into());
    }
    let inj = Injection::from_env();
    if inj.slowdown > 1 || inj.inflate_lrat > 0 {
        eprintln!(
            "perf gate: INJECTED slowdown x{} / LRAT +{} bytes (planted control)",
            inj.slowdown, inj.inflate_lrat
        );
    }

    println!(
        "{:<34} {:<6} {:<4} {:<6} {:>9} {:>8} {:>8} {:>10} {:>7}  status",
        "query", "from", "real", "verdct", "time ms", "budget", "clauses", "lrat B", "lines"
    );
    let mut suggested = BTreeMap::new();
    let mut checked = 0usize;
    let mut total_ms = 0.0;
    for e in &selected {
        let Some(budget) = budgets.get(&e.id) else {
            continue;
        };
        let m = match measure(e, inj) {
            Ok(m) => m,
            Err(err) => {
                println!("{:<34} ERROR {err}", e.id);
                failures.push(err);
                continue;
            }
        };
        checked += 1;
        total_ms += m.time_ms;
        let errs = judge(e, budget, &m);
        println!(
            "{:<34} {:<6} {:<4} {:<6} {:>9.1} {:>8} {:>8} {:>10} {:>7}  {}",
            e.id,
            e.consumer,
            if e.real { "yes" } else { "no" },
            m.verdict.as_str(),
            m.time_ms,
            budget.time_ms,
            m.cnf_clauses,
            m.lrat_bytes.map_or("-".into(), |b| b.to_string()),
            m.lrat_lines.map_or("-".into(), |b| b.to_string()),
            if errs.is_empty() { "ok" } else { "FAIL" }
        );
        suggested.insert(
            e.id.clone(),
            serde_json::json!({
                "time_ms": time_budget(m.time_ms),
                "measured_ms": (m.time_ms * 10.0).round() / 10.0,
                "cnf_clauses": m.cnf_clauses,
                "lrat_bytes": m.lrat_bytes,
                "lrat_lines": m.lrat_lines,
            }),
        );
        failures.extend(errs);
    }
    let real = selected.iter().filter(|e| e.real).count();
    println!(
        "perf gate: {checked} queries checked ({real} real, {} synthetic), {total_ms:.0} ms solving",
        selected.len() - real
    );
    if checked == 0 && !selected.is_empty() {
        failures.push("0 queries checked".into());
    }
    if std::env::var_os("ORDEAL_PERF_GATE_SUGGEST").is_some() {
        println!("{}", serde_json::to_string_pretty(&suggested).unwrap());
    }
    if !failures.is_empty() {
        for f in &failures {
            println!("FAIL {f}");
        }
        panic!("perf gate: {} failure(s)", failures.len());
    }
}
