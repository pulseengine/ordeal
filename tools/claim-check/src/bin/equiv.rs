//! claim-check-equiv: the equivalence harness for the claim-check port.
//!
//! Runs the reference (`scripts/claim_check.py`) and the port on the same
//! inputs and requires identical stdout and exit codes.
//!
//!   CLAIM_CHECK_REF="python3 scripts/claim_check.py" \
//!   CLAIM_CHECK_NEW="wasmtime run --dir . claim-check.wasm" \
//!   claim-check-equiv [claims.yaml]          # run from the repository root
//!
//! Cases: the self-test; the real claims file; for every claim, one-claim
//! files with the claim mutated (claim text, doc, evidence list) and with each
//! evidence predicate mutated by kind, so every failure path is exercised;
//! structural files (no claims, duplicate / missing ids, a missing path).
//! Variant files are written beside the claims file as `.claim-equiv-N.yaml`
//! and removed afterwards.
//!
//! Exit 0 only when every case is identical, the count is non-zero, and the
//! reference's exit codes over the cases include 0, 1 and 2 (the mutants
//! really failed). Anything that keeps a command from running is a failure,
//! never a skip. Only stdout and the exit code are compared, not stderr.

use rivet_yaml::{Mapping, Value};
use std::path::Path;
use std::process::{Command, exit};

fn cmd_of(var: &str) -> Vec<String> {
    let v = std::env::var(var).unwrap_or_default();
    let parts: Vec<String> = v.split_whitespace().map(str::to_string).collect();
    if parts.is_empty() {
        eprintln!("claim-check-equiv: set {var} to a command");
        exit(2);
    }
    parts
}

fn run(cmd: &[String], args: &[String]) -> (Vec<u8>, i32) {
    match Command::new(&cmd[0]).args(&cmd[1..]).args(args).output() {
        Ok(o) => (o.stdout, o.status.code().unwrap_or(-1)),
        Err(e) => {
            eprintln!("claim-check-equiv: cannot run {}: {e}", cmd[0]);
            exit(2);
        }
    }
}

fn s(x: &str) -> Value {
    Value::from(x)
}

fn set(m: &mut Value, k: &str, v: Value) {
    if let Some(map) = m.as_mapping_mut() {
        map.insert(s(k), v);
    }
}

fn get_str(m: &Value, k: &str) -> Option<String> {
    m.get(k).and_then(Value::as_str).map(str::to_string)
}

fn doc_of(claims: Vec<Value>) -> Value {
    let mut top = Mapping::new();
    top.insert(s("claims"), Value::Sequence(claims));
    Value::Mapping(top)
}

/// Mutations of one side of set-equal / count-equals.
fn side_mutants(side: &Value) -> Vec<Value> {
    let mut out = Vec::new();
    if side.get("glob").is_some() {
        let mut a = side.clone();
        set(&mut a, "glob", s("zz-nowhere/*"));
        out.push(a);
        let mut b = side.clone();
        set(&mut b, "name", s("(zz-never)"));
        out.push(b);
    }
    if side.get("file").is_some() {
        let mut a = side.clone();
        set(&mut a, "pattern", s("(zz-never-matches)"));
        out.push(a);
        let mut b = side.clone();
        set(&mut b, "after", s("zz-no-such-marker"));
        out.push(b);
        let mut c = side.clone();
        set(&mut c, "file", s("zz-missing.md"));
        out.push(c);
    }
    out
}

/// Kind-specific mutations of one evidence predicate.
fn ev_mutants(ev: &Value) -> Vec<Value> {
    let kind = get_str(ev, "kind").unwrap_or_default();
    let mut out = Vec::new();
    let with = |k: &str, v: Value| {
        let mut e = ev.clone();
        set(&mut e, k, v);
        e
    };
    match kind.as_str() {
        "verbatim" => {
            match get_str(ev, "text") {
                Some(t) => out.push(with("text", s(&format!("{t} zz-mutant")))),
                None => out.push(with("text", s("zz-absent"))),
            }
            out.push(with("text", s("")));
        }
        "file-exists" => {
            let p = get_str(ev, "path").unwrap_or_default();
            out.push(with("path", s(&format!("{p}.zz"))));
        }
        "count-min" => {
            let n = ev.get("min").and_then(Value::as_i64).unwrap_or(0);
            out.push(with("min", Value::from(n + 1)));
            out.push(with("min", Value::from(n + 1_000_000)));
            out.push(with("pattern", s("zz-absent-pattern")));
            out.push(with("glob", s("zz-nowhere/*.x")));
        }
        "count-max" | "no-new" => {
            let k = if kind == "count-max" { "max" } else { "recorded" };
            out.push(with("pattern", s("(?s).")));
            out.push(with(k, Value::from(-1i64)));
            out.push(with("glob", s("zz-nowhere/*.x")));
            out.push(with("glob", Value::Sequence(vec![s("zz-nowhere/*.x"), s("zz2/*")])));
        }
        "set-equal" => {
            out.push(with("waive", Value::Sequence(vec![s("zz-waived")])));
            for which in ["left", "right"] {
                if let Some(side) = ev.get(which) {
                    for m in side_mutants(side) {
                        out.push(with(which, m));
                    }
                }
            }
        }
        "count-equals" => {
            if let Some(num) = ev.get("number") {
                let mut a = num.clone();
                set(&mut a, "pattern", s(r"(\d+) zz-never"));
                out.push(with("number", a));
                let mut b = num.clone();
                set(&mut b, "file", s("zz-missing.md"));
                out.push(with("number", b));
                let mut c = num.clone();
                set(&mut c, "pattern", s(r"(\d)"));
                out.push(with("number", c));
            }
            if let Some(side) = ev.get("set") {
                for m in side_mutants(side) {
                    out.push(with("set", m));
                }
            }
        }
        _ => {}
    }
    out.push(with("kind", s("zz-unknown-kind")));
    out
}

fn main() {
    let r = cmd_of("CLAIM_CHECK_REF");
    let n = cmd_of("CLAIM_CHECK_NEW");
    let claims_path = std::env::args().nth(1).unwrap_or_else(|| "claims.yaml".into());
    let dir = Path::new(&claims_path).parent().map(Path::to_path_buf).unwrap_or_default();
    let src = std::fs::read_to_string(&claims_path).unwrap_or_else(|e| {
        eprintln!("claim-check-equiv: {claims_path}: {e}");
        exit(2);
    });
    let data: Value = rivet_yaml::from_str(&src).unwrap_or_else(|e| {
        eprintln!("claim-check-equiv: {claims_path}: {e}");
        exit(2);
    });
    let claims: Vec<Value> = data.get("claims").and_then(Value::as_sequence).cloned().unwrap_or_default();
    if claims.is_empty() {
        eprintln!("claim-check-equiv: {claims_path} declares no claims");
        exit(2);
    }

    // (label, file contents or None for a fixed argv)
    let mut variants: Vec<(String, Option<String>, Vec<String>)> = vec![
        ("self-test".into(), None, vec!["--self-test".into()]),
        (claims_path.clone(), None, vec![claims_path.clone()]),
        ("missing path".into(), None, vec!["zz-missing-claims.yaml".into()]),
    ];
    let emit = |v: &Value| rivet_yaml::to_string(v).expect("emit variant");
    variants.push(("empty file".into(), Some(String::new()), vec![]));
    variants.push(("no claims".into(), Some(emit(&doc_of(vec![]))), vec![]));
    variants.push(("duplicate id".into(), Some(emit(&doc_of(vec![claims[0].clone(), claims[0].clone()]))), vec![]));
    let mut noid = claims[0].clone();
    if let Some(m) = noid.as_mapping_mut() {
        m.remove("id");
    }
    variants.push(("missing id".into(), Some(emit(&doc_of(vec![noid]))), vec![]));

    for c in &claims {
        let id = c.get("id").map(|v| format!("{v:?}")).unwrap_or_default();
        let mut push = |what: &str, m: Value| {
            variants.push((format!("{id} {what}"), Some(emit(&doc_of(vec![m]))), vec![]));
        };
        push("as is", c.clone());
        if let Some(t) = get_str(c, "text") {
            let mut m = c.clone();
            set(&mut m, "text", s(&format!("{t} zz-mutant")));
            push("text", m);
        }
        let mut m = c.clone();
        set(&mut m, "doc", s("zz-missing-doc.md"));
        push("doc", m);
        let mut m = c.clone();
        set(&mut m, "evidence", Value::Sequence(vec![]));
        push("no evidence", m);
        let evs: Vec<Value> = c.get("evidence").and_then(Value::as_sequence).cloned().unwrap_or_default();
        for (j, ev) in evs.iter().enumerate() {
            for (k, mev) in ev_mutants(ev).into_iter().enumerate() {
                let mut e2 = evs.clone();
                e2[j] = mev;
                let mut m = c.clone();
                set(&mut m, "evidence", Value::Sequence(e2));
                push(&format!("ev{j} mutant{k}"), m);
            }
        }
    }

    let mut identical = 0usize;
    let mut differ = 0usize;
    let mut ref_codes = std::collections::BTreeMap::<i32, usize>::new();
    for (i, (label, body, argv)) in variants.iter().enumerate() {
        let (args, file) = match body {
            None => (argv.clone(), None),
            Some(b) => {
                let f = dir.join(format!(".claim-equiv-{i}.yaml"));
                std::fs::write(&f, b).expect("write variant");
                (vec![f.to_string_lossy().into_owned()], Some(f))
            }
        };
        let (ro, rc) = run(&r, &args);
        let (no, nc) = run(&n, &args);
        if let Some(f) = file {
            let _ = std::fs::remove_file(f);
        }
        *ref_codes.entry(rc).or_default() += 1;
        if ro == no && rc == nc {
            identical += 1;
        } else {
            differ += 1;
            if differ <= 20 {
                println!("DIFFER: {label}: exit ref {rc} new {nc}");
                let (rs, ns) = (String::from_utf8_lossy(&ro), String::from_utf8_lossy(&no));
                for (a, b) in rs.lines().zip(ns.lines()).filter(|(a, b)| a != b).take(2) {
                    println!("  ref: {a}\n  new: {b}");
                }
                if rs.lines().count() != ns.lines().count() {
                    println!("  lines: ref {} new {}", rs.lines().count(), ns.lines().count());
                }
            }
        }
    }
    let total = identical + differ;
    let codes: Vec<String> = ref_codes.iter().map(|(c, k)| format!("exit {c}: {k}")).collect();
    println!("reference exit codes over the cases: {}", codes.join(", "));
    println!("{identical} of {total} cases identical (stdout and exit code)");
    let covers = [0, 1, 2].iter().all(|c| ref_codes.contains_key(c));
    if !covers {
        println!("claim-check-equiv: the reference did not exit 0, 1 and 2 across the cases; the mutants did not bite");
    }
    exit(if differ == 0 && total > 0 && covers { 0 } else { 1 });
}
