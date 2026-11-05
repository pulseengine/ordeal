// rivet: verifies VER-075
//! TR-075 / issue #277: the `ordeal-recheck` binary, end to end.
//!
//! The bundles come from the REAL solver (`tests/corpus/mod.rs`, through
//! `ordeal`'s public API — a dev-dependency, never in the binary's
//! closure). Every `ordeal-cert/v1`..`v4` UNSAT and SAT bundle must be
//! ACCEPTED (exit 0); each mutation — a flipped clause literal, a dropped
//! LRAT line, a swapped term node — must be REJECTED (exit 1). The
//! mutations are re-emitted through the `ordeal-cert` emitters, so every
//! content hash is recomputed and the rejection has to come from the
//! trusted recheck, not from the integrity check; a separate control
//! shows an un-rehashed edit is caught by the hash.

mod corpus;

use ordeal_cert::cert_bundle::{Attests, bundle_header};
use ordeal_cert::{
    Certificate, QueryCertificate, QuerySatCertificate, SatCertificate, SliverCertificate,
    SliverSatCertificate, TermCertificate, TermSatCertificate,
};
use ordeal_lrat::ExtNode;
use ordeal_lrat::blast_kernel::DagNode;
use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

const BIN: &str = env!("CARGO_BIN_EXE_ordeal-recheck");

fn scratch(tag: &str) -> PathBuf {
    static N: AtomicUsize = AtomicUsize::new(0);
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!(
        "recheck-{}-{}-{tag}",
        std::process::id(),
        N.fetch_add(1, Ordering::SeqCst)
    ));
    std::fs::create_dir_all(&d).unwrap();
    d
}

fn write(dir: &std::path::Path, name: &str, json: &str) -> PathBuf {
    let p = dir.join(name);
    std::fs::write(&p, json).unwrap();
    p
}

fn run(args: &[&str]) -> Output {
    Command::new(BIN)
        .args(args)
        .output()
        .expect("run ordeal-recheck")
}

fn run_json(files: &[PathBuf]) -> (i32, serde_json::Value) {
    let mut args = vec!["--format".to_string(), "json".to_string()];
    args.extend(files.iter().map(|p| p.display().to_string()));
    let out = Command::new(BIN).args(&args).output().unwrap();
    let v: serde_json::Value = serde_json::from_slice(&out.stdout)
        .unwrap_or_else(|e| panic!("json output: {e}: {}", String::from_utf8_lossy(&out.stdout)));
    (out.status.code().unwrap(), v)
}

fn attests() -> Attests {
    Attests {
        kind: "translation_validation".into(),
        claim: "mutated".into(),
        standards: vec![],
    }
}

/// Flip the sign of one literal of the CNF. For a SAT witness the flipped
/// literal is the ONLY true literal of its clause under the assignment, so
/// the clause becomes false; for UNSAT, the first unit clause (a root the
/// refutation must use).
fn flip_unsat(cnf: &mut [Vec<i32>]) {
    let c = cnf
        .iter_mut()
        .find(|c| c.len() == 1)
        .expect("a unit clause to flip");
    c[0] = -c[0];
}

fn flip_sat(cnf: &mut [Vec<i32>], assignment: &[bool]) {
    let truth = |l: i32| assignment[(l.unsigned_abs() - 1) as usize] == (l > 0);
    let c = cnf
        .iter_mut()
        .find(|c| c.iter().filter(|&&l| truth(l)).count() == 1)
        .expect("a clause with a single true literal");
    let i = c.iter().position(|&l| truth(l)).unwrap();
    c[i] = -c[i];
}

/// Drop the LRAT line that derives the empty clause (`id 0 hints… 0`).
fn drop_lrat_line(lrat: &mut Vec<u8>) {
    let text = String::from_utf8(lrat.clone()).unwrap();
    let lines: Vec<&str> = text.lines().collect();
    let at = lines
        .iter()
        .position(|l| {
            let t: Vec<&str> = l.split_whitespace().collect();
            t.len() > 1 && t[1] == "0"
        })
        .unwrap_or(lines.len() - 1);
    let kept: Vec<&str> = lines
        .iter()
        .enumerate()
        .filter(|(i, _)| *i != at)
        .map(|(_, l)| *l)
        .collect();
    let mut s = kept.join("\n");
    if text.ends_with('\n') {
        s.push('\n');
    }
    *lrat = s.into_bytes();
}

/// Swap the operator of the first node that has a semantically different
/// twin (`add`↔`sub`, `eq`↔`ne`, `ult`↔`uge`, `ugt`↔`ule`, `mul`→`add`).
fn swap_node(nodes: &mut [DagNode]) {
    use DagNode as N;
    for n in nodes.iter_mut() {
        let s = match *n {
            N::Add(a, b) => N::Sub(a, b),
            N::Sub(a, b) => N::Add(a, b),
            N::Eq(a, b) => N::Ne(a, b),
            N::Ne(a, b) => N::Eq(a, b),
            N::Ult(a, b) => N::Uge(a, b),
            N::Ugt(a, b) => N::Ule(a, b),
            N::Mul(a, b) => N::Add(a, b),
            _ => continue,
        };
        *n = s;
        return;
    }
    panic!("no swappable node");
}

/// Every mutation of a bundle, each re-emitted with fresh hashes.
fn mutations(json: &str) -> Vec<(&'static str, String)> {
    let a = attests();
    let (format, verdict) = bundle_header(json).unwrap();
    let mut out = Vec::new();
    match (format.as_str(), verdict.as_str()) {
        ("ordeal-cert/v1", "unsat") => {
            let c = Certificate::from_cert_v1(json).unwrap().certificate;
            let mut m = c.clone();
            flip_unsat(&mut m.cnf);
            out.push(("flipped clause literal", m.to_cert_v1(&a)));
            let mut m = c;
            drop_lrat_line(&mut m.lrat);
            out.push(("dropped LRAT line", m.to_cert_v1(&a)));
        }
        ("ordeal-cert/v1", "sat") => {
            let mut m = SatCertificate::from_cert_v1(json).unwrap();
            flip_sat(&mut m.cnf, &m.assignment.clone());
            out.push(("flipped clause literal", m.to_cert_v1(&a)));
        }
        ("ordeal-cert/v2", "unsat") => {
            let c = QueryCertificate::from_cert_v2(json).unwrap().certificate;
            let mut m = c.clone();
            flip_unsat(&mut m.certificate.cnf);
            out.push(("flipped clause literal", m.to_cert_v2(&a)));
            let mut m = c.clone();
            drop_lrat_line(&mut m.certificate.lrat);
            out.push(("dropped LRAT line", m.to_cert_v2(&a)));
            let mut m = c;
            swap_node(&mut m.query.nodes);
            out.push(("swapped query node", m.to_cert_v2(&a)));
        }
        ("ordeal-cert/v2", "sat") => {
            let c = QuerySatCertificate::from_cert_v2(json).unwrap().certificate;
            let mut m = c.clone();
            let asg = m.witness.assignment.clone();
            flip_sat(&mut m.witness.cnf, &asg);
            out.push(("flipped clause literal", m.to_cert_v2(&a)));
            let mut m = c;
            swap_node(&mut m.query.nodes);
            out.push(("swapped query node", m.to_cert_v2(&a)));
        }
        ("ordeal-cert/v3", "unsat") => {
            let c = TermCertificate::from_cert_v3(json).unwrap().certificate;
            let mut m = c.clone();
            flip_unsat(&mut m.query.certificate.cnf);
            out.push(("flipped clause literal", m.to_cert_v3(&a)));
            let mut m = c.clone();
            drop_lrat_line(&mut m.query.certificate.lrat);
            out.push(("dropped LRAT line", m.to_cert_v3(&a)));
            let mut m = c;
            swap_node(&mut m.term.nodes);
            out.push(("swapped term node", m.to_cert_v3(&a)));
        }
        ("ordeal-cert/v3", "sat") => {
            let c = TermSatCertificate::from_cert_v3(json).unwrap().certificate;
            let mut m = c.clone();
            let asg = m.query.witness.assignment.clone();
            flip_sat(&mut m.query.witness.cnf, &asg);
            out.push(("flipped clause literal", m.to_cert_v3(&a)));
            let mut m = c;
            swap_node(&mut m.term.nodes);
            out.push(("swapped term node", m.to_cert_v3(&a)));
        }
        ("ordeal-cert/v4", "unsat") => {
            let c = SliverCertificate::from_cert_v4(json).unwrap().certificate;
            let mut m = c.clone();
            flip_unsat(&mut m.term.query.certificate.cnf);
            out.push(("flipped clause literal", m.to_cert_v4(&a)));
            let mut m = c.clone();
            drop_lrat_line(&mut m.term.query.certificate.lrat);
            out.push(("dropped LRAT line", m.to_cert_v4(&a)));
            let mut m = c.clone();
            swap_node(&mut m.term.term.nodes);
            out.push(("swapped term node", m.to_cert_v4(&a)));
            // The extended query as asked: a core node inside the ext block.
            let mut m = c;
            let mut core: Vec<DagNode> = m
                .sliver
                .ext
                .nodes
                .iter()
                .filter_map(|n| match n {
                    ExtNode::Core(d) => Some(*d),
                    _ => None,
                })
                .collect();
            swap_node(&mut core);
            let mut it = core.into_iter();
            for n in m.sliver.ext.nodes.iter_mut() {
                if let ExtNode::Core(d) = n {
                    *d = it.next().unwrap();
                }
            }
            out.push(("swapped ext node", m.to_cert_v4(&a)));
        }
        ("ordeal-cert/v4", "sat") => {
            let c = SliverSatCertificate::from_cert_v4(json)
                .unwrap()
                .certificate;
            let mut m = c.clone();
            let asg = m.term.query.witness.assignment.clone();
            flip_sat(&mut m.term.query.witness.cnf, &asg);
            out.push(("flipped clause literal", m.to_cert_v4(&a)));
            let mut m = c;
            swap_node(&mut m.term.term.nodes);
            out.push(("swapped term node", m.to_cert_v4(&a)));
        }
        other => panic!("unexpected bundle kind {other:?}"),
    }
    out
}

/// Every v1..v4 UNSAT and SAT bundle the solver emits on the corpus is
/// accepted, one at a time and all together (exit 0).
#[test]
fn every_solver_bundle_is_accepted() {
    let dir = scratch("accept");
    let corpus = corpus::corpus();
    let mut kinds = std::collections::BTreeSet::new();
    let mut files = Vec::new();
    for e in corpus.iter().filter(|e| e.recheckable) {
        let p = write(&dir, &e.name, &e.json);
        let out = run(&[p.to_str().unwrap()]);
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert_eq!(
            out.status.code(),
            Some(0),
            "{}: {stdout}{}",
            e.name,
            String::from_utf8_lossy(&out.stderr)
        );
        assert!(stdout.contains(": accepted ("), "{}: {stdout}", e.name);
        kinds.insert(bundle_header(&e.json).unwrap());
        files.push(p);
    }
    // All eight (format, verdict) kinds are covered.
    assert_eq!(kinds.len(), 8, "{kinds:?}");
    let (code, v) = run_json(&files);
    assert_eq!(code, 0, "{v}");
    assert_eq!(v["tool"], "ordeal-recheck");
    assert_eq!(v["version"], env!("CARGO_PKG_VERSION"));
    assert_eq!(v["accepted"], files.len());
    assert_eq!(v["rejected"], 0);
    for r in v["results"].as_array().unwrap() {
        assert_eq!(r["status"], "accepted", "{r}");
    }
}

/// Each mutation — flipped clause literal, dropped LRAT line, swapped term
/// node — of each bundle is rejected (exit 1) BY THE RECHECK: the hashes
/// were recomputed, so the integrity check passes and the trusted check
/// is what refuses.
#[test]
fn every_mutated_bundle_is_rejected_by_the_recheck() {
    let dir = scratch("mutate");
    let mut n = 0;
    let mut labels = std::collections::BTreeSet::new();
    for e in corpus::corpus().iter().filter(|e| e.recheckable) {
        for (label, json) in mutations(&e.json) {
            let name = format!("{}-{}.json", e.name, label.replace(' ', "-"));
            let p = write(&dir, &name, &json);
            let (code, v) = run_json(std::slice::from_ref(&p));
            assert_eq!(code, 1, "{name} was not rejected: {v}");
            let r = &v["results"][0];
            assert_eq!(r["status"], "rejected", "{name}: {r}");
            let reason = r["reason"].as_str().unwrap();
            assert!(
                reason.starts_with("recheck failed:"),
                "{name}: rejected before the recheck ran ({reason}) — the mutation should be hash-consistent"
            );
            // The text format says the same, on stdout, with the reason.
            let out = run(&[p.to_str().unwrap()]);
            assert_eq!(out.status.code(), Some(1));
            assert!(String::from_utf8_lossy(&out.stdout).contains(": rejected ("));
            labels.insert(label);
            n += 1;
        }
    }
    for l in [
        "flipped clause literal",
        "dropped LRAT line",
        "swapped query node",
        "swapped term node",
        "swapped ext node",
    ] {
        assert!(labels.contains(l), "mutation '{l}' never applied");
    }
    // 4 widths x (v1: 2, v2: 3, v3: 3) UNSAT + 3 widths x (v1: 1, v2: 2,
    // v3: 2) SAT + v4 (UNSAT 4, SAT 2): every mutant ran.
    assert_eq!(n, 53, "mutant count");
}

/// One bad bundle among good ones makes the whole run exit 1, and the
/// good ones are still reported accepted.
#[test]
fn one_rejected_bundle_fails_the_run() {
    let dir = scratch("mixed");
    let corpus = corpus::corpus();
    let good = corpus
        .iter()
        .find(|e| e.name == "v3-unsat-w5.json")
        .unwrap();
    let bad = mutations(&good.json).remove(0).1;
    let files = vec![
        write(&dir, "good.json", &good.json),
        write(&dir, "bad.json", &bad),
    ];
    let (code, v) = run_json(&files);
    assert_eq!(code, 1);
    assert_eq!(v["accepted"], 1);
    assert_eq!(v["rejected"], 1);
    assert_eq!(v["results"][0]["status"], "accepted");
    assert_eq!(v["results"][1]["status"], "rejected");
}

/// Integrity control: a literal flipped WITHOUT recomputing the hash is
/// refused at decoding (content hash mismatch); malformed input, a
/// missing file, an unknown format and a model-only (witness-less) SAT
/// bundle are rejected too — never accepted.
#[test]
fn tampered_malformed_and_witnessless_bundles_are_rejected() {
    let dir = scratch("tamper");
    let corpus = corpus::corpus();
    let v1 = corpus
        .iter()
        .find(|e| e.name == "v1-unsat-w8.json")
        .unwrap();
    let mut j: serde_json::Value = serde_json::from_str(&v1.json).unwrap();
    let lit = j["problem"]["clauses"][0][0].as_i64().unwrap();
    j["problem"]["clauses"][0][0] = serde_json::json!(-lit);
    let tampered = write(&dir, "tampered.json", &j.to_string());
    let (code, v) = run_json(std::slice::from_ref(&tampered));
    assert_eq!(code, 1);
    assert!(
        v["results"][0]["reason"]
            .as_str()
            .unwrap()
            .contains("content hash mismatch"),
        "{v}"
    );

    let mut other = j.clone();
    other["format"] = serde_json::json!("ordeal-cert/v9");
    let cases = [
        write(&dir, "garbage.json", "this is not json"),
        write(&dir, "v9.json", &other.to_string()),
        dir.join("does-not-exist.json"),
    ];
    for p in &cases {
        let (code, v) = run_json(std::slice::from_ref(p));
        assert_eq!(code, 1, "{}: {v}", p.display());
        assert_eq!(v["results"][0]["status"], "rejected");
    }
    for e in corpus.iter().filter(|e| !e.recheckable) {
        let p = write(&dir, &e.name, &e.json);
        let (code, v) = run_json(std::slice::from_ref(&p));
        assert_eq!(code, 1, "{}: {v}", e.name);
    }
}

/// The PulseEngine CLI conventions: `--version` / `-V` print
/// `ordeal-recheck <semver>` and exit 0; `--help` exits 0; an unknown
/// flag or a missing bundle prints the usage on stderr and exits 2.
#[test]
fn cli_conventions() {
    let want = format!("ordeal-recheck {}\n", env!("CARGO_PKG_VERSION"));
    for flag in ["--version", "-V"] {
        let out = run(&[flag]);
        assert_eq!(out.status.code(), Some(0));
        assert_eq!(String::from_utf8_lossy(&out.stdout), want);
    }
    let out = run(&["--help"]);
    assert_eq!(out.status.code(), Some(0));
    assert!(String::from_utf8_lossy(&out.stdout).contains("Usage: ordeal-recheck"));
    for args in [
        &["--bogus"][..],
        &[][..],
        &["--format", "yaml", "x.json"][..],
        &["--format"][..],
    ] {
        let out = run(args);
        assert_eq!(out.status.code(), Some(2), "{args:?}");
        assert!(
            String::from_utf8_lossy(&out.stderr).contains("Usage: ordeal-recheck"),
            "{args:?}"
        );
        assert!(out.stdout.is_empty(), "{args:?}");
    }
}

/// The committed fixtures (`tests/fixtures/`, real solver output) that the
/// release workflow smokes the shipped native binaries and the wasm
/// component with are accepted.
#[test]
fn committed_release_smoke_fixtures_are_accepted() {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
    let files = [dir.join("v3-unsat-w3.json"), dir.join("v3-sat-w5.json")];
    let (code, v) = run_json(&files);
    assert_eq!(code, 0, "{v}");
    assert_eq!(v["accepted"], 2);
}
