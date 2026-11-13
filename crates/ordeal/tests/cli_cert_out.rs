// rivet: verifies VER-092
//! `ordeal check FILE --cert-out PATH` (#316, TR-092), with the REAL binaries:
//! the bundle the CLI writes is an `ordeal-cert/v3` bundle that the real
//! `ordeal-recheck` accepts (exit 0), and a copy with one byte flipped in a
//! certified field is rejected (exit 1). The precedent for a `--cert-out`
//! flag is `ordeal verus --cert-out DIR`; the API's own bundle writer is
//! `TermCertificate::to_cert_v3` / `TermSatCertificate::to_cert_v3`, which
//! the `cert-bundle` leg below compares the CLI file against.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::OnceLock;
use std::sync::atomic::{AtomicUsize, Ordering};

const ORDEAL: &str = env!("CARGO_BIN_EXE_ordeal");

/// `u.smt2` of #316: unsat.
const UNSAT: &str = "(set-logic QF_BV)\n(declare-fun x () (_ BitVec 8))\n\
                     (assert (distinct (bvadd x #x01) (bvadd #x01 x)))\n(check-sat)\n";
/// Satisfiable, with a model.
const SAT: &str = "(set-logic QF_BV)\n(declare-fun x () (_ BitVec 8))\n\
                   (declare-fun y () (_ BitVec 8))\n\
                   (assert (= (bvadd x y) #x2a))\n(assert (bvult x #x10))\n(check-sat)\n";
/// A 136-bit literal: answered `unknown` (README, #313).
const UNKNOWN: &str = "(set-logic QF_BV)\n(declare-fun x () (_ BitVec 8))\n\
                       (assert (= ((_ extract 7 0) (_ bv5 136)) x))\n(check-sat)\n";

fn scratch(tag: &str) -> PathBuf {
    static N: AtomicUsize = AtomicUsize::new(0);
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!(
        "cert-out-{}-{}-{tag}",
        std::process::id(),
        N.fetch_add(1, Ordering::SeqCst)
    ));
    std::fs::create_dir_all(&d).unwrap();
    d
}

/// The real `ordeal-recheck`: the sibling of the `ordeal` binary in the
/// target directory (`cargo test --workspace` builds both). Built here when
/// a narrower `cargo test -p ordeal` left it out; the test then fails if it
/// still is not there — it never skips.
fn recheck_bin() -> &'static Path {
    static BIN: OnceLock<PathBuf> = OnceLock::new();
    BIN.get_or_init(|| {
        let ordeal = Path::new(ORDEAL);
        let profile_dir = ordeal.parent().expect("target profile dir");
        let exe = profile_dir.join(format!("ordeal-recheck{}", std::env::consts::EXE_SUFFIX));
        if !exe.exists() {
            let mut cmd = Command::new(env!("CARGO"));
            cmd.args(["build", "-p", "ordeal-recheck", "--manifest-path"])
                .arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("../../Cargo.toml"))
                .arg("--target-dir")
                .arg(profile_dir.parent().expect("target dir"));
            if profile_dir.file_name().and_then(|n| n.to_str()) == Some("release") {
                cmd.arg("--release");
            }
            let st = cmd.status().expect("run cargo build -p ordeal-recheck");
            assert!(st.success(), "cargo build -p ordeal-recheck failed");
        }
        assert!(
            exe.exists(),
            "ordeal-recheck not found at {}",
            exe.display()
        );
        exe
    })
}

fn ordeal(args: &[&str]) -> Output {
    Command::new(ORDEAL)
        .args(args)
        .output()
        .expect("run ordeal")
}

fn recheck(file: &Path) -> Output {
    Command::new(recheck_bin())
        .arg(file)
        .output()
        .expect("run ordeal-recheck")
}

fn out_text(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).into_owned()
}

fn err_text(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

fn write(dir: &Path, name: &str, text: &str) -> PathBuf {
    let p = dir.join(name);
    std::fs::write(&p, text).unwrap();
    p
}

/// `json` with the first byte after `marker` that is not `0` changed to
/// `0` (or a `0` changed to `1`): one byte flipped inside a certified field,
/// the document still valid JSON.
fn flip_after(json: &str, marker: &str) -> String {
    let at = json
        .find(marker)
        .unwrap_or_else(|| panic!("marker {marker:?} not in the bundle"))
        + marker.len();
    let mut bytes = json.as_bytes().to_vec();
    let i = (at..bytes.len())
        .find(|&i| bytes[i].is_ascii_alphanumeric())
        .expect("a byte to flip");
    bytes[i] = if bytes[i] == b'0' { b'1' } else { b'0' };
    String::from_utf8(bytes).unwrap()
}

/// Write the bundle of `script` and return (dir, bundle path, bundle text).
fn bundle_of(tag: &str, script: &str) -> (PathBuf, PathBuf, String) {
    let dir = scratch(tag);
    let q = write(&dir, "q.smt2", script);
    let bundle = dir.join("q.cert.json");
    let o = ordeal(&[
        "check",
        q.to_str().unwrap(),
        "--cert-out",
        bundle.to_str().unwrap(),
    ]);
    assert_eq!(
        o.status.code(),
        Some(0),
        "stdout {} stderr {}",
        out_text(&o),
        err_text(&o)
    );
    let text = std::fs::read_to_string(&bundle).expect("the bundle was written");
    (dir, bundle, text)
}

#[test]
fn unsat_bundle_round_trips_through_ordeal_recheck() {
    let (dir, bundle, text) = bundle_of("unsat", UNSAT);
    let v: serde_json::Value = serde_json::from_str(&text).expect("the bundle is JSON");
    assert_eq!(v["format"], "ordeal-cert/v3");
    assert_eq!(v["verdict"], "unsat");
    let ok = recheck(&bundle);
    assert_eq!(
        ok.status.code(),
        Some(0),
        "{}{}",
        out_text(&ok),
        err_text(&ok)
    );
    assert!(
        out_text(&ok).contains("accepted (ordeal-cert/v3, unsat)"),
        "{}",
        out_text(&ok)
    );
    // One byte flipped in each certified field: rejected, exit 1.
    for marker in [
        "\"problem\":{\"encoding\":\"dimacs-cnf\",\"num_clauses\":",
        "\"clauses\":[[",
        "\"body\":\"",
        "\"problem_sha256\":\"",
        "\"proof_sha256\":\"",
        "\"query\":{\"encoding\":\"",
        "\"term\":{\"encoding\":\"",
        "\"bits\":\"",
    ] {
        let bad = write(&dir, "bad.json", &flip_after(&text, marker));
        let r = recheck(&bad);
        assert_eq!(
            r.status.code(),
            Some(1),
            "flip after {marker:?} must be rejected: {}{}",
            out_text(&r),
            err_text(&r)
        );
        assert!(out_text(&r).contains("rejected"), "{}", out_text(&r));
    }
}

#[test]
fn sat_bundle_round_trips_through_ordeal_recheck() {
    let (dir, bundle, text) = bundle_of("sat", SAT);
    let v: serde_json::Value = serde_json::from_str(&text).expect("the bundle is JSON");
    assert_eq!(v["format"], "ordeal-cert/v3");
    assert_eq!(v["verdict"], "sat");
    let ok = recheck(&bundle);
    assert_eq!(
        ok.status.code(),
        Some(0),
        "{}{}",
        out_text(&ok),
        err_text(&ok)
    );
    assert!(
        out_text(&ok).contains("accepted (ordeal-cert/v3, sat)"),
        "{}",
        out_text(&ok)
    );
    for marker in [
        "\"clauses\":[[",
        "\"assignment\":\"",
        "\"assignment_sha256\":\"",
        "\"problem_sha256\":\"",
        "\"inputs\":{\"encoding\":\"",
        "\"term\":{\"encoding\":\"",
    ] {
        let bad = write(&dir, "bad.json", &flip_after(&text, marker));
        let r = recheck(&bad);
        assert_eq!(
            r.status.code(),
            Some(1),
            "flip after {marker:?} must be rejected: {}{}",
            out_text(&r),
            err_text(&r)
        );
    }
}

#[test]
fn the_json_report_is_not_a_bundle_and_cert_out_is() {
    let dir = scratch("report");
    let q = write(&dir, "q.smt2", UNSAT);
    let bundle = dir.join("b.json");
    let o = ordeal(&[
        "check",
        q.to_str().unwrap(),
        "--format",
        "json",
        "--cert-out",
        bundle.to_str().unwrap(),
    ]);
    assert_eq!(o.status.code(), Some(0));
    // stdout is the verdict report, unchanged in shape ...
    let report = write(&dir, "report.json", &out_text(&o));
    let rv: serde_json::Value = serde_json::from_str(&out_text(&o)).expect("report is JSON");
    assert_eq!(rv["verdict"], "unsat");
    assert!(rv.get("format").is_none());
    // ... and ordeal-recheck rejects it: it is not a bundle (#316) ...
    let r = recheck(&report);
    assert_eq!(r.status.code(), Some(1));
    assert!(
        out_text(&r).contains("missing field `format`"),
        "{}",
        out_text(&r)
    );
    // ... while the file --cert-out wrote is accepted.
    assert_eq!(recheck(&bundle).status.code(), Some(0));
    // --with-term and --with-query print as they do without --cert-out.
    for flag in ["--with-term", "--with-query"] {
        let b2 = dir.join("b2.json");
        let o = ordeal(&[
            "check",
            q.to_str().unwrap(),
            "--format",
            "json",
            flag,
            "--cert-out",
            b2.to_str().unwrap(),
        ]);
        assert_eq!(o.status.code(), Some(0), "{flag}");
        let plain = ordeal(&["check", q.to_str().unwrap(), "--format", "json", flag]);
        assert_eq!(out_text(&o), out_text(&plain), "{flag}");
        assert_eq!(recheck(&b2).status.code(), Some(0), "{flag}");
    }
}

#[test]
fn stdout_is_the_same_verdict_with_and_without_cert_out() {
    let dir = scratch("same");
    for script in [UNSAT, SAT] {
        let q = write(&dir, "q.smt2", script);
        let b = dir.join("b.json");
        let with = ordeal(&[
            "check",
            q.to_str().unwrap(),
            "--cert-out",
            b.to_str().unwrap(),
        ]);
        let without = ordeal(&["check", q.to_str().unwrap()]);
        // The verdict line (the first) and the exit code agree; the model of
        // a `sat` may legitimately differ between the two solve paths.
        assert_eq!(
            out_text(&with).lines().next(),
            out_text(&without).lines().next()
        );
        assert_eq!(with.status.code(), without.status.code());
    }
}

#[test]
fn unknown_writes_no_bundle_and_exits_1() {
    let dir = scratch("unknown");
    let q = write(&dir, "q.smt2", UNKNOWN);
    let b = dir.join("b.json");
    let o = ordeal(&[
        "check",
        q.to_str().unwrap(),
        "--cert-out",
        b.to_str().unwrap(),
    ]);
    assert_eq!(out_text(&o).trim(), "unknown");
    assert_eq!(o.status.code(), Some(1), "{}", err_text(&o));
    assert!(
        err_text(&o).contains("no certificate written"),
        "{}",
        err_text(&o)
    );
    assert!(!b.exists(), "an undecided verdict writes no file");
    // Without --cert-out the same script is `unknown`, exit 0.
    let plain = ordeal(&["check", q.to_str().unwrap()]);
    assert_eq!(out_text(&plain).trim(), "unknown");
    assert_eq!(plain.status.code(), Some(0));
}

#[test]
fn usage_and_input_errors_exit_2_and_write_nothing() {
    let dir = scratch("usage");
    let q = write(&dir, "q.smt2", UNSAT);
    // --cert-out without a path
    let o = ordeal(&["check", q.to_str().unwrap(), "--cert-out"]);
    assert_eq!(o.status.code(), Some(2));
    assert!(
        err_text(&o).contains("--cert-out needs"),
        "{}",
        err_text(&o)
    );
    // a script that does not parse
    let bad = write(&dir, "bad.smt2", "(assert (= x");
    let b = dir.join("b.json");
    let o = ordeal(&[
        "check",
        bad.to_str().unwrap(),
        "--cert-out",
        b.to_str().unwrap(),
    ]);
    assert_eq!(o.status.code(), Some(2));
    assert!(!b.exists());
    // an unwritable destination
    let nowhere = dir.join("no-such-dir").join("b.json");
    let o = ordeal(&[
        "check",
        q.to_str().unwrap(),
        "--cert-out",
        nowhere.to_str().unwrap(),
    ]);
    assert_eq!(o.status.code(), Some(2));
    assert!(err_text(&o).contains("cannot write"), "{}", err_text(&o));
}

#[test]
fn help_lists_cert_out_and_says_the_report_is_not_a_bundle() {
    for flag in ["--help", "-h"] {
        let o = ordeal(&[flag]);
        assert_eq!(o.status.code(), Some(0));
        let h = out_text(&o);
        assert!(h.contains("--cert-out PATH"), "{h}");
        assert!(h.contains("NOT a bundle"), "{h}");
        assert!(h.contains("ordeal-recheck"), "{h}");
    }
}

/// The CLI file is the bundle the API writes: the same JSON as
/// `to_cert_v3`, and it parses with the API's hash-verifying reader.
#[cfg(feature = "cert-bundle")]
#[test]
fn cli_bundle_equals_the_api_bundle() {
    use ordeal::cert_bundle::Attests;
    use ordeal::query::{TermCertificate, TermCheckResult, TermSatCertificate};

    let attests = |claim: &str| Attests {
        kind: "qf_bv_validity".into(),
        claim: claim.into(),
        standards: vec![],
    };
    let (_, _, text) = bundle_of("api-unsat", UNSAT);
    let cli: serde_json::Value = serde_json::from_str(&text).unwrap();
    let (res, _) = ordeal::smtlib::solve_str_with_term(UNSAT).unwrap();
    let Some(TermCheckResult::Unsat(cert)) = res else {
        panic!("expected a term-carrying unsat");
    };
    let api: serde_json::Value = serde_json::from_str(
        &cert.to_cert_v3(&attests("the asserted QF_BV script is unsatisfiable")),
    )
    .unwrap();
    assert_eq!(cli, api, "the CLI unsat bundle differs from to_cert_v3");
    TermCertificate::from_cert_v3(&text)
        .expect("the API reader accepts the CLI bundle")
        .recheck()
        .expect("and re-checks it");

    let (_, _, text) = bundle_of("api-sat", SAT);
    let cli: serde_json::Value = serde_json::from_str(&text).unwrap();
    let (res, _) = ordeal::smtlib::solve_str_with_term(SAT).unwrap();
    let Some(TermCheckResult::Sat(cert)) = res else {
        panic!("expected a term-carrying sat");
    };
    let api: serde_json::Value = serde_json::from_str(&cert.to_cert_v3(&attests(
        "the asserted QF_BV script is satisfiable (model self-checked)",
    )))
    .unwrap();
    assert_eq!(cli, api, "the CLI sat bundle differs from to_cert_v3");
    TermSatCertificate::from_cert_v3(&text)
        .expect("the API reader accepts the CLI sat bundle")
        .recheck()
        .expect("and re-checks it");
}
