// rivet: verifies VER-097
//! `ordeal check FILE --cert-out PATH --echo` and `ordeal verus … --cert-out
//! DIR --echo` (#281 E2, TR-097), with the REAL binaries: the bundle is
//! `ordeal-cert/v5` — the v3 bundle plus the certified echo of its term —
//! and the real `ordeal-recheck` accepts it (exit 0), re-deriving the echo
//! with the trusted printer; a one-byte change in the echo is rejected by
//! its hash, and with the hash recomputed by the re-derivation. A quoted
//! symbol is echoed quoted (`|a b|`): the reader stores its content.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::OnceLock;
use std::sync::atomic::{AtomicUsize, Ordering};

const ORDEAL: &str = env!("CARGO_BIN_EXE_ordeal");

/// Unsat, with a quoted symbol that is not a simple symbol and the two
/// spellings of one simple symbol.
const UNSAT: &str = "(set-logic QF_BV)\n(declare-fun |a b| () (_ BitVec 8))\n\
                     (declare-fun x () (_ BitVec 8))\n\
                     (assert (= |x| |a b|))\n\
                     (assert (distinct (bvadd x #x01) (bvadd #x01 |a b|)))\n(check-sat)\n";
/// Satisfiable, with a model.
const SAT: &str = "(set-logic QF_BV)\n(declare-fun |0v| () (_ BitVec 8))\n\
                   (declare-fun y () (_ BitVec 8))\n\
                   (assert (= (bvadd |0v| y) #x2a))\n(assert (bvult |0v| #x10))\n(check-sat)\n";
/// Unsat, with the empty symbol `||`, which the printer refuses: the
/// bundle is then v3, without an echo.
const EMPTY_NAME: &str = "(set-logic QF_BV)\n(declare-fun || () (_ BitVec 8))\n\
                          (assert (distinct (bvadd || #x01) (bvadd #x01 ||)))\n(check-sat)\n";

fn scratch(tag: &str) -> PathBuf {
    static N: AtomicUsize = AtomicUsize::new(0);
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!(
        "cli-echo-{}-{}-{tag}",
        std::process::id(),
        N.fetch_add(1, Ordering::SeqCst)
    ));
    std::fs::create_dir_all(&d).unwrap();
    d
}

/// The real `ordeal-recheck` (as in `cli_cert_out.rs`): built when a
/// narrower `cargo test -p ordeal` left it out; never skipped.
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

/// Write the `--echo` bundle of `script`; return (dir, path, text).
fn echo_bundle_of(tag: &str, script: &str) -> (PathBuf, PathBuf, String) {
    let dir = scratch(tag);
    let q = write(&dir, "q.smt2", script);
    let bundle = dir.join("q.cert.json");
    let o = ordeal(&[
        "check",
        q.to_str().unwrap(),
        "--cert-out",
        bundle.to_str().unwrap(),
        "--echo",
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

fn accepted(bundle: &Path, kind: &str) {
    let ok = recheck(bundle);
    assert_eq!(
        ok.status.code(),
        Some(0),
        "{}{}",
        out_text(&ok),
        err_text(&ok)
    );
    assert!(
        out_text(&ok).contains(&format!("accepted ({kind})")),
        "{}",
        out_text(&ok)
    );
}

fn rejected(dir: &Path, json: &str, what: &str) -> String {
    let bad = write(dir, "bad.json", json);
    let r = recheck(&bad);
    assert_eq!(
        r.status.code(),
        Some(1),
        "{what} must be rejected: {}{}",
        out_text(&r),
        err_text(&r)
    );
    out_text(&r)
}

#[test]
fn echo_bundles_are_v5_and_round_trip_through_ordeal_recheck() {
    for (tag, script, verdict) in [("unsat", UNSAT, "unsat"), ("sat", SAT, "sat")] {
        let (dir, bundle, text) = echo_bundle_of(tag, script);
        let v: serde_json::Value = serde_json::from_str(&text).expect("the bundle is JSON");
        assert_eq!(v["format"], "ordeal-cert/v5");
        assert_eq!(v["verdict"], verdict);
        assert_eq!(v["recheck"]["min_version"], "0.38.0");
        assert!(
            v["recheck"]["cmd"]
                .as_str()
                .unwrap()
                .ends_with("== Ok(echo.text)"),
            "{}",
            v["recheck"]["cmd"]
        );
        assert_eq!(v["echo"]["encoding"], "ordeal-echo/v1");
        assert_eq!(v["echo"]["logic"], "QF_BV");
        let echo = v["echo"]["text"].as_str().unwrap().to_string();
        assert!(echo.starts_with("(set-logic QF_BV)\n"), "{echo}");
        // The reader stored the content; the printer quoted it again.
        if verdict == "unsat" {
            assert!(
                echo.contains("(declare-const |a b| (_ BitVec 8))"),
                "{echo}"
            );
            assert!(echo.contains("(declare-const |x| (_ BitVec 8))"), "{echo}");
            assert!(!echo.contains("||a b||"), "{echo}");
        } else {
            assert!(echo.contains("(declare-const |0v| (_ BitVec 8))"), "{echo}");
        }
        accepted(&bundle, &format!("ordeal-cert/v5, {verdict}"));

        // One byte of the echo changed: refused by its hash ...
        let at = echo.find("(assert").unwrap() + 1;
        let mut tampered = echo.clone();
        tampered.replace_range(at..=at, "A");
        let mut j = v.clone();
        j["echo"]["text"] = serde_json::json!(tampered);
        let out = rejected(&dir, &j.to_string(), "an echo byte changed");
        assert!(out.contains("content hash mismatch"), "{out}");
        // ... and with the hash recomputed, by the re-derivation.
        j["echo"]["sha256"] = serde_json::json!(sha256_hex(tampered.as_bytes()));
        let out = rejected(&dir, &j.to_string(), "an echo byte changed, rehashed");
        assert!(
            out.contains("the echo is not the trusted printer's output"),
            "{out}"
        );
        // A v5 bundle relabelled v3 is still accepted by the v3 reader,
        // which ignores the echo: the echo is read only under v5, where it
        // is re-derived (the reason v5 is a new format).
        let mut v3 = v.clone();
        v3["format"] = serde_json::json!("ordeal-cert/v3");
        let p = write(&dir, "as-v3.json", &v3.to_string());
        assert_eq!(recheck(&p).status.code(), Some(0));
        // A wrong logic is refused.
        let mut j = v.clone();
        j["echo"]["logic"] = serde_json::json!("QF_ABV");
        let out = rejected(&dir, &j.to_string(), "a wrong echo logic");
        assert!(out.contains("logic"), "{out}");
    }
}

#[test]
fn without_echo_the_bundle_is_v3_and_a_refused_echo_falls_back_to_v3() {
    let dir = scratch("v3");
    let q = write(&dir, "q.smt2", UNSAT);
    let b = dir.join("b.json");
    let o = ordeal(&[
        "check",
        q.to_str().unwrap(),
        "--cert-out",
        b.to_str().unwrap(),
    ]);
    assert_eq!(o.status.code(), Some(0));
    let v: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(&b).unwrap()).unwrap();
    assert_eq!(v["format"], "ordeal-cert/v3");
    assert!(v.get("echo").is_none());
    accepted(&b, "ordeal-cert/v3, unsat");

    // `||` is a symbol (the reader reads it), but the printer refuses an
    // empty name: the verdict stands, the bundle is v3, stderr says why.
    let q = write(&dir, "e.smt2", EMPTY_NAME);
    let b = dir.join("e.json");
    let o = ordeal(&[
        "check",
        q.to_str().unwrap(),
        "--cert-out",
        b.to_str().unwrap(),
        "--echo",
    ]);
    assert_eq!(o.status.code(), Some(0), "{}", err_text(&o));
    assert_eq!(out_text(&o).lines().next(), Some("unsat"));
    assert!(err_text(&o).contains("no echo"), "{}", err_text(&o));
    let v: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(&b).unwrap()).unwrap();
    assert_eq!(v["format"], "ordeal-cert/v3");
    accepted(&b, "ordeal-cert/v3, unsat");
}

#[test]
fn echo_without_cert_out_is_a_usage_error() {
    let dir = scratch("usage");
    let q = write(&dir, "q.smt2", UNSAT);
    let o = ordeal(&["check", q.to_str().unwrap(), "--echo"]);
    assert_eq!(o.status.code(), Some(2));
    assert!(
        err_text(&o).contains("--echo requires --cert-out"),
        "{}",
        err_text(&o)
    );
    let fixtures = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
    let o = ordeal(&[
        "verus",
        fixtures
            .join("verus_gale_cpu_mask_raw.smt2")
            .to_str()
            .unwrap(),
        "--echo",
    ]);
    assert_eq!(o.status.code(), Some(2));
    assert!(
        err_text(&o).contains("--echo requires --cert-out"),
        "{}",
        err_text(&o)
    );
}

/// `ordeal verus --cert-out DIR --echo`: beside each `<name>.lrat`, a
/// `<name>.cert.json` that `ordeal-recheck` accepts; its echo is the
/// obligation as ordeal read it. Without `--echo`, only the `.lrat`.
#[test]
fn verus_echo_writes_a_rechecked_bundle_beside_the_lrat() {
    let fixtures = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
    let log = fixtures.join("verus_gale_cpu_mask_raw.smt2");
    let dir = scratch("verus");
    let o = ordeal(&[
        "verus",
        log.to_str().unwrap(),
        "--cert-out",
        dir.to_str().unwrap(),
        "--echo",
    ]);
    assert_eq!(o.status.code(), Some(0), "{}{}", out_text(&o), err_text(&o));
    let lrat = dir.join("verus_gale_cpu_mask_raw.lrat");
    let bundle = dir.join("verus_gale_cpu_mask_raw.cert.json");
    assert!(lrat.exists() && bundle.exists());
    let text = std::fs::read_to_string(&bundle).unwrap();
    let v: serde_json::Value = serde_json::from_str(&text).unwrap();
    assert_eq!(v["format"], "ordeal-cert/v5");
    assert_eq!(v["verdict"], "unsat");
    // The `.lrat` is the bundle's proof.
    assert_eq!(
        v["proof"]["body"].as_str().unwrap().as_bytes(),
        std::fs::read(&lrat).unwrap()
    );
    let echo = v["echo"]["text"].as_str().unwrap();
    assert!(echo.contains("|%%location_label%%"), "{echo}");
    accepted(&bundle, "ordeal-cert/v5, unsat");

    let plain = scratch("verus-plain");
    let o = ordeal(&[
        "verus",
        log.to_str().unwrap(),
        "--cert-out",
        plain.to_str().unwrap(),
    ]);
    assert_eq!(o.status.code(), Some(0));
    assert!(plain.join("verus_gale_cpu_mask_raw.lrat").exists());
    assert!(!plain.join("verus_gale_cpu_mask_raw.cert.json").exists());
}

/// The CLI's hand-written v5 file is the bundle the API writes
/// (`EchoCertificate::to_cert_v5`), and the API reader accepts it.
#[cfg(feature = "cert-bundle")]
#[test]
fn cli_echo_bundle_equals_the_api_bundle() {
    use ordeal::cert_bundle::Attests;
    use ordeal::query::TermCheckResult;
    use ordeal::{EchoCertificate, EchoSubject};

    let attests = |claim: &str| Attests {
        kind: "qf_bv_validity".into(),
        claim: claim.into(),
        standards: vec![],
    };
    for (tag, script, claim) in [
        (
            "api-unsat",
            UNSAT,
            "the asserted QF_BV script is unsatisfiable",
        ),
        (
            "api-sat",
            SAT,
            "the asserted QF_BV script is satisfiable (model self-checked)",
        ),
    ] {
        let (_, _, text) = echo_bundle_of(tag, script);
        let cli: serde_json::Value = serde_json::from_str(&text).unwrap();
        let (res, _) = ordeal::smtlib::solve_str_with_term(script).unwrap();
        let subject = match res {
            Some(TermCheckResult::Unsat(c)) => EchoSubject::Unsat(c),
            Some(TermCheckResult::Sat(c)) => EchoSubject::Sat(c),
            other => panic!("{other:?}"),
        };
        let api = EchoCertificate::new(subject)
            .expect("the printer accepts")
            .to_cert_v5(&attests(claim));
        let api: serde_json::Value = serde_json::from_str(&api).unwrap();
        assert_eq!(cli, api, "{tag}: the CLI bundle differs from to_cert_v5");
        EchoCertificate::from_cert_v5(&text)
            .expect("the API reader accepts the CLI bundle")
            .recheck()
            .expect("and re-checks it");
    }
}

fn sha256_hex(bytes: &[u8]) -> String {
    ordeal::sha256::sha256_hex(bytes)
}
