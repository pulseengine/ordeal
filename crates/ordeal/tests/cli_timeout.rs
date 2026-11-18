// rivet: verifies VER-093
//! `ordeal check --timeout-ms N` (#314, TR-093), with the real binary. The
//! slow query is #314's own shape at width 64: `x udiv 2^32` against the
//! high half of `x`, which the built-in search did not decide in 300 s on
//! v0.37.0. The bound must turn it into a prompt `unknown` in every output
//! shape, and must not change a verdict the solver reaches in time.

use std::path::PathBuf;
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};

const ORDEAL: &str = env!("CARGO_BIN_EXE_ordeal");

/// #314 at width 64: valid, so the honest answers are `unsat` or `unknown`.
const SLOW: &str = "(set-logic QF_BV)\n(declare-fun x () (_ BitVec 64))\n\
    (assert (distinct (bvudiv x #x0000000100000000) \
    ((_ zero_extend 32) ((_ extract 63 32) x))))\n(check-sat)\n";
/// Decided at once.
const UNSAT: &str = "(set-logic QF_BV)\n(declare-fun x () (_ BitVec 8))\n\
    (assert (distinct (bvadd x #x01) (bvadd #x01 x)))\n(check-sat)\n";

/// The bound plus generous slack for a loaded CI runner; the unbounded solve
/// takes minutes, so this still separates "bounded" from "not bounded".
const SLACK: Duration = Duration::from_secs(20);

fn run(args: &[&str], stdin: &str) -> (Output, Duration) {
    use std::io::Write;
    let start = Instant::now();
    let mut child = Command::new(ORDEAL)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn ordeal");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(stdin.as_bytes())
        .unwrap();
    let out = child.wait_with_output().expect("wait ordeal");
    (out, start.elapsed())
}

fn stdout(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).trim().to_string()
}

#[test]
fn bound_turns_a_slow_solve_into_unknown() {
    let (o, took) = run(&["check", "-", "--timeout-ms", "1000"], SLOW);
    assert_eq!(
        stdout(&o),
        "unknown",
        "stderr: {}",
        String::from_utf8_lossy(&o.stderr)
    );
    assert_eq!(o.status.code(), Some(0));
    assert!(
        took < Duration::from_secs(1) + SLACK,
        "bound ignored: took {took:?}"
    );
}

#[test]
fn bound_keeps_the_json_shape() {
    for extra in [&[][..], &["--with-query"][..], &["--with-term"][..]] {
        let mut args = vec!["check", "-", "--format", "json", "--timeout-ms", "1000"];
        args.extend_from_slice(extra);
        let (o, took) = run(&args, SLOW);
        let line = stdout(&o);
        assert_eq!(
            line,
            format!(
                "{{\"tool\":\"ordeal\",\"version\":\"{}\",\"verdict\":\"unknown\"}}",
                env!("CARGO_PKG_VERSION")
            ),
            "{extra:?}"
        );
        assert_eq!(o.status.code(), Some(0), "{extra:?}");
        assert!(
            took < Duration::from_secs(1) + SLACK,
            "{extra:?}: took {took:?}"
        );
    }
}

#[test]
fn bound_with_cert_out_writes_nothing_and_exits_1() {
    let path = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("timeout-{}.cert.json", std::process::id()));
    let _ = std::fs::remove_file(&path);
    let p = path.to_str().unwrap();
    let (o, took) = run(
        &["check", "-", "--cert-out", p, "--timeout-ms", "1000"],
        SLOW,
    );
    assert_eq!(stdout(&o), "unknown");
    assert_eq!(o.status.code(), Some(1));
    assert!(!path.exists(), "an unknown verdict must not write a bundle");
    assert!(took < Duration::from_secs(1) + SLACK, "took {took:?}");
}

#[test]
fn bound_does_not_change_a_decided_verdict() {
    let (o, _) = run(&["check", "-", "--timeout-ms", "60000"], UNSAT);
    assert_eq!(stdout(&o), "unsat");
    assert_eq!(o.status.code(), Some(0));
    let (o, _) = run(
        &["check", "-", "--timeout-ms", "60000", "--format", "json"],
        UNSAT,
    );
    assert!(stdout(&o).contains("\"verdict\":\"unsat\""));
}

#[test]
fn malformed_bound_is_a_usage_error() {
    for bad in [
        &["--timeout-ms"][..],
        &["--timeout-ms", "soon"][..],
        &["--timeout-ms", "-5"][..],
    ] {
        let mut args = vec!["check", "-"];
        args.extend_from_slice(bad);
        let (o, _) = run(&args, UNSAT);
        assert_eq!(o.status.code(), Some(2), "{bad:?}");
        assert!(o.stdout.is_empty(), "{bad:?}: printed a verdict");
    }
}

#[test]
fn unknown_option_or_second_file_is_a_usage_error() {
    // Before #314 these were ignored, so a misspelled bound ran unbounded.
    for bad in [
        &["--timeout", "1000"][..],
        &["--bogus"][..],
        &["-x"][..],
        &["other.smt2"][..],
    ] {
        let mut args = vec!["check", "-"];
        args.extend_from_slice(bad);
        let (o, _) = run(&args, UNSAT);
        assert_eq!(o.status.code(), Some(2), "{bad:?}");
        assert!(o.stdout.is_empty(), "{bad:?}: printed a verdict");
    }
}
