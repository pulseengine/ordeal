// rivet: verifies VER-099
//! Every documented exit code of the native binary (TR-099). These are the
//! five cases `scripts/wasm_native_differential.sh` pins: the wasm component
//! must give the same code, so the native side is the reference it is
//! compared against. 2026-11-27: the v0.38.0 components reported exit 2 as
//! exit 1, which a corpus that only exits 0 could not see.

use std::io::Write;
use std::process::{Command, Stdio};

const TWO_CHECKSAT: &str = "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n(assert (= x x))\n(check-sat)\n(check-sat)\n";
// 200 bits is past the solver's width bound, so the verdict is `unknown`.
const WIDE: &str =
    "(set-logic QF_BV)\n(declare-const x (_ BitVec 200))\n(assert (= x x))\n(check-sat)\n";

fn exit_code(stdin: &str, args: &[&str]) -> i32 {
    let mut child = Command::new(env!("CARGO_BIN_EXE_ordeal"))
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .expect("run ordeal binary");
    child
        .stdin
        .take()
        .expect("stdin")
        .write_all(stdin.as_bytes())
        .expect("write stdin");
    child
        .wait()
        .expect("wait for ordeal")
        .code()
        .expect("exit code")
}

#[test]
fn documented_exit_codes_hold_on_the_native_binary() {
    let dir = std::env::temp_dir().join(format!("ordeal-exit-codes-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let cert = dir.join("unknown.cert.json");
    let cert = cert.to_str().expect("utf-8 temp path");
    let cases: [(&str, i32, &str, Vec<&str>); 5] = [
        ("unknown command", 2, "", vec!["zz-no-such-command"]),
        (
            "unknown --format value",
            2,
            WIDE,
            vec!["check", "-", "--format", "yaml"],
        ),
        (
            "more than one check-sat",
            2,
            TWO_CHECKSAT,
            vec!["check", "-"],
        ),
        (
            "unknown verdict with --cert-out",
            1,
            WIDE,
            vec!["check", "-", "--cert-out", cert],
        ),
        (
            "unknown verdict, no certificate asked",
            0,
            WIDE,
            vec!["check", "-"],
        ),
    ];
    for (label, want, stdin, args) in cases {
        assert_eq!(
            exit_code(stdin, &args),
            want,
            "{label}: documented exit {want}"
        );
    }
    assert!(
        !std::path::Path::new(cert).exists(),
        "an unknown verdict writes no certificate"
    );
    let _ = std::fs::remove_dir_all(&dir);
}
