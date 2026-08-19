// rivet: verifies VER-032
//! Org CLI-baseline contract (issue #120 / pulseengine.eu#167): the version
//! is machine-quotable (qualification evidence must cite tool versions
//! without scraping help banners), and unknown flags keep the strict
//! exit-2-with-usage behaviour the survey singled out as the reference.

use std::process::Command;

fn ordeal(args: &[&str]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_ordeal"))
        .args(args)
        .output()
        .expect("run ordeal binary")
}

#[test]
fn version_flags_print_semver_and_exit_zero() {
    let expect = format!("ordeal {}\n", env!("CARGO_PKG_VERSION"));
    for flag in ["--version", "-V", "version"] {
        let out = ordeal(&[flag]);
        assert!(out.status.success(), "{flag} must exit 0");
        assert_eq!(
            String::from_utf8_lossy(&out.stdout),
            expect,
            "{flag} must print exactly `ordeal <semver>`"
        );
        assert!(out.stderr.is_empty(), "{flag} must not write to stderr");
    }
}

#[test]
fn unknown_flag_exits_two_with_usage_on_stderr() {
    let out = ordeal(&["--definitely-not-a-flag"]);
    assert_eq!(out.status.code(), Some(2), "unknown flags exit 2");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(
        err.contains("unknown command") && err.contains("usage:"),
        "stderr carries the diagnosis and usage, got: {err}"
    );
    assert!(out.stdout.is_empty(), "errors do not pollute stdout");
}

#[test]
fn help_keeps_the_honesty_banner() {
    // #120 explicitly asked to preserve the help text that states the
    // soundness property and the outstanding obligation. Pin the
    // load-bearing phrases so a help rework cannot silently drop them.
    let out = ordeal(&["--help"]);
    assert!(out.status.success());
    let help = String::from_utf8_lossy(&out.stdout);
    for needle in ["Usage:", "LRAT certificate", "ordeal-lrat checker"] {
        assert!(help.contains(needle), "help must contain `{needle}`");
    }
}
