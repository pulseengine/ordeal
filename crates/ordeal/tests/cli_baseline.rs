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

// rivet: verifies VER-034
fn ordeal_stdin(args: &[&str], input: &str) -> std::process::Output {
    use std::io::Write;
    use std::process::Stdio;
    let mut child = Command::new(env!("CARGO_BIN_EXE_ordeal"))
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn ordeal");
    child
        .stdin
        .take()
        .expect("stdin")
        .write_all(input.as_bytes())
        .expect("write script");
    child.wait_with_output().expect("wait ordeal")
}

const UNSAT_SCRIPT: &str = "(set-logic QF_BV)\n(declare-const a (_ BitVec 8))\n\
     (assert (distinct (bvurem a #x01) #x00))\n(check-sat)\n";
const SAT_SCRIPT: &str = "(set-logic QF_BV)\n(declare-const a (_ BitVec 8))\n\
     (assert (= (bvurem a #x05) #x03))\n(check-sat)\n";

/// TR-037: `--format json` emits one parseable object whose verdict matches
/// text mode, and the unsat object carries the FULL checkable pair — which
/// this test re-checks with the trusted checker, making the JSON itself
/// evidence rather than a claim.
#[test]
fn format_json_unsat_carries_a_recheckable_pair() {
    let out = ordeal_stdin(&["check", "-", "--format", "json"], UNSAT_SCRIPT);
    assert!(out.status.success());
    let v: serde_json::Value =
        serde_json::from_slice(&out.stdout).expect("stdout is one JSON object");
    assert_eq!(v["tool"], "ordeal");
    assert_eq!(v["version"], env!("CARGO_PKG_VERSION"));
    assert_eq!(v["verdict"], "unsat");
    let cnf: Vec<Vec<i32>> = v["certificate"]["clauses"]
        .as_array()
        .expect("clauses")
        .iter()
        .map(|c| {
            c.as_array()
                .expect("clause")
                .iter()
                .map(|l| l.as_i64().expect("lit") as i32)
                .collect()
        })
        .collect();
    let lrat = v["certificate"]["lrat"].as_str().expect("lrat text");
    assert!(!cnf.is_empty() && !lrat.is_empty());
    ordeal_lrat::check(&cnf, lrat).expect("the emitted pair re-checks independently");
}

#[test]
fn format_json_sat_and_unknown_shapes() {
    let out = ordeal_stdin(&["check", "-", "--format", "json"], SAT_SCRIPT);
    assert!(out.status.success());
    let v: serde_json::Value = serde_json::from_slice(&out.stdout).expect("json");
    assert_eq!(v["verdict"], "sat");
    let model = v["model"].as_array().expect("model array");
    let a = model.iter().find(|b| b["name"] == "a").expect("binding a");
    assert_eq!(a["width"], 8);
    // 0x80 = 128; 128 % 5 == 3 — the model value must satisfy the script.
    let val = a["value"].as_str().expect("value string");
    let parsed = u128::from_str_radix(val.trim_start_matches("#x"), 16).expect("hex value");
    assert_eq!(parsed % 5, 3, "model must satisfy a % 5 == 3, got {val}");
}

#[test]
fn format_json_verdicts_match_text_mode() {
    for script in [UNSAT_SCRIPT, SAT_SCRIPT] {
        let text = ordeal_stdin(&["check", "-"], script);
        let json = ordeal_stdin(&["check", "-", "--format", "json"], script);
        assert_eq!(text.status.code(), json.status.code(), "exit codes match");
        let text_verdict = String::from_utf8_lossy(&text.stdout)
            .lines()
            .next()
            .expect("text verdict")
            .to_string();
        let v: serde_json::Value = serde_json::from_slice(&json.stdout).expect("json");
        assert_eq!(v["verdict"], text_verdict.as_str());
    }
}

#[test]
fn format_json_is_advertised_in_top_level_help() {
    let out = ordeal(&["--help"]);
    let help = String::from_utf8_lossy(&out.stdout);
    assert!(
        help.contains("--format json"),
        "rule 3: the flag is advertised at top level, got:\n{help}"
    );
}

#[test]
fn unknown_format_value_exits_two() {
    let out = ordeal_stdin(&["check", "-", "--format", "yaml"], SAT_SCRIPT);
    assert_eq!(out.status.code(), Some(2));
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
