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
        err.contains("unknown command") && err.contains("Usage:"),
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
    // A child that rejects its arguments (e.g. `--format yaml`) exits
    // before ever reading stdin, so this write can race the exit and see
    // EPIPE — expected, not an error (observed as a Linux-only flake in
    // CI; macOS pipe buffering masked it). Anything else is real.
    if let Err(e) = child
        .stdin
        .take()
        .expect("stdin")
        .write_all(input.as_bytes())
    {
        assert_eq!(
            e.kind(),
            std::io::ErrorKind::BrokenPipe,
            "write script failed: {e}"
        );
    }
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
    // soundness property; #140 pinned the proof-status sentence after the
    // banner shipped a stale "remaining obligation" claim. Pin the
    // load-bearing phrases so a help rework cannot silently drop them —
    // or drift the proof status back to "open".
    let out = ordeal(&["--help"]);
    assert!(out.status.success());
    let help = String::from_utf8_lossy(&out.stdout);
    for needle in [
        "Usage:",
        "LRAT certificate",
        "ordeal-lrat checker",
        "discharged and CI-gated against the",
        "regenerated model",
    ] {
        assert!(help.contains(needle), "help must contain `{needle}`");
    }
}

/// Lowercase hex of an independent digest (sha2 0.11 arrays have no LowerHex).
fn hex_of(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

// rivet: verifies VER-042
/// #162 / TR-045: the `sat` JSON carries the FULL witness — clauses,
/// complete assignment, per-variable bit map, both content hashes — and
/// this test re-establishes the verdict with the trusted crate (zero trust
/// in the CLI process), checks every advertised model value against the
/// bit map, and recomputes the hashes with an INDEPENDENT SHA-256 (`sha2`,
/// dev-only) so the in-tree implementation the binary ships is itself
/// cross-checked on real output.
#[test]
fn format_json_sat_carries_a_recheckable_witness() {
    use sha2::Digest;
    let out = ordeal_stdin(&["check", "-", "--format", "json"], SAT_SCRIPT);
    assert!(out.status.success());
    let v: serde_json::Value = serde_json::from_slice(&out.stdout).expect("json");
    assert_eq!(v["verdict"], "sat");
    let cert = &v["certificate"];
    let cnf: Vec<Vec<i32>> = cert["clauses"]
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
    let w = &cert["witness"];
    assert_eq!(w["encoding"], "bitstring-lsb-var1");
    let bitstring = w["assignment"].as_str().expect("assignment bitstring");
    let assignment: Vec<bool> = bitstring
        .chars()
        .map(|c| match c {
            '0' => false,
            '1' => true,
            other => panic!("non-bit character {other:?} in the assignment"),
        })
        .collect();
    assert!(!cnf.is_empty() && !assignment.is_empty());
    // 1. Every clause is satisfied — the trusted crate says so, not the CLI.
    ordeal_lrat::check_sat(&cnf, &assignment).expect("the emitted witness re-checks");
    // 2. Every advertised model value IS what the assignment says, bit by bit.
    let model = v["model"].as_array().expect("model array");
    let bit_map = w["bit_map"].as_array().expect("bit map");
    assert_eq!(model.len(), 1, "one declared variable");
    for binding in model {
        let name = binding["name"].as_str().expect("name");
        let width = binding["width"].as_u64().expect("width");
        let value = u128::from_str_radix(
            binding["value"]
                .as_str()
                .expect("value")
                .trim_start_matches("#x"),
            16,
        )
        .expect("hex value");
        let entry = bit_map
            .iter()
            .find(|e| e["name"] == name)
            .expect("every model variable has a bit-map entry");
        assert_eq!(entry["width"].as_u64().expect("bm width"), width);
        let bits: Vec<i32> = entry["bits"]
            .as_array()
            .expect("bits")
            .iter()
            .map(|b| b.as_i64().expect("bit lit") as i32)
            .collect();
        assert_eq!(bits.len() as u64, width);
        ordeal_lrat::check_binding(&assignment, &bits, value)
            .expect("the advertised model value is bound by the witness");
        assert_eq!(value % 5, 3, "and it satisfies the script");
    }
    // 3. The content hashes are what an independent SHA-256 computes over
    //    the documented canonical texts.
    let assignment_sha = hex_of(&sha2::Sha256::digest(bitstring.as_bytes()));
    assert_eq!(w["assignment_sha256"], assignment_sha);
    let mut bit_map_text = String::new();
    for e in bit_map {
        bit_map_text.push_str(e["name"].as_str().unwrap());
        bit_map_text.push(' ');
        bit_map_text.push_str(&e["width"].as_u64().unwrap().to_string());
        for b in e["bits"].as_array().unwrap() {
            bit_map_text.push(' ');
            bit_map_text.push_str(&b.as_i64().unwrap().to_string());
        }
        bit_map_text.push('\n');
    }
    let bit_map_sha = hex_of(&sha2::Sha256::digest(bit_map_text.as_bytes()));
    assert_eq!(w["bit_map_sha256"], bit_map_sha);
}

/// A tampered witness must be REJECTED by the same re-check a consumer
/// runs — the negative control that proves test above is not vacuous:
/// flip one assignment bit that a model variable is bound to.
#[test]
fn tampered_sat_witness_is_rejected_by_the_trusted_crate() {
    let out = ordeal_stdin(&["check", "-", "--format", "json"], SAT_SCRIPT);
    let v: serde_json::Value = serde_json::from_slice(&out.stdout).expect("json");
    let w = &v["certificate"]["witness"];
    let mut assignment: Vec<bool> = w["assignment"]
        .as_str()
        .unwrap()
        .chars()
        .map(|c| c == '1')
        .collect();
    let entry = &w["bit_map"].as_array().unwrap()[0];
    let bits: Vec<i32> = entry["bits"]
        .as_array()
        .unwrap()
        .iter()
        .map(|b| b.as_i64().unwrap() as i32)
        .collect();
    let value = u128::from_str_radix(
        v["model"][0]["value"]
            .as_str()
            .unwrap()
            .trim_start_matches("#x"),
        16,
    )
    .unwrap();
    ordeal_lrat::check_binding(&assignment, &bits, value).expect("pristine binding holds");
    let var = bits[0].unsigned_abs() as usize - 1;
    assignment[var] = !assignment[var];
    assert!(
        ordeal_lrat::check_binding(&assignment, &bits, value).is_err(),
        "a flipped witness bit must break the advertised binding"
    );
}
