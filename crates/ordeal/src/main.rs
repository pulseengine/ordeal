//! The `ordeal` CLI.
//!
//! The production interface is the Rust API (loom/synth embed the crate
//! in-process; see TR-010/SYS-006). This binary adds a small **QF_BV
//! SMT-LIB2** front end for standalone testing and a differential harness
//! (loom field-report #34): `ordeal check <file.smt2>` (or `-`/stdin) parses a
//! script, solves it, and prints `sat` / `unsat` / `unknown`. With no
//! arguments it prints the engine-status banner.
//!
//! The parser and solver logic live in [`ordeal::smtlib`] (pure `std`, no
//! I/O, so the library stays `wasm32-wasip2`-clean); this file only owns
//! stdin/file reading, model formatting, and exit codes.

use std::io::Read;
use std::process::ExitCode;

use ordeal::smtlib;
use ordeal::verus;
use ordeal::{CheckResult, WitnessCheckResult};

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(String::as_str) {
        None => {
            banner();
            ExitCode::SUCCESS
        }
        Some("check") => run_check(&args[2..]),
        Some("verus") => run_verus(&args[2..]),
        Some("-h" | "--help") => {
            banner();
            ExitCode::SUCCESS
        }
        // Machine-quotable version (issue #120 / org CLI baseline,
        // pulseengine.eu#167): qualification evidence must cite tool
        // versions without scraping the help banner. Exit 0, one line.
        Some("-V" | "--version" | "version") => {
            println!("ordeal {}", env!("CARGO_PKG_VERSION"));
            ExitCode::SUCCESS
        }
        Some(other) => {
            eprintln!("ordeal: unknown command '{other}'");
            eprintln!(
                "Usage: ordeal check [FILE | -] [--format json]   (reads stdin if FILE is '-' or omitted)"
            );
            eprintln!(
                "       ordeal verus <VERUS-LOG.smt2 | DIR> [--cert-out DIR] [--format json]"
            );
            ExitCode::from(2)
        }
    }
}

/// Output format for verdicts (issue #132 / TR-037, org CLI-baseline rule 3:
/// gates parse `--format json`, never scrape human output). Errors stay
/// human-readable on stderr in both modes — an error is not a verdict.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Format {
    Text,
    Json,
}

/// Extract `--format <text|json>` from an argument list, returning the
/// remaining positional arguments. `Err` carries the exit code for a
/// malformed or unknown format value.
fn parse_format(args: &[String]) -> Result<(Format, Vec<&str>), ExitCode> {
    let mut format = Format::Text;
    let mut rest: Vec<&str> = Vec::new();
    let mut i = 0;
    while i < args.len() {
        if args[i] == "--format" {
            match args.get(i + 1).map(String::as_str) {
                Some("json") => format = Format::Json,
                Some("text") => format = Format::Text,
                Some(other) => {
                    eprintln!("ordeal: unknown format '{other}' (expected 'json' or 'text')");
                    return Err(ExitCode::from(2));
                }
                None => {
                    eprintln!("ordeal: --format needs a value ('json' or 'text')");
                    return Err(ExitCode::from(2));
                }
            }
            i += 2;
        } else {
            rest.push(args[i].as_str());
            i += 1;
        }
    }
    Ok((format, rest))
}

/// Read a script from the positional FILE (or stdin when `-`/omitted), solve
/// it, and print the verdict in the selected format. Returns the process
/// exit code: 0 on a cleanly decided run (including `unknown`), non-zero on
/// a read/parse/unsupported error.
fn run_check(args: &[String]) -> ExitCode {
    let (format, rest) = match parse_format(args) {
        Ok(pair) => pair,
        Err(code) => return code,
    };
    let path = rest.first().copied();
    let input = match path {
        None | Some("-") => {
            let mut buf = String::new();
            if let Err(e) = std::io::stdin().read_to_string(&mut buf) {
                eprintln!("ordeal: cannot read stdin: {e}");
                return ExitCode::from(2);
            }
            buf
        }
        Some(file) => match std::fs::read_to_string(file) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("ordeal: cannot read '{file}': {e}");
                return ExitCode::from(2);
            }
        },
    };

    // The witness-carrying solve (TR-038): a `sat` is only ever printed
    // after the trusted crate re-checked its witness, and `--format json`
    // carries that witness so the consumer can re-check it too (#162).
    match smtlib::solve_str_with_witness(&input) {
        Ok((result, declared)) => match format {
            Format::Text => print_outcome(result.as_ref(), &declared),
            Format::Json => print_outcome_json(result.as_ref(), &declared),
        },
        Err(e) => {
            // Prints `parse error: ...` / `unsupported: ...` / `solver error: ...`.
            eprintln!("{e}");
            ExitCode::from(2)
        }
    }
}

/// Minimal JSON string escaping (quotes, backslash, control characters).
/// Hand-rolled on purpose: the default build stays dependency-free, and the
/// values are verdicts, identifiers from the input script, and LRAT text.
fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out
}

/// DIMACS clauses as a JSON array-of-arrays body (no brackets around the
/// whole): `[1,-2],[3]`.
fn clauses_json(cnf: &[Vec<i32>]) -> String {
    cnf.iter()
        .map(|c| {
            let lits: Vec<String> = c.iter().map(ToString::to_string).collect();
            format!("[{}]", lits.join(","))
        })
        .collect::<Vec<_>>()
        .join(",")
}

/// One JSON object on stdout — the structured twin of [`print_outcome`].
/// Both verdict directions carry their FULL re-checkable evidence: on
/// `unsat` the CNF clauses + LRAT text (`ordeal_lrat::check`), on `sat`
/// the CNF clauses + the `witness` block — the complete assignment, the
/// per-variable bit map and both content hashes, byte-identical to the
/// `ordeal-cert/v1` witness the API emits (`ordeal_lrat::check_sat` +
/// `check_binding`). Strictly stronger than a hash: a consumer
/// re-establishes either verdict with zero trust in this process.
fn print_outcome_json(result: Option<&WitnessCheckResult>, declared: &[(String, u32)]) -> ExitCode {
    let Some(result) = result else {
        eprintln!("ordeal: script contained no (check-sat) command");
        return ExitCode::from(2);
    };
    let head = format!(
        "{{\"tool\":\"ordeal\",\"version\":\"{}\"",
        env!("CARGO_PKG_VERSION")
    );
    match result {
        WitnessCheckResult::Sat(cert) => {
            let model = &cert.model;
            let value_of = |name: &str| -> u128 {
                model
                    .assignments
                    .iter()
                    .find(|(k, _)| k == name)
                    .map(|(_, v)| *v)
                    .unwrap_or(0)
            };
            let bindings: Vec<String> = declared
                .iter()
                .map(|(name, width)| {
                    format!(
                        "{{\"name\":\"{}\",\"width\":{},\"value\":\"{}\"}}",
                        json_escape(name),
                        width,
                        fmt_bv(*width, value_of(name))
                    )
                })
                .collect();
            let bit_map: Vec<String> = cert
                .bit_map
                .iter()
                .map(|(name, width, bits)| {
                    let lits: Vec<String> = bits.iter().map(ToString::to_string).collect();
                    format!(
                        "{{\"name\":\"{}\",\"width\":{},\"bits\":[{}]}}",
                        json_escape(name),
                        width,
                        lits.join(",")
                    )
                })
                .collect();
            println!(
                "{head},\"verdict\":\"sat\",\"model\":[{}],\"certificate\":{{\"clauses\":[{}],\"witness\":{{\"encoding\":\"{}\",\"assignment\":\"{}\",\"bit_map\":[{}],\"assignment_sha256\":\"{}\",\"bit_map_sha256\":\"{}\"}}}}}}",
                bindings.join(","),
                clauses_json(&cert.cnf),
                ordeal::witness::WITNESS_ENCODING,
                cert.assignment_bitstring(),
                bit_map.join(","),
                cert.assignment_sha256(),
                cert.bit_map_sha256()
            );
        }
        WitnessCheckResult::Unsat(cert) => {
            let lrat = cert.lrat_text().unwrap_or_default();
            println!(
                "{head},\"verdict\":\"unsat\",\"certificate\":{{\"clauses\":[{}],\"lrat\":\"{}\"}}}}",
                clauses_json(&cert.cnf),
                json_escape(lrat)
            );
        }
        WitnessCheckResult::Unknown => println!("{head},\"verdict\":\"unknown\"}}"),
    }
    ExitCode::SUCCESS
}

/// Print the verdict (and, on `sat`, the model) and return the exit code.
fn print_outcome(result: Option<&WitnessCheckResult>, declared: &[(String, u32)]) -> ExitCode {
    let Some(result) = result else {
        eprintln!("ordeal: script contained no (check-sat) command");
        return ExitCode::from(2);
    };
    match result {
        WitnessCheckResult::Sat(cert) => {
            println!("sat");
            print_model(&cert.model, declared);
            // Note the witness on stderr so stdout stays a clean verdict.
            eprintln!(
                "; sat witness: {} variables re-checked by the trusted crate against {} clauses",
                cert.assignment.len(),
                cert.cnf.len()
            );
        }
        WitnessCheckResult::Unsat(cert) => {
            println!("unsat");
            // Note the certificate on stderr so stdout stays a clean verdict.
            eprintln!(
                "; unsat certificate: {} bytes of checker-validated LRAT",
                cert.lrat.len()
            );
        }
        WitnessCheckResult::Unknown => println!("unknown"),
    }
    ExitCode::SUCCESS
}

/// Print a satisfying model in SMT-LIB style, one binding per line:
/// `((x #x0000002a) (y #b101))`. Every declared variable is shown; one that
/// never reached an assertion is unconstrained and printed as zero.
fn print_model(model: &ordeal::Model, declared: &[(String, u32)]) {
    if declared.is_empty() {
        return;
    }
    let value_of = |name: &str| -> u128 {
        model
            .assignments
            .iter()
            .find(|(k, _)| k == name)
            .map(|(_, v)| *v)
            .unwrap_or(0)
    };
    let n = declared.len();
    for (i, (name, width)) in declared.iter().enumerate() {
        let open = if i == 0 { "(" } else { " " };
        let close = if i + 1 == n { ")" } else { "" };
        println!("{open}({name} {}){close}", fmt_bv(*width, value_of(name)));
    }
}

/// Format a `width`-bit value as an SMT-LIB literal: `#x…` when the width is a
/// multiple of 4, otherwise `#b…` (SMT-LIB only allows hex on nibble-aligned
/// widths).
fn fmt_bv(width: u32, value: u128) -> String {
    let masked = if width >= 128 {
        value
    } else {
        value & ((1u128 << width) - 1)
    };
    if width.is_multiple_of(4) {
        let nibbles = (width / 4) as usize;
        format!("#x{masked:0nibbles$x}")
    } else {
        let mut s = String::from("#b");
        for i in (0..width).rev() {
            s.push(if (masked >> i) & 1 == 1 { '1' } else { '0' });
        }
        s
    }
}

/// Print the engine-status banner (bare `ordeal`, `-h`, `--help`).
fn banner() {
    let version = env!("CARGO_PKG_VERSION");
    println!("ordeal {version}");
    println!("certificate-checked QF_BV SMT solver for the PulseEngine toolchain");
    println!();
    println!("Usage:");
    println!("  ordeal check <file.smt2>   solve a QF_BV SMT-LIB2 script");
    println!("  ordeal check -             solve a script read from stdin");
    println!("  ordeal verus <log | dir>   discharge Verus `by (bit_vector)`");
    println!("                             obligations from a --log-all dump");
    println!("  ordeal -V | --version      print `ordeal <semver>` and exit");
    println!("  --format json              structured verdict on stdout (check and");
    println!("                             verus); unsat carries the full checkable");
    println!("                             pair (CNF clauses + LRAT text)");
    println!();
    println!("engine: certificate-checked pipeline (bit-blast -> AIG -> Tseitin ->");
    println!("own CDCL core -> LRAT). SAT verdicts carry self-checked models;");
    println!("UNSAT verdicts carry an LRAT certificate validated by the");
    println!("ordeal-lrat checker before being returned — an Unsat the checker");
    println!("did not accept is never reported. The checker's soundness proof");
    println!("(Aeneas -> Lean 4) is discharged and CI-gated against the");
    println!("regenerated model.");
    println!("See ROADMAP.md for where the roadmap lives (the rivet graph).");
}

/// `ordeal verus <log|dir> [--cert-out DIR]` — discharge the `by (bit_vector)`
/// obligations Verus emitted (TR-023, issue #65).
///
/// Point it at a `--log-all` file or directory. Prelude dumps (`root.smt2`) and
/// ordinary quantified queries are **skipped, not failed**: only queries Verus
/// itself marked as spun off for bitvector reasoning are in the QF_BV fragment.
///
/// Exit code is non-zero if any obligation fails to discharge, so this can gate
/// a build: `unsat` means the obligation holds and the certificate re-checked.
fn run_verus(args: &[String]) -> ExitCode {
    let (format, rest) = match parse_format(args) {
        Ok(pair) => pair,
        Err(code) => return code,
    };
    let mut path: Option<&str> = None;
    let mut cert_out: Option<&str> = None;
    let mut i = 0;
    while i < rest.len() {
        match rest[i] {
            "--cert-out" => match rest.get(i + 1) {
                Some(d) => {
                    cert_out = Some(*d);
                    i += 2;
                }
                None => {
                    eprintln!("ordeal: --cert-out needs a directory");
                    return ExitCode::from(2);
                }
            },
            other => {
                path = Some(other);
                i += 1;
            }
        }
    }
    let Some(path) = path else {
        eprintln!("Usage: ordeal verus <VERUS-LOG.smt2 | DIR> [--cert-out DIR] [--format json]");
        return ExitCode::from(2);
    };
    // Per-obligation records for --format json: (name, verdict, lrat_bytes).
    let mut records: Vec<(String, &'static str, usize)> = Vec::new();
    let text = format == Format::Text;

    let mut files: Vec<std::path::PathBuf> = Vec::new();
    let p = std::path::Path::new(path);
    if p.is_dir() {
        match std::fs::read_dir(p) {
            Ok(rd) => {
                for e in rd.flatten() {
                    let f = e.path();
                    if f.extension().and_then(|x| x.to_str()) == Some("smt2") {
                        files.push(f);
                    }
                }
            }
            Err(e) => {
                eprintln!("ordeal: cannot read directory '{path}': {e}");
                return ExitCode::from(2);
            }
        }
        files.sort();
    } else {
        files.push(p.to_path_buf());
    }

    if let Some(dir) = cert_out
        && let Err(e) = std::fs::create_dir_all(dir)
    {
        eprintln!("ordeal: cannot create '{dir}': {e}");
        return ExitCode::from(2);
    }

    let (mut discharged, mut skipped, mut failed) = (0usize, 0usize, 0usize);
    for f in &files {
        let log = match std::fs::read_to_string(f) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("ordeal: cannot read '{}': {e}", f.display());
                failed += 1;
                continue;
            }
        };
        if !verus::is_bitvector_query(&log) {
            skipped += 1;
            continue;
        }
        let ob = match verus::extract(&log) {
            Ok(o) => o,
            Err(e) => {
                eprintln!("{}: {e}", f.display());
                failed += 1;
                continue;
            }
        };
        let who = ob
            .location
            .clone()
            .unwrap_or_else(|| f.display().to_string());
        match smtlib::solve_str(&ob.script) {
            Ok(outcome) => match outcome.result {
                Some(CheckResult::Unsat(cert)) => {
                    // The verdict is only worth as much as the re-check.
                    if let Err(e) = cert.recheck() {
                        if text {
                            println!("FAIL {who}: certificate did not re-check: {e}");
                        }
                        records.push((who.clone(), "recheck-failed", 0));
                        failed += 1;
                        continue;
                    }
                    if text {
                        println!("unsat  {who}  ({} bytes of checked LRAT)", cert.lrat.len());
                    }
                    records.push((who.clone(), "unsat", cert.lrat.len()));
                    discharged += 1;
                    if let Some(dir) = cert_out {
                        let name = f
                            .file_stem()
                            .and_then(|s| s.to_str())
                            .unwrap_or("obligation");
                        let out = std::path::Path::new(dir).join(format!("{name}.lrat"));
                        if let Err(e) = std::fs::write(&out, &cert.lrat) {
                            eprintln!("ordeal: cannot write '{}': {e}", out.display());
                            failed += 1;
                        }
                    }
                }
                // Verus posed the obligation as `premises AND NOT goal`, so a
                // model means the lemma does NOT hold as stated.
                Some(CheckResult::Sat(_)) => {
                    if text {
                        println!(
                            "SAT    {who}  — obligation does NOT hold (counterexample exists)"
                        );
                    }
                    records.push((who.clone(), "sat", 0));
                    failed += 1;
                }
                Some(CheckResult::Unknown) => {
                    if text {
                        println!("unknown {who} — undecided; treat conservatively");
                    }
                    records.push((who.clone(), "unknown", 0));
                    failed += 1;
                }
                None => {
                    if text {
                        println!("FAIL   {who}: no (check-sat) in the sliced obligation");
                    }
                    records.push((who.clone(), "error", 0));
                    failed += 1;
                }
            },
            Err(e) => {
                if text {
                    println!("FAIL   {who}: {e}");
                }
                records.push((who.clone(), "error", 0));
                failed += 1;
            }
        }
    }

    if text {
        println!(
            "\n{discharged} discharged, {failed} failed, {skipped} skipped (not bitvector queries)"
        );
    } else {
        let obligations: Vec<String> = records
            .iter()
            .map(|(name, verdict, lrat_bytes)| {
                format!(
                    "{{\"name\":\"{}\",\"verdict\":\"{verdict}\",\"lrat_bytes\":{lrat_bytes}}}",
                    json_escape(name)
                )
            })
            .collect();
        println!(
            "{{\"tool\":\"ordeal\",\"version\":\"{}\",\"discharged\":{discharged},\"failed\":{failed},\"skipped\":{skipped},\"obligations\":[{}]}}",
            env!("CARGO_PKG_VERSION"),
            obligations.join(",")
        );
    }
    if failed > 0 || discharged == 0 {
        ExitCode::from(1)
    } else {
        ExitCode::SUCCESS
    }
}
