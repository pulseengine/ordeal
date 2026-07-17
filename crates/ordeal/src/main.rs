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

use ordeal::CheckResult;
use ordeal::smtlib::{self, Outcome};
use ordeal::verus;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(String::as_str) {
        None => {
            banner();
            ExitCode::SUCCESS
        }
        Some("check") => run_check(args.get(2).map(String::as_str)),
        Some("verus") => run_verus(&args[2..]),
        Some("-h" | "--help") => {
            banner();
            ExitCode::SUCCESS
        }
        Some(other) => {
            eprintln!("ordeal: unknown command '{other}'");
            eprintln!("usage: ordeal check [FILE | -]   (reads stdin if FILE is '-' or omitted)");
            eprintln!("       ordeal verus <VERUS-LOG.smt2 | DIR> [--cert-out DIR]");
            ExitCode::from(2)
        }
    }
}

/// Read a script from `path` (a file, or stdin when `-`/omitted), solve it,
/// and print the verdict. Returns the process exit code: 0 on a cleanly
/// decided run (including `unknown`), non-zero on a read/parse/unsupported
/// error.
fn run_check(path: Option<&str>) -> ExitCode {
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

    match smtlib::solve_str(&input) {
        Ok(outcome) => print_outcome(&outcome),
        Err(e) => {
            // Prints `parse error: ...` / `unsupported: ...` / `solver error: ...`.
            eprintln!("{e}");
            ExitCode::from(2)
        }
    }
}

/// Print the verdict (and, on `sat`, the model) and return the exit code.
fn print_outcome(outcome: &Outcome) -> ExitCode {
    let Some(result) = &outcome.result else {
        eprintln!("ordeal: script contained no (check-sat) command");
        return ExitCode::from(2);
    };
    match result {
        CheckResult::Sat(model) => {
            println!("sat");
            print_model(model, &outcome.declared);
        }
        CheckResult::Unsat(cert) => {
            println!("unsat");
            // Note the certificate on stderr so stdout stays a clean verdict.
            eprintln!(
                "; unsat certificate: {} bytes of checker-validated LRAT",
                cert.lrat.len()
            );
        }
        CheckResult::Unknown => println!("unknown"),
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
    println!("usage:");
    println!("  ordeal check <file.smt2>   solve a QF_BV SMT-LIB2 script");
    println!("  ordeal check -             solve a script read from stdin");
    println!();
    println!("engine: certificate-checked pipeline (bit-blast -> AIG -> Tseitin ->");
    println!("own CDCL core -> LRAT). SAT verdicts carry self-checked models;");
    println!("UNSAT verdicts carry an LRAT certificate validated by the");
    println!("ordeal-lrat checker before being returned — an Unsat the checker");
    println!("did not accept is never reported. The checker's formal soundness");
    println!("proof (Aeneas -> Lean 4) is the remaining P2 obligation.");
    println!("See ROADMAP.md (phases P0-P5) for status.");
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
    let mut path: Option<&str> = None;
    let mut cert_out: Option<&str> = None;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--cert-out" => match args.get(i + 1) {
                Some(d) => {
                    cert_out = Some(d.as_str());
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
        eprintln!("usage: ordeal verus <VERUS-LOG.smt2 | DIR> [--cert-out DIR]");
        return ExitCode::from(2);
    };

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
                        println!("FAIL {who}: certificate did not re-check: {e}");
                        failed += 1;
                        continue;
                    }
                    println!("unsat  {who}  ({} bytes of checked LRAT)", cert.lrat.len());
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
                    println!("SAT    {who}  — obligation does NOT hold (counterexample exists)");
                    failed += 1;
                }
                Some(CheckResult::Unknown) => {
                    println!("unknown {who} — undecided; treat conservatively");
                    failed += 1;
                }
                None => {
                    println!("FAIL   {who}: no (check-sat) in the sliced obligation");
                    failed += 1;
                }
            },
            Err(e) => {
                println!("FAIL   {who}: {e}");
                failed += 1;
            }
        }
    }

    println!(
        "\n{discharged} discharged, {failed} failed, {skipped} skipped (not bitvector queries)"
    );
    if failed > 0 || discharged == 0 {
        ExitCode::from(1)
    } else {
        ExitCode::SUCCESS
    }
}
