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

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(String::as_str) {
        None => {
            banner();
            ExitCode::SUCCESS
        }
        Some("check") => run_check(args.get(2).map(String::as_str)),
        Some("-h" | "--help") => {
            banner();
            ExitCode::SUCCESS
        }
        Some(other) => {
            eprintln!("ordeal: unknown command '{other}'");
            eprintln!("usage: ordeal check [FILE | -]   (reads stdin if FILE is '-' or omitted)");
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
