//! `ordeal-recheck` — re-check `ordeal-cert/v1`..`v4` certificate bundles
//! with no solver in the dependency closure (TR-075, issue #277).
//!
//! An auditor holding a bundle does not have to trust, build or even have
//! the ordeal solver: this binary is built from `ordeal-cert` (the decoder
//! and the recheck glue) and the trusted `ordeal-lrat` alone — CI asserts
//! that closure (`scripts/recheck_closure.sh`). For each file it reads the
//! declared `format` and `verdict`, decodes the bundle with the matching
//! `ordeal-cert` reader (every content hash verified before anything is
//! returned), and runs the full recheck of that format:
//!
//! | format | unsat | sat |
//! |---|---|---|
//! | `ordeal-cert/v1` | `ordeal_lrat::check` (CNF + LRAT) | `check_sat` + `check_binding` |
//! | `ordeal-cert/v2` | `check_query` (re-encodes the DAG) | `check_query_model` |
//! | `ordeal-cert/v3` | `check_term_dag` + `check_query` | + term bindings, `check_tree_model` |
//! | `ordeal-cert/v4` | `check_sliver_lowering` + v3 | + pullback, `check_tree_model_ext` |
//!
//! Exit status: 0 iff every bundle was accepted; 1 if any was rejected,
//! unreadable or malformed; 2 on a usage error.

use std::process::ExitCode;

use ordeal_cert::cert_bundle::{BundleError, bundle_header};
use ordeal_cert::{
    Certificate, QueryCertificate, QuerySatCertificate, SatCertificate, SliverCertificate,
    SliverSatCertificate, TermCertificate, TermSatCertificate,
};

const USAGE: &str = "Usage: ordeal-recheck [--format text|json] <bundle.json>...";

#[derive(Clone, Copy, PartialEq, Eq)]
enum Format {
    Text,
    Json,
}

/// One file's outcome.
struct Outcome {
    file: String,
    /// The declared `format` / `verdict`, when the header could be read.
    format: Option<String>,
    verdict: Option<String>,
    /// `Ok(())` accepted; `Err(reason)` rejected.
    result: Result<(), String>,
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut format = Format::Text;
    let mut files: Vec<String> = Vec::new();
    let mut i = 0;
    let mut only_files = false;
    while i < args.len() {
        let a = args[i].as_str();
        if only_files {
            files.push(a.to_string());
            i += 1;
            continue;
        }
        match a {
            "-V" | "--version" => {
                println!("ordeal-recheck {}", env!("CARGO_PKG_VERSION"));
                return ExitCode::SUCCESS;
            }
            "-h" | "--help" => {
                help();
                return ExitCode::SUCCESS;
            }
            "--format" => {
                match args.get(i + 1).map(String::as_str) {
                    Some("text") => format = Format::Text,
                    Some("json") => format = Format::Json,
                    Some(other) => {
                        eprintln!(
                            "ordeal-recheck: unknown format '{other}' (expected 'text' or 'json')"
                        );
                        eprintln!("{USAGE}");
                        return ExitCode::from(2);
                    }
                    None => {
                        eprintln!("ordeal-recheck: --format needs a value ('text' or 'json')");
                        eprintln!("{USAGE}");
                        return ExitCode::from(2);
                    }
                }
                i += 2;
                continue;
            }
            "--" => only_files = true,
            flag if flag.starts_with('-') && flag != "-" => {
                eprintln!("ordeal-recheck: unknown flag '{flag}'");
                eprintln!("{USAGE}");
                return ExitCode::from(2);
            }
            file => files.push(file.to_string()),
        }
        i += 1;
    }
    if files.is_empty() {
        eprintln!("ordeal-recheck: no bundle given");
        eprintln!("{USAGE}");
        return ExitCode::from(2);
    }

    let outcomes: Vec<Outcome> = files.iter().map(|f| recheck_file(f)).collect();
    let rejected = outcomes.iter().filter(|o| o.result.is_err()).count();
    match format {
        Format::Text => {
            for o in &outcomes {
                let what = match (&o.format, &o.verdict) {
                    (Some(f), Some(v)) => format!(" ({f}, {v})"),
                    _ => String::new(),
                };
                match &o.result {
                    Ok(()) => println!("{}: accepted{what}", o.file),
                    Err(reason) => println!("{}: rejected{what}: {reason}", o.file),
                }
            }
        }
        Format::Json => println!("{}", json_report(&outcomes)),
    }
    if rejected == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

fn help() {
    println!("ordeal-recheck {}", env!("CARGO_PKG_VERSION"));
    println!("re-check ordeal-cert/v1..v4 certificate bundles with the trusted");
    println!("ordeal-lrat checks — no solver in the dependency closure");
    println!();
    println!("{USAGE}");
    println!();
    println!("  --format text|json   per-bundle result as text (default) or one");
    println!("                       JSON object on stdout");
    println!("  -V, --version        print `ordeal-recheck <semver>` and exit");
    println!("  -h, --help           print this help and exit");
    println!();
    println!("The bundle's `format` (ordeal-cert/v1..v4) and `verdict` (unsat |");
    println!("sat) are detected; the content hashes are verified, then the full");
    println!("recheck of that format runs. Exit 0 iff every bundle is accepted,");
    println!("1 if any is rejected or malformed, 2 on a usage error.");
}

fn recheck_file(file: &str) -> Outcome {
    let mut out = Outcome {
        file: file.to_string(),
        format: None,
        verdict: None,
        result: Ok(()),
    };
    let json = match std::fs::read_to_string(file) {
        Ok(s) => s,
        Err(e) => {
            out.result = Err(format!("cannot read: {e}"));
            return out;
        }
    };
    let (format, verdict) = match bundle_header(&json) {
        Ok(h) => h,
        Err(e) => {
            out.result = Err(e.to_string());
            return out;
        }
    };
    out.result = recheck(&json, &format, &verdict);
    out.format = Some(format);
    out.verdict = Some(verdict);
    out
}

/// Decode with the reader the header names, then run its full recheck.
/// Every reader re-validates `format` and `verdict` itself.
fn recheck(json: &str, format: &str, verdict: &str) -> Result<(), String> {
    fn decode<T>(r: Result<T, BundleError>) -> Result<T, String> {
        r.map_err(|e| e.to_string())
    }
    fn checked<E: std::fmt::Display>(r: Result<(), E>) -> Result<(), String> {
        r.map_err(|e| format!("recheck failed: {e}"))
    }
    match (format, verdict) {
        ("ordeal-cert/v1", "unsat") => checked(decode(Certificate::from_cert_v1(json))?.recheck()),
        ("ordeal-cert/v1", "sat") => checked(decode(SatCertificate::from_cert_v1(json))?.recheck()),
        ("ordeal-cert/v2", "unsat") => {
            checked(decode(QueryCertificate::from_cert_v2(json))?.recheck())
        }
        ("ordeal-cert/v2", "sat") => {
            checked(decode(QuerySatCertificate::from_cert_v2(json))?.recheck())
        }
        ("ordeal-cert/v3", "unsat") => {
            checked(decode(TermCertificate::from_cert_v3(json))?.recheck())
        }
        ("ordeal-cert/v3", "sat") => {
            checked(decode(TermSatCertificate::from_cert_v3(json))?.recheck())
        }
        ("ordeal-cert/v4", "unsat") => {
            checked(decode(SliverCertificate::from_cert_v4(json))?.recheck())
        }
        ("ordeal-cert/v4", "sat") => {
            checked(decode(SliverSatCertificate::from_cert_v4(json))?.recheck())
        }
        ("ordeal-cert/v1" | "ordeal-cert/v2" | "ordeal-cert/v3" | "ordeal-cert/v4", v) => Err(
            format!("unexpected verdict: {v} (expected 'unsat' or 'sat')"),
        ),
        (f, _) => Err(format!("unsupported bundle format: {f}")),
    }
}

/// A JSON string literal (RFC 8259 escaping).
fn json_str(s: &str) -> String {
    let mut o = String::with_capacity(s.len() + 2);
    o.push('"');
    for c in s.chars() {
        match c {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            '\n' => o.push_str("\\n"),
            '\r' => o.push_str("\\r"),
            '\t' => o.push_str("\\t"),
            c if (c as u32) < 0x20 => o.push_str(&format!("\\u{:04x}", c as u32)),
            c => o.push(c),
        }
    }
    o.push('"');
    o
}

fn json_opt(s: Option<&String>) -> String {
    s.map_or_else(|| "null".to_string(), |s| json_str(s))
}

fn json_report(outcomes: &[Outcome]) -> String {
    let entries: Vec<String> = outcomes
        .iter()
        .map(|o| {
            let (status, reason) = match &o.result {
                Ok(()) => ("accepted", "null".to_string()),
                Err(r) => ("rejected", json_str(r)),
            };
            format!(
                "{{\"file\":{},\"format\":{},\"verdict\":{},\"status\":\"{status}\",\"reason\":{reason}}}",
                json_str(&o.file),
                json_opt(o.format.as_ref()),
                json_opt(o.verdict.as_ref()),
            )
        })
        .collect();
    let accepted = outcomes.iter().filter(|o| o.result.is_ok()).count();
    format!(
        "{{\"tool\":\"ordeal-recheck\",\"version\":\"{}\",\"accepted\":{accepted},\"rejected\":{},\"results\":[{}]}}",
        env!("CARGO_PKG_VERSION"),
        outcomes.len() - accepted,
        entries.join(",")
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn json_strings_are_escaped() {
        assert_eq!(json_str("a\"b\\c\nd\u{1}"), "\"a\\\"b\\\\c\\nd\\u0001\"");
    }

    #[test]
    fn unknown_formats_and_verdicts_are_rejected() {
        assert!(recheck("{}", "ordeal-cert/v9", "unsat").is_err());
        assert!(recheck("{}", "ordeal-cert/v1", "maybe").is_err());
    }
}
