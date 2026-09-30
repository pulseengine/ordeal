// rivet: verifies VER-058
//! Emit an `ordeal-cert/v1` bundle for an UNSAT SMT-LIB2 script, and print
//! the hashes a rivet `ordeal-certificate` artifact records (#191:
//! ordeal records its own certificates as evidence, dogfooding the type it
//! asks consumers to use).
//!
//! ```sh
//! cargo run -p ordeal --features cert-bundle --example cert_bundle_smt2 -- \
//!     <query.smt2> <out-bundle.json> <attests-kind> <attests-claim>
//! ```
//!
//! Exits 0 only if the script is decided UNSAT with a checker-validated
//! certificate, the written bundle re-parses (content hashes verified), and
//! the trusted checker re-checks it. Prints `cnf-sha256` and `proof-sha256`
//! for the artifact.

use ordeal::cert_bundle::Attests;
use ordeal::{Certificate, CheckResult};
use std::process::ExitCode;

fn main() -> ExitCode {
    let a: Vec<String> = std::env::args().skip(1).collect();
    let [query, out, kind, claim] = a.as_slice() else {
        eprintln!(
            "usage: cert_bundle_smt2 <query.smt2> <out-bundle.json> <attests-kind> <attests-claim>"
        );
        return ExitCode::from(2);
    };
    let script = match std::fs::read_to_string(query) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("FAIL: cannot read {query}: {e}");
            return ExitCode::from(2);
        }
    };
    let cert = match ordeal::smtlib::solve_str(&script) {
        Ok(o) => match o.result {
            Some(CheckResult::Unsat(cert)) => cert,
            other => {
                eprintln!("FAIL: expected a certified unsat, got {other:?}");
                return ExitCode::from(1);
            }
        },
        Err(e) => {
            eprintln!("FAIL: {e:?}");
            return ExitCode::from(1);
        }
    };
    let bundle = cert.to_cert_v1(&Attests {
        kind: kind.clone(),
        claim: claim.clone(),
        standards: vec![],
    });
    if let Err(e) = std::fs::write(out, &bundle) {
        eprintln!("FAIL: cannot write {out}: {e}");
        return ExitCode::from(1);
    }
    let back = match Certificate::from_cert_v1(&bundle) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("FAIL: bundle rejected at ingestion: {e}");
            return ExitCode::from(1);
        }
    };
    if let Err(e) = back.recheck() {
        eprintln!("FAIL: trusted checker rejected the bundle: {e}");
        return ExitCode::from(1);
    }
    let v: serde_json::Value = serde_json::from_str(&bundle).expect("own bundle re-parses");
    println!(
        "PASS {} clauses re-checked by ordeal-lrat",
        back.certificate.cnf.len()
    );
    println!(
        "cnf-sha256: {}",
        v["recheck"]["problem_sha256"].as_str().unwrap_or("?")
    );
    println!(
        "proof-sha256: {}",
        v["recheck"]["proof_sha256"].as_str().unwrap_or("?")
    );
    println!(
        "produced-by: {}",
        v["produced_by"]["version"].as_str().unwrap_or("?")
    );
    ExitCode::SUCCESS
}
