// rivet: verifies VER-029
//! TR-030 end-to-end demonstration: the rivet-ingestion leg of the
//! `ordeal-cert/v1` evidence spine (rivet#693 Part 2 / ordeal#67).
//!
//! rivet ≥ 0.31.0 ships the `ordeal-certificate` artifact type, whose rule
//! `V-ordeal-cert-recheck-gates-verifies` makes "re-checks OK" — not a
//! claimed status — the thing that lets a certificate source `verifies`
//! links. This example produces the ordeal side of that hand-off with a
//! REAL solve (no synthetic hashes):
//!
//! 1. decide a QF_BV equivalence → checker-validated UNSAT [`Certificate`];
//! 2. serialize it as an `ordeal-cert/v1` bundle (`to_cert_v1`);
//! 3. ingest it back the way rivet does: `from_cert_v1` (content hashes
//!    verified before parse returns) + `recheck()` (the trusted checker
//!    re-runs — this is the recorded `verification-result: pass`);
//! 4. tamper with the proof and then the problem payload — both must be
//!    REJECTED at ingestion (`BundleError::HashMismatch`), before any
//!    recheck could even run;
//! 5. emit a ready-to-validate rivet fixture project whose
//!    `ordeal-certificate` artifact carries the real sha256s from step 2.
//!
//! Run (the timestamp is the recheck time being recorded — derive it from
//! the clock, never hand-author it):
//!
//! ```sh
//! cargo run -p ordeal --features cert-bundle --example rivet_ingestion -- \
//!     target/rivet-ingestion "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
//! rivet --project target/rivet-ingestion/rivet-project validate
//! ```
//!
//! The first command exits 0 only if the round-trip PASSES and both
//! tampered bundles are REJECTED. The second is the actual TR-030 event: a
//! released rivet ingesting the bundle's evidence and exiting 0. Dropping
//! the `verification-result: pass` line from the fixture flips `rivet
//! validate` to a failing exit naming `V-ordeal-cert-recheck-gates-verifies`
//! — the never-re-checked certificate cannot count as evidence.

use ordeal::cert_bundle::{Attests, BundleError};
use ordeal::{BvTerm, Certificate, CheckResult, Solver, Sort};
use std::process::ExitCode;

fn main() -> ExitCode {
    let mut args = std::env::args().skip(1);
    let (Some(out_dir), Some(rechecked_at)) = (args.next(), args.next()) else {
        eprintln!("usage: rivet_ingestion <OUT-DIR> <RFC3339-UTC-NOW>");
        eprintln!("       (pass \"$(date -u +%Y-%m-%dT%H:%M:%SZ)\" — the recheck timestamp");
        eprintln!("        being recorded must come from the clock)");
        return ExitCode::from(2);
    };

    // ── 1. A real query: strength-reduction equivalence, mul-by-2 vs shl-1.
    let x = || BvTerm::Var {
        name: "x".into(),
        sort: Sort::new(32),
    };
    let two = BvTerm::Const {
        value: 2,
        sort: Sort::new(32),
    };
    let one = BvTerm::Const {
        value: 1,
        sort: Sort::new(32),
    };
    let cert = match Solver::prove_equiv(
        BvTerm::Mul(Box::new(x()), Box::new(two)),
        BvTerm::Shl(Box::new(x()), Box::new(one)),
    ) {
        CheckResult::Unsat(cert) => cert,
        other => {
            eprintln!("FAIL: expected Unsat for a true equivalence, got {other:?}");
            return ExitCode::from(1);
        }
    };

    // ── 2. Serialize as ordeal-cert/v1.
    let attests = Attests {
        kind: "equivalence".into(),
        claim: "i32.mul(x, 2) == i32.shl(x, 1) for all x".into(),
        standards: vec!["DO-178C:6.4".into()],
    };
    let bundle_json = cert.to_cert_v1(&attests);

    // ── 3. Ingest the way rivet does: hash-verified parse, then recheck.
    let bundle = match Certificate::from_cert_v1(&bundle_json) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("FAIL: pristine bundle rejected at ingestion: {e}");
            return ExitCode::from(1);
        }
    };
    if let Err(e) = bundle.recheck() {
        eprintln!("FAIL: trusted checker rejected the pristine bundle: {e}");
        return ExitCode::from(1);
    }
    println!(
        "PASS ingest+recheck: {} clauses re-checked by ordeal-lrat",
        bundle.certificate.cnf.len()
    );

    // ── 4. Tampered bundles must be rejected BEFORE any recheck.
    // The proof body and the clause list are the two trusted payloads; alter
    // each one the way an attacker editing the JSON would (payload changed,
    // recorded hashes left as-is) and demand rejection at ingestion.
    let pristine: serde_json::Value =
        serde_json::from_str(&bundle_json).expect("own bundle re-parses");
    let mut with_forged_proof = pristine.clone();
    let body = with_forged_proof["proof"]["body"]
        .as_str()
        .expect("proof body")
        .to_string();
    with_forged_proof["proof"]["body"] = serde_json::Value::String(format!("1 {body}"));
    match Certificate::from_cert_v1(&with_forged_proof.to_string()) {
        Err(BundleError::HashMismatch("proof")) => {
            println!("PASS tampered proof rejected at ingestion (hash mismatch)");
        }
        other => {
            eprintln!("FAIL: tampered proof not rejected as proof-hash mismatch: {other:?}");
            return ExitCode::from(1);
        }
    }
    let mut with_forged_problem = pristine.clone();
    let first_lit = with_forged_problem["problem"]["clauses"][0][0]
        .as_i64()
        .expect("first literal");
    with_forged_problem["problem"]["clauses"][0][0] = serde_json::Value::from(-first_lit);
    match Certificate::from_cert_v1(&with_forged_problem.to_string()) {
        Err(BundleError::HashMismatch("problem")) => {
            println!("PASS tampered problem rejected at ingestion (hash mismatch)");
        }
        other => {
            eprintln!("FAIL: tampered problem not rejected as problem-hash mismatch: {other:?}");
            return ExitCode::from(1);
        }
    }

    // ── 5. Emit the rivet fixture project with the REAL hashes.
    // Pull the recorded sha256s and version straight from the bundle JSON so
    // the fixture can never drift from what step 2 actually produced.
    let problem_sha = pristine["recheck"]["problem_sha256"]
        .as_str()
        .expect("problem sha");
    let proof_sha = pristine["recheck"]["proof_sha256"]
        .as_str()
        .expect("proof sha");
    let version = pristine["produced_by"]["version"]
        .as_str()
        .expect("version");

    let project = std::path::Path::new(&out_dir).join("rivet-project");
    let artifacts = project.join("artifacts");
    if let Err(e) = std::fs::create_dir_all(&artifacts) {
        eprintln!("FAIL: cannot create {}: {e}", artifacts.display());
        return ExitCode::from(1);
    }
    let write = |path: std::path::PathBuf, content: String| -> bool {
        if let Err(e) = std::fs::write(&path, content) {
            eprintln!("FAIL: cannot write {}: {e}", path.display());
            return false;
        }
        true
    };
    if !write(
        std::path::Path::new(&out_dir).join("bundle.json"),
        bundle_json.clone(),
    ) {
        return ExitCode::from(1);
    }
    if !write(
        project.join("rivet.yaml"),
        "project:\n  name: ordeal-tr030-ingestion\n  version: \"0.1.0\"\n  \
         schemas: [common, dev, ordeal-certificate]\nsources:\n  - path: artifacts\n    \
         format: generic-yaml\n"
            .into(),
    ) {
        return ExitCode::from(1);
    }
    let certs_yaml = format!(
        r#"artifacts:
  - id: REQ-1
    type: requirement
    title: The strength-reduction rewrite must be proven equivalent
    status: implemented
    description: >
      i32.mul(x, 2) may be lowered to i32.shl(x, 1) only with a
      machine-re-checkable equivalence proof.
  - id: FEAT-1
    type: feature
    title: mul-by-power-of-two strength reduction
    status: implemented
    links:
      - type: satisfies
        target: REQ-1
  - id: OC-1
    type: ordeal-certificate
    title: mul(x,2) == shl(x,1) proven equivalent (UNSAT, checker-validated)
    status: verified
    description: >
      Bundle produced by crates/ordeal/examples/rivet_ingestion.rs from a
      live solve; sha256s below are the bundle's own recorded content
      hashes, and verification-result records an actual recheck() run.
    fields:
      format: ordeal-cert/v1
      verdict: unsat
      produced-by: {{name: ordeal, version: {version}}}
      checked-by: {{name: ordeal-lrat, version: {version}}}
      attests-kind: equivalence
      attests-claim: "i32.mul(x, 2) == i32.shl(x, 1) for all x"
      attests-standards: ["DO-178C:6.4"]
      cnf-sha256: {problem_sha}
      proof-sha256: {proof_sha}
      recheck: {{command: 'cargo run -p ordeal --features cert-bundle --example rivet_ingestion', expect-exit: 0}}
      verification-result: pass
      rechecked-at: {rechecked_at}
    links:
      - type: attests-transform
        target: FEAT-1
      - type: verifies
        target: REQ-1
"#
    );
    if !write(artifacts.join("certs.yaml"), certs_yaml) {
        return ExitCode::from(1);
    }

    println!(
        "PASS fixture emitted: {} (validate with: rivet --project {} validate)",
        project.display(),
        project.display()
    );
    ExitCode::SUCCESS
}
