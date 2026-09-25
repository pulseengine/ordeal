// rivet: verifies VER-048
//! TR-048 end-to-end demonstration: the SAT twin of `rivet_ingestion`.
//!
//! rivet ≥ 0.39.0 (rivet#991) consumes the TR-038 SAT witness: an
//! `ordeal-certificate` with `verdict: sat`, a `witness-sha256` and a recorded
//! `verification-result: pass` no longer draws `V-ordeal-cert-sat-is-self-checked`.
//! This example produces the ordeal side of that hand-off with a REAL solve:
//!
//! 1. find a model for a satisfiable QF_BV query → `check_with_witness`
//!    returns a [`SatCertificate`] the trusted crate already re-checked;
//! 2. serialize it as an `ordeal-cert/v1` bundle with the `witness` block;
//! 3. ingest it back the way rivet does: `from_cert_v1` (content hashes
//!    verified before parse returns) + `recheck()` (`check_sat` +
//!    `check_binding` in the trusted crate);
//! 4. tamper with the assignment (must be REJECTED at parse — hash mismatch)
//!    and with the advertised model (parses — the model is deliberately not
//!    hashed — but must be REJECTED by `recheck` as a binding mismatch);
//! 5. emit TWO rivet fixture projects from the same live bundle: one whose
//!    certificate carries the witness fields, and a negative control
//!    without them.
//!
//! Run:
//!
//! ```sh
//! cargo run -p ordeal --features cert-bundle --example rivet_witness_ingestion -- \
//!     target/rivet-witness "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
//! rivet --project target/rivet-witness/rivet-project validate            # no SAT warning
//! rivet --project target/rivet-witness/rivet-project-no-witness validate # warns
//! ```
//!
//! The first command exits 0 only if the round-trip PASSES and both tampered
//! bundles are REJECTED. With a released rivet ≥ 0.39.0, the witness fixture
//! must validate without `V-ordeal-cert-sat-is-self-checked` and the
//! no-witness control must raise it — that pair is the TR-048 event.

use std::process::ExitCode;

use ordeal::cert_bundle::{Attests, SatCertificate};
use ordeal::{BoolTerm, BvTerm, Solver, Sort, WitnessCheckResult};

fn main() -> ExitCode {
    let mut args = std::env::args().skip(1);
    let (Some(out_dir), Some(rechecked_at)) = (args.next(), args.next()) else {
        eprintln!("usage: rivet_witness_ingestion <OUT-DIR> <RFC3339-UTC-NOW>");
        eprintln!("       (pass \"$(date -u +%Y-%m-%dT%H:%M:%SZ)\" — the recheck timestamp");
        eprintln!("        being recorded must come from the clock)");
        return ExitCode::from(2);
    };

    // ── 1. A real satisfiable query: some byte x with x mod 5 == 3.
    let x = || BvTerm::Var {
        name: "x".into(),
        sort: Sort::new(8),
    };
    let c = |v| BvTerm::Const {
        value: v,
        sort: Sort::new(8),
    };
    let mut solver = Solver::new();
    solver.assert(BoolTerm::Eq(
        Box::new(BvTerm::Urem(Box::new(x()), Box::new(c(5)))),
        Box::new(c(3)),
    ));
    let cert = match solver.check_with_witness() {
        WitnessCheckResult::Sat(cert) => cert,
        other => {
            eprintln!("FAIL: expected Sat for a satisfiable query, got {other:?}");
            return ExitCode::from(1);
        }
    };

    // ── 2. Serialize as ordeal-cert/v1 with the witness block.
    let attests = Attests {
        kind: "satisfiability".into(),
        claim: "some 8-bit x satisfies x mod 5 == 3".into(),
        standards: vec![],
    };
    let bundle_json = cert.to_cert_v1(&attests);
    let pristine: serde_json::Value =
        serde_json::from_str(&bundle_json).expect("the bundle is JSON we just wrote");

    // ── 3. Ingest the way rivet does: hash-verified parse, then recheck.
    let ingested = match SatCertificate::from_cert_v1(&bundle_json) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("FAIL: pristine bundle rejected at ingestion: {e}");
            return ExitCode::from(1);
        }
    };
    if let Err(e) = ingested.recheck() {
        eprintln!("FAIL: pristine witness did not re-check: {e}");
        return ExitCode::from(1);
    }
    println!(
        "PASS ingest+recheck: {} clauses satisfied, {} model binding(s) consistent (ordeal-lrat)",
        ingested.cnf.len(),
        ingested.model.assignments.len()
    );

    // ── 4a. A flipped assignment bit must be rejected before any recheck.
    let mut tampered = pristine.clone();
    let bits = tampered["witness"]["assignment"]
        .as_str()
        .expect("assignment bitstring")
        .to_string();
    let flipped: String = bits
        .chars()
        .enumerate()
        .map(|(i, ch)| match (i, ch) {
            (0, '0') => '1',
            (0, _) => '0',
            (_, ch) => ch,
        })
        .collect();
    tampered["witness"]["assignment"] = serde_json::Value::String(flipped);
    match SatCertificate::from_cert_v1(&tampered.to_string()) {
        Err(e) => println!("PASS tampered assignment rejected at ingestion ({e})"),
        Ok(_) => {
            eprintln!("FAIL: a tampered assignment was accepted at ingestion");
            return ExitCode::from(1);
        }
    }

    // ── 4b. A lying model parses (the model block is not hashed) but must
    //        fail the semantic recheck against the witness.
    let mut lying = pristine.clone();
    let real = lying["model"]["assignments"][0][1]
        .as_u64()
        .expect("model value");
    lying["model"]["assignments"][0][1] = serde_json::Value::from(real ^ 1);
    match SatCertificate::from_cert_v1(&lying.to_string()).map(|b| b.recheck()) {
        Ok(Err(e)) => println!("PASS lying model rejected by recheck ({e})"),
        Ok(Ok(())) => {
            eprintln!("FAIL: a lying model passed the recheck");
            return ExitCode::from(1);
        }
        Err(e) => {
            eprintln!("FAIL: a lying model should parse and fail recheck, but parse failed: {e}");
            return ExitCode::from(1);
        }
    }

    // ── 5. Emit the two fixture projects with the REAL hashes.
    let s = |v: &serde_json::Value| v.as_str().expect("string field").to_string();
    let cnf_sha = s(&pristine["recheck"]["problem_sha256"]);
    let witness_sha = s(&pristine["witness"]["assignment_sha256"]);
    let bit_map_sha = s(&pristine["witness"]["bit_map_sha256"]);
    let version = s(&pristine["produced_by"]["version"]);

    let root = std::path::Path::new(&out_dir);
    let write = |path: std::path::PathBuf, content: String| -> bool {
        if let Some(dir) = path.parent()
            && let Err(e) = std::fs::create_dir_all(dir)
        {
            eprintln!("FAIL: cannot create {}: {e}", dir.display());
            return false;
        }
        if let Err(e) = std::fs::write(&path, content) {
            eprintln!("FAIL: cannot write {}: {e}", path.display());
            return false;
        }
        true
    };
    if !write(root.join("bundle.json"), bundle_json.clone()) {
        return ExitCode::from(1);
    }
    for (dir, with_witness) in [("rivet-project", true), ("rivet-project-no-witness", false)] {
        let project = root.join(dir);
        if !write(
            project.join("rivet.yaml"),
            "project:\n  name: ordeal-tr048-witness-ingestion\n  version: \"0.1.0\"\n  \
             schemas: [common, dev, ordeal-certificate]\nsources:\n  - path: artifacts\n    \
             format: generic-yaml\n"
                .into(),
        ) {
            return ExitCode::from(1);
        }
        let witness_fields = if with_witness {
            format!("      witness-sha256: {witness_sha}\n      bit-map-sha256: {bit_map_sha}\n")
        } else {
            String::new()
        };
        let certs_yaml = format!(
            r#"artifacts:
  - id: REQ-1
    type: requirement
    title: The residue class 3 mod 5 must be reachable by a byte
    status: implemented
    description: >
      Demonstrated by exhibiting a satisfying byte with a re-checkable
      witness, not by trusting the solver.
  - id: FEAT-1
    type: feature
    title: residue-class reachability check
    status: implemented
    links:
      - type: satisfies
        target: REQ-1
  - id: OC-1
    type: ordeal-certificate
    title: some 8-bit x has x mod 5 == 3 (SAT, witness re-checked)
    status: verified
    description: >
      Bundle produced by crates/ordeal/examples/rivet_witness_ingestion.rs
      from a live solve; the sha256s are the bundle's own recorded content
      hashes, and verification-result records an actual recheck() run.
    fields:
      format: ordeal-cert/v1
      verdict: sat
      produced-by: {{name: ordeal, version: {version}}}
      checked-by: {{name: ordeal-lrat, version: {version}}}
      attests-kind: satisfiability
      attests-claim: "some 8-bit x satisfies x mod 5 == 3"
      cnf-sha256: {cnf_sha}
{witness_fields}      recheck: {{command: 'cargo run -p ordeal --features cert-bundle --example rivet_witness_ingestion', expect-exit: 0}}
      verification-result: pass
      rechecked-at: {rechecked_at}
    links:
      - type: verifies
        target: REQ-1
"#
        );
        if !write(project.join("artifacts").join("certs.yaml"), certs_yaml) {
            return ExitCode::from(1);
        }
    }
    println!(
        "PASS fixtures emitted: {0}/rivet-project (witness) and {0}/rivet-project-no-witness (control)",
        root.display()
    );
    ExitCode::SUCCESS
}
