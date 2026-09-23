//! Fuzz the SMT-LIB front end end to end (#139).
//!
//! Two properties, both load-bearing:
//! 1. No input may panic the parser or solver (the CLI feeds untrusted
//!    files/stdin straight in here).
//! 2. THE SOUNDNESS ORACLE: if a fuzz-mutated input ever produces an
//!    `Unsat`, its certificate must re-check through the trusted
//!    `ordeal-lrat` checker. A fuzz input that yields an unrecheckable
//!    Unsat would be a soundness bug worth more than any crash.
//!
//! Inputs are size-bounded by the harness flags (-max_len) and per-input
//! wall time by -timeout; random text rarely forms hard queries, and the
//! seed corpus (fuzz/seeds/smtlib) starts from real solvable scripts.
#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let Ok(script) = std::str::from_utf8(data) else {
        return;
    };
    // TR-038: BOTH verdict directions carry a trusted-crate oracle now —
    // a fuzz-found Unsat must re-check its LRAT certificate, and a
    // fuzz-found Sat must re-check its witness (full CNF assignment +
    // model-binding consistency). check_with_witness already runs both
    // gates internally and degrades to Unknown on rejection, so any
    // Sat/Unsat that reaches us was validated — we re-run the recheck
    // here anyway so a future regression in that internal gating is
    // itself fuzz-visible.
    use ordeal::cert_bundle::WitnessCheckResult;
    if let Ok((result, _declared)) = ordeal::smtlib::solve_str_with_witness(script) {
        match result {
            Some(WitnessCheckResult::Unsat(cert)) => {
                cert.recheck()
                    .expect("fuzz-found Unsat certificate must re-check (soundness oracle)");
            }
            Some(WitnessCheckResult::Sat(cert)) => {
                cert.recheck()
                    .expect("fuzz-found Sat witness must re-check (soundness oracle)");
            }
            Some(WitnessCheckResult::Unknown) | None => {}
        }
    }
});
