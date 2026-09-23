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
    if let Ok(outcome) = ordeal::smtlib::solve_str(script) {
        if let Some(ordeal::CheckResult::Unsat(cert)) = outcome.result {
            cert.recheck()
                .expect("fuzz-found Unsat certificate must re-check (soundness oracle)");
        }
    }
});
