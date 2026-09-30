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
//! 3. THE SEMANTIC ORACLE (#187): properties 1-2 only check ordeal's
//!    certificate against ordeal's OWN CNF, so an encoding bug (#182)
//!    passes them. For an `Unsat` whose declared variables total at most
//!    `BRUTE_FORCE_BITS` bits, every assignment is evaluated through the
//!    concrete evaluator, which shares no code with the bit-blaster. Any
//!    assignment satisfying every assertion is a certified wrong answer.
//!
//! Inputs are size-bounded by the harness flags (-max_len) and per-input
//! wall time by -timeout; random text rarely forms hard queries, and the
//! seed corpus (fuzz/seeds/smtlib) starts from real solvable scripts.
#![no_main]

use libfuzzer_sys::fuzz_target;

/// Largest total declared width brute-forced on an `Unsat` (2^16 evaluations
/// at most; #182's width-3 shift would have been caught at 3 bits).
const BRUTE_FORCE_BITS: u32 = 16;

/// Panics if some assignment of `declared` satisfies every assertion.
fn assert_no_model(script: &str) {
    let Ok((Some(assertions), declared)) = ordeal::smtlib::assertions_at_check_sat(script) else {
        return;
    };
    let total: u32 = declared.iter().map(|(_, w)| *w).sum();
    if total > BRUTE_FORCE_BITS {
        return;
    }
    for bits in 0u64..(1u64 << total) {
        let mut env = ordeal::eval::Env::new();
        let mut shift = 0;
        for (name, w) in &declared {
            env.insert(
                name.clone(),
                u128::from((bits >> shift) & ((1u64 << w) - 1)),
            );
            shift += w;
        }
        let all_true = assertions
            .iter()
            .all(|a| ordeal::eval::eval_bool(a, &env) == Ok(true));
        assert!(
            !all_true,
            "certified Unsat, but the evaluator satisfies every assertion with {env:?} (semantic oracle, #187)"
        );
    }
}

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
                assert_no_model(script);
            }
            Some(WitnessCheckResult::Sat(cert)) => {
                cert.recheck()
                    .expect("fuzz-found Sat witness must re-check (soundness oracle)");
            }
            Some(WitnessCheckResult::Unknown) | None => {}
        }
    }
});
