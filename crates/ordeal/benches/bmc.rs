// rivet: verifies VER-028
//! TR-031 — the BMC practical-`k` envelope (spar#350 consumer enablement).
//!
//! Certified end-to-end latency (blast → solve → LRAT → verified check) on
//! BMC-shaped queries vs unrolling depth `k`, in the two shapes spar's
//! spike gates on: event-port queue overflow and two-lock deadlock (both
//! the UNSAT "property holds within k" direction — that is the expensive,
//! certificate-carrying lane a CI gate would sit on).
//!
//! Two lanes when the `cadical` feature is on: the own pure-Rust core
//! (`check`) and the CaDiCaL accelerator (`check_with_cadical`) — both
//! checker-gated, so this compares engines, not trust models.
//!
//! Measured envelope (macOS arm64, 2026-07-29, release):
//!
//! | shape          | k    | own core | cadical |
//! |----------------|------|----------|---------|
//! | queue overflow | 16   |  15.4 ms |  15.9 ms |
//! | queue overflow | 32   |  86.3 ms |  82.5 ms |
//! | queue overflow | 64   |   522 ms |   404 ms |
//! | queue overflow | 128  |  2.53 s  |  2.00 s  |
//! | deadlock       | 24   |  16.5 ms |  33.4 ms |
//! | deadlock       | 48   |  34.3 ms |  99.2 ms |
//! | deadlock       | 96   |   205 ms |   274 ms |
//!
//! Reading: the certified 1 s line crosses at k ≈ 90 for the queue shape
//! (both engines) and is nowhere in sight at k = 96 for the deadlock
//! shape; 10 s is beyond k = 128 for every measured configuration. The
//! accelerator wins ~20 % on the big arithmetic-heavy unrollings and
//! LOSES on the cheap deadlock instances (fixed DIMACS/proof-file
//! overhead) — CaDiCaL is a lever for the far end of the envelope, not a
//! default. The w=8 queue counter makes the encoding meaningful only to
//! k ≤ 255.

use criterion::{Criterion, criterion_group, criterion_main};
use ordeal::bmc_corpus::{deadlock, queue_overflow};
use ordeal::{BoolTerm, CheckResult, Solver};

fn certified(assertions: &[BoolTerm]) -> CheckResult {
    let mut s = Solver::new();
    for a in assertions {
        s.assert(a.clone());
    }
    s.check()
}

#[cfg(feature = "cadical")]
fn certified_cadical(assertions: &[BoolTerm]) -> CheckResult {
    let mut s = Solver::new();
    for a in assertions {
        s.assert(a.clone());
    }
    s.check_with_cadical()
}

fn assert_unsat(r: &CheckResult) {
    assert!(
        matches!(r, CheckResult::Unsat(_)),
        "corpus instance must be UNSAT"
    );
}

fn bench_bmc(c: &mut Criterion) {
    // Small sample counts: the big instances are seconds each, and the
    // envelope needs the trend, not microsecond confidence intervals.
    let mut own = c.benchmark_group("bmc_certified_own");
    own.sample_size(10);
    for k in [16usize, 32, 64, 128] {
        let q = queue_overflow(k, k as u8);
        assert_unsat(&certified(&q));
        own.bench_function(format!("queue_overflow_k{k}"), |b| b.iter(|| certified(&q)));
    }
    for k in [24usize, 48, 96] {
        let d = deadlock(k, false);
        assert_unsat(&certified(&d));
        own.bench_function(format!("deadlock_k{k}"), |b| b.iter(|| certified(&d)));
    }
    own.finish();

    #[cfg(feature = "cadical")]
    {
        let mut acc = c.benchmark_group("bmc_certified_cadical");
        acc.sample_size(10);
        for k in [16usize, 32, 64, 128] {
            let q = queue_overflow(k, k as u8);
            assert_unsat(&certified_cadical(&q));
            acc.bench_function(format!("queue_overflow_k{k}"), |b| {
                b.iter(|| certified_cadical(&q))
            });
        }
        for k in [24usize, 48, 96] {
            let d = deadlock(k, false);
            assert_unsat(&certified_cadical(&d));
            acc.bench_function(format!("deadlock_k{k}"), |b| {
                b.iter(|| certified_cadical(&d))
            });
        }
        acc.finish();
    }
}

criterion_group!(benches, bench_bmc);
criterion_main!(benches);
