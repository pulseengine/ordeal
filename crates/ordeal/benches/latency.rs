//! Per-op integration-latency benchmarks (TR-009 item 3 / VER-010, issue #57).
//!
//! The honest performance claim these benches quantify: **amortized
//! per-operation integration latency** — an in-process `check()` including
//! blast, solve, LRAT emission, checker validation, and `recheck()`, with no
//! SMT-LIB text round-trip and no theory combination. NOT "out-solving Z3's
//! SAT engine": Z3 wins raw search; ordeal's proposition is the certificate
//! and the integration profile.
//!
//! The corpus is consumer-shaped, not synthetic: the #97/#101 div/rem VC
//! shapes (synth), a layout round-trip (spar/relay), a trap-preservation VC
//! (loom), a comparison chain, and a propositional feature-model conflict
//! (rivet). Each decides in the propagation-to-small-search class — the
//! region consumers live in after the #97/#101 fixes.
//!
//! Run:            cargo bench -p ordeal
//! With Z3 lane:   LIBRARY_PATH=/opt/homebrew/lib cargo bench -p ordeal --features oracle
//! (macOS/Homebrew; the Z3 comparison lane compiles only with `oracle`.)

use criterion::{Criterion, criterion_group, criterion_main};
use ordeal::{BoolTerm, BvTerm, CheckResult, Solver, Sort, lowering};

fn v(n: &str, w: u32) -> BvTerm {
    BvTerm::Var {
        name: n.into(),
        sort: Sort::new(w),
    }
}
fn c(val: u128, w: u32) -> BvTerm {
    BvTerm::Const {
        value: val,
        sort: Sort::new(w),
    }
}

/// The queries, each a named conjunction expected UNSAT (so every iteration
/// exercises the FULL certified path incl. LRAT validation + recheck).
fn corpus() -> Vec<(&'static str, Vec<BoolTerm>)> {
    let mut out = Vec::new();

    // #97 shape: srem value model vs multiplicative consumer model, w=32.
    {
        let (a, b) = (v("a", 32), v("b", 32));
        let ours = lowering::bvsrem(a.clone(), b.clone(), 32);
        let q = lowering::bvsdiv(a.clone(), b.clone(), 32);
        let theirs = BvTerm::Sub(Box::new(a), Box::new(BvTerm::Mul(Box::new(q), Box::new(b))));
        out.push((
            "srem_vc_32",
            vec![BoolTerm::Ne(Box::new(ours), Box::new(theirs))],
        ));
    }
    // #101 shape: native urem vs multiplicative model, w=32.
    {
        let (a, b) = (v("a", 32), v("b", 32));
        let ours = BvTerm::Urem(Box::new(a.clone()), Box::new(b.clone()));
        let q = BvTerm::Udiv(Box::new(a.clone()), Box::new(b.clone()));
        let theirs = BvTerm::Sub(Box::new(a), Box::new(BvTerm::Mul(Box::new(q), Box::new(b))));
        out.push((
            "urem_vc_32",
            vec![BoolTerm::Ne(Box::new(ours), Box::new(theirs))],
        ));
    }
    // Layout round-trip (spar/relay): from_le_bytes(to_le_bytes(x)) == x, w=32.
    {
        let x = v("x", 32);
        let bytes = ordeal::layout::to_le_bytes(&x, 32);
        let back = ordeal::layout::from_le_bytes(&bytes);
        out.push((
            "layout_roundtrip_32",
            vec![BoolTerm::Ne(Box::new(back), Box::new(x))],
        ));
    }
    // Trap-preservation VC (loom): identical div defines must be
    // trap-and-value equivalent, w=32.
    {
        use ordeal::trap::{DivOp, trap_div};
        let (a, b) = (v("a", 32), v("b", 32));
        let t1 = trap_div(DivOp::DivU, &a, &b, 32);
        let t2 = trap_div(DivOp::DivU, &a, &b, 32);
        // t1 <-> t2 is valid; assert its negation.
        let iff = BoolTerm::And(
            Box::new(BoolTerm::Or(
                Box::new(BoolTerm::Not(Box::new(t1.clone()))),
                Box::new(t2.clone()),
            )),
            Box::new(BoolTerm::Or(
                Box::new(BoolTerm::Not(Box::new(t2))),
                Box::new(t1),
            )),
        );
        out.push(("trap_vc_32", vec![BoolTerm::Not(Box::new(iff))]));
    }
    // Comparison chain (propagation class): a < b && b < c && c < a, w=64.
    {
        let (a, b, cc) = (v("a", 64), v("b", 64), v("c", 64));
        out.push((
            "ult_cycle_64",
            vec![
                BoolTerm::Ult(Box::new(a.clone()), Box::new(b.clone())),
                BoolTerm::Ult(Box::new(b), Box::new(cc.clone())),
                BoolTerm::Ult(Box::new(cc), Box::new(a)),
            ],
        ));
    }
    // Add/shift identity: (x << 1) == x + x, w=64.
    {
        let x = v("x", 64);
        let shl = BvTerm::Shl(Box::new(x.clone()), Box::new(c(1, 64)));
        let add = BvTerm::Add(Box::new(x.clone()), Box::new(x));
        out.push((
            "shl1_eq_add_64",
            vec![BoolTerm::Ne(Box::new(shl), Box::new(add))],
        ));
    }
    out
}

fn bench_ordeal(cr: &mut Criterion) {
    let mut g = cr.benchmark_group("ordeal_certified");
    for (name, q) in corpus() {
        // Sanity outside the timing loop: the query is UNSAT and re-checks.
        let mut s = Solver::new();
        for a in &q {
            s.assert(a.clone());
        }
        match s.check() {
            CheckResult::Unsat(cert) => cert.recheck().expect("bench query must re-check"),
            other => panic!("bench query {name} must be UNSAT, got {other:?}"),
        }
        g.bench_function(name, |bench| {
            bench.iter(|| {
                let mut s = Solver::new();
                for a in &q {
                    s.assert(a.clone());
                }
                match s.check() {
                    CheckResult::Unsat(cert) => {
                        cert.recheck().expect("recheck");
                    }
                    other => panic!("{name}: {other:?}"),
                }
            })
        });
    }
    g.finish();

    // The propositional lane (rivet feature-model conflict).
    let f = ordeal::cnf::CnfFormula {
        num_vars: 3,
        clauses: vec![vec![1], vec![-2, -3], vec![2], vec![3]],
    };
    cr.bench_function("check_cnf_feature_conflict", |bench| {
        bench.iter(|| match Solver::check_cnf(&f) {
            CheckResult::Unsat(cert) => {
                cert.recheck().expect("recheck");
            }
            other => panic!("{other:?}"),
        })
    });
}

/// The Z3 lane: the SAME queries through `oracle::z3_check` — a raw verdict,
/// no certificate, no recheck (that asymmetry is the point being measured:
/// ordeal's number INCLUDES producing and validating the proof).
#[cfg(feature = "oracle")]
fn bench_z3(cr: &mut Criterion) {
    use ordeal::oracle;
    let mut g = cr.benchmark_group("z3_unchecked");
    for (name, q) in corpus() {
        g.bench_function(name, |bench| {
            bench.iter(|| {
                let _ = oracle::z3_check(&q);
            })
        });
    }
    g.finish();
}

#[cfg(not(feature = "oracle"))]
fn bench_z3(_cr: &mut Criterion) {}

criterion_group!(benches, bench_ordeal, bench_z3);
criterion_main!(benches);
