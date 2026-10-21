//! TR-073 verdict scan, core path: every core corpus through
//! `Solver::assert` and `check_with_deadline(10_000)`, one line per query
//! streamed to the file named by the first argument —
//! `<corpus>\t<index>\t<verdict>\t<ms>`. Built and run against v0.33.0
//! and against this tree, the two files must agree verdict for verdict;
//! the only rows allowed to move are the `f1-*` shapes (#262: a constant
//! whose raw value exceeds its width), which v0.33.0 may have left
//! `unknown`.
//!
//! Needs `--features oracle` for the seeded corpora (Z3 is linked but not
//! called).

use ordeal::{BoolTerm, BvTerm, CheckResult, Solver, Sort};
use std::io::Write;

fn v(name: &str, w: u32) -> BvTerm {
    BvTerm::Var {
        name: name.into(),
        sort: Sort::new(w),
    }
}

fn c(value: u128, w: u32) -> BvTerm {
    BvTerm::Const {
        value,
        sort: Sort::new(w),
    }
}

fn b(t: BvTerm) -> Box<BvTerm> {
    Box::new(t)
}

/// The #262 shapes on the core path: a constant whose raw value exceeds
/// its width, compared, interned next to its masked twin, and under an
/// operator.
pub fn f1_shapes() -> Vec<(String, Vec<BoolTerm>)> {
    vec![
        (
            "f1-eq-sat".into(),
            vec![BoolTerm::Eq(b(v("x", 8)), b(c(0x1FF, 8)))],
        ),
        (
            "f1-eq-ne-unsat".into(),
            vec![
                BoolTerm::Eq(b(v("x", 8)), b(c(0x1FF, 8))),
                BoolTerm::Ne(b(v("x", 8)), b(c(0xFF, 8))),
            ],
        ),
        (
            "f1-two-raw-unsat".into(),
            vec![BoolTerm::Ne(b(c(0x1FF, 8)), b(c(0xFF, 8)))],
        ),
        (
            "f1-add-sat".into(),
            vec![BoolTerm::Eq(
                b(BvTerm::Add(b(v("x", 8)), b(c(0x100, 8)))),
                b(c(0, 8)),
            )],
        ),
    ]
}

fn verdict(q: &[BoolTerm]) -> (&'static str, u128) {
    let t0 = std::time::Instant::now();
    let mut s = Solver::new();
    for a in q {
        s.assert(a.clone());
    }
    let v = match s.check_with_deadline(10_000) {
        CheckResult::Sat(_) => "sat",
        CheckResult::Unsat(_) => "unsat",
        CheckResult::Unknown => "unknown",
    };
    (v, t0.elapsed().as_millis())
}

fn main() {
    let path = std::env::args().nth(1).expect("output path");
    let mut out = std::io::BufWriter::new(std::fs::File::create(path).expect("create"));
    let corpora: Vec<(String, Vec<Vec<BoolTerm>>)> = vec![
        ("seed-0192".into(), ordeal::oracle::gen_corpus(0x192, 200)),
        (
            "seed-C0FFEE".into(),
            ordeal::oracle::gen_corpus(0xC0FFEE, 1000),
        ),
    ];
    for (name, corpus) in &corpora {
        for (i, q) in corpus.iter().enumerate() {
            let (v, ms) = verdict(q);
            writeln!(out, "{name}\t{i}\t{v}\t{ms}").unwrap();
            out.flush().unwrap();
        }
    }
    let mut named: Vec<(String, Vec<BoolTerm>)> = Vec::new();
    for k in [2usize, 4, 8, 16] {
        named.push((
            format!("queue_overflow_{k}"),
            ordeal::bmc_corpus::queue_overflow(k, 3),
        ));
        named.push((
            format!("deadlock_{k}"),
            ordeal::bmc_corpus::deadlock(k, false),
        ));
        named.push((
            format!("deadlock_inv_{k}"),
            ordeal::bmc_corpus::deadlock(k, true),
        ));
    }
    for (name, q) in named.into_iter().chain(f1_shapes()) {
        let (v, ms) = verdict(&q);
        writeln!(out, "{name}\t0\t{v}\t{ms}").unwrap();
        out.flush().unwrap();
    }
}
