//! TR-072 verdict scan: every sliver corpus through `Solver::from_sliver`
//! and `check_with_deadline(10_000)`, one line per query streamed to the
//! file named by the first argument — `<corpus>\t<index>\t<verdict>\t<ms>`.
//! Built and run against v0.32.0 and against this tree, the two files
//! must agree verdict for verdict (the latency column is the overhead).
//!
//! Needs `--features oracle` for the seeded corpora (Z3 is linked but not
//! called).

use ordeal::sliver::{ArrayTerm, ExtBoolTerm, ExtBvTerm, ExtOp};
use ordeal::{BvTerm, CheckResult, Solver, Sort};
use std::io::Write;

fn v8(name: &str) -> ExtBvTerm {
    ExtBvTerm::Core(BvTerm::Var {
        name: name.into(),
        sort: Sort::new(8),
    })
}

fn v32(name: &str) -> ExtBvTerm {
    ExtBvTerm::Core(BvTerm::Var {
        name: name.into(),
        sort: Sort::new(32),
    })
}

fn c8(v: u128) -> ExtBvTerm {
    ExtBvTerm::Core(BvTerm::Const {
        value: v,
        sort: Sort::new(8),
    })
}

fn c32(v: u128) -> ExtBvTerm {
    ExtBvTerm::Core(BvTerm::Const {
        value: v,
        sort: Sort::new(32),
    })
}

fn add32(a: ExtBvTerm, b: ExtBvTerm) -> ExtBvTerm {
    ExtBvTerm::Op(Box::new(ExtOp::Add(a, b)))
}

fn sel(a: ArrayTerm, i: ExtBvTerm) -> ExtBvTerm {
    ExtBvTerm::Select {
        array: Box::new(a),
        index: Box::new(i),
    }
}

fn store(a: ArrayTerm, i: ExtBvTerm, v: ExtBvTerm) -> ArrayTerm {
    ArrayTerm::Store {
        array: Box::new(a),
        index: Box::new(i),
        value: Box::new(v),
    }
}

fn mem() -> ArrayTerm {
    ArrayTerm::Var { name: "mem".into() }
}

fn call(name: &str, args: Vec<ExtBvTerm>) -> ExtBvTerm {
    ExtBvTerm::PureCall {
        name: name.into(),
        args,
        sort: Sort::new(8),
    }
}

/// `n` i32 store/load pairs over a symbolic base: `4n` byte stores at
/// `b + k`, then the loads. Per `n`: every single byte read back (UNSAT
/// each), every byte against a fresh variable (SAT each), the whole
/// `Or` of the mismatches (UNSAT, `4n` reads of one array — the
/// quadratic congruence shape) and the whole `And` of the matches (SAT).
pub fn loom_shaped() -> Vec<(String, Vec<ExtBoolTerm>)> {
    let mut out = Vec::new();
    for n in 1..=6usize {
        let chain = || {
            (0..4 * n).fold(mem(), |acc, k| {
                store(acc, add32(v32("b"), c32(k as u128)), v8(&format!("v{k}")))
            })
        };
        let read = |k: usize| sel(chain(), add32(v32("b"), c32(k as u128)));
        for k in 0..4 * n {
            out.push((
                format!("loom{n}-byte{k}-unsat"),
                vec![ExtBoolTerm::Ne(read(k), v8(&format!("v{k}")))],
            ));
            out.push((
                format!("loom{n}-byte{k}-sat"),
                vec![ExtBoolTerm::Ne(read(k), v8("w"))],
            ));
        }
        let mut or_ne: Option<ExtBoolTerm> = None;
        let mut and_eq: Option<ExtBoolTerm> = None;
        for k in 0..4 * n {
            let ne = ExtBoolTerm::Ne(read(k), v8(&format!("v{k}")));
            let eq = ExtBoolTerm::Eq(read(k), v8(&format!("v{k}")));
            or_ne = Some(match or_ne {
                None => ne,
                Some(p) => ExtBoolTerm::Or(Box::new(p), Box::new(ne)),
            });
            and_eq = Some(match and_eq {
                None => eq,
                Some(p) => ExtBoolTerm::And(Box::new(p), Box::new(eq)),
            });
        }
        out.push((format!("loom{n}-all-unsat"), vec![or_ne.unwrap()]));
        out.push((format!("loom{n}-all-sat"), vec![and_eq.unwrap()]));
        // An aliasing question: two reads at different offsets.
        out.push((
            format!("loom{n}-alias-sat"),
            vec![ExtBoolTerm::Eq(read(0), read(1))],
        ));
    }
    out
}

/// The #231 shapes (a lifted operator above a select / pure_call) and the
/// bounded-entry queries of the solver tests.
pub fn trap_and_entry_shapes() -> Vec<(String, Vec<ExtBoolTerm>)> {
    let a = || ArrayTerm::Var { name: "a".into() };
    let r = || sel(a(), v32("i"));
    let ite = |c: ExtBoolTerm, t: ExtBvTerm, e: ExtBvTerm| {
        ExtBvTerm::Op(Box::new(ExtOp::Ite {
            cond: c,
            then_: t,
            else_: e,
        }))
    };
    let guarded = || ite(ExtBoolTerm::Ult(r(), c8(128)), r(), call("f", vec![r()]));
    let mut out = vec![
        (
            "trap-guard-sat".into(),
            vec![ExtBoolTerm::Eq(guarded(), c8(200))],
        ),
        (
            "trap-guard-unsat".into(),
            vec![
                ExtBoolTerm::Ult(r(), c8(128)),
                ExtBoolTerm::Ne(guarded(), r()),
            ],
        ),
        (
            "urem-over-select-unsat".into(),
            vec![ExtBoolTerm::Uge(
                ExtBvTerm::Op(Box::new(ExtOp::Urem(r(), c8(16)))),
                c8(16),
            )],
        ),
        (
            "sdiv-over-select-sat".into(),
            vec![ExtBoolTerm::Eq(
                ExtBvTerm::Op(Box::new(ExtOp::Sdiv(r(), c8(2)))),
                c8(3),
            )],
        ),
        (
            "neg-over-call-unsat".into(),
            vec![ExtBoolTerm::Ne(
                ExtBvTerm::Op(Box::new(ExtOp::Neg(ExtBvTerm::Op(Box::new(ExtOp::Neg(
                    call("g", vec![r(), v8("x")]),
                )))))),
                call("g", vec![r(), v8("x")]),
            )],
        ),
        (
            "entry-valid-unsat".into(),
            vec![ExtBoolTerm::Ne(
                sel(store(mem(), v32("i"), v8("v")), v32("i")),
                v8("v"),
            )],
        ),
        (
            "entry-free-sat".into(),
            vec![ExtBoolTerm::Ne(
                sel(store(mem(), v32("i"), v8("v")), v32("i")),
                v8("w"),
            )],
        ),
        (
            "uf-congruence-unsat".into(),
            vec![
                ExtBoolTerm::Eq(v8("x"), v8("y")),
                ExtBoolTerm::Ne(call("f", vec![v8("x")]), call("f", vec![v8("y")])),
            ],
        ),
        (
            "array-congruence-unsat".into(),
            vec![
                ExtBoolTerm::Ne(sel(a(), v32("i")), sel(a(), v32("j"))),
                ExtBoolTerm::Eq(v32("i"), v32("j")),
            ],
        ),
        (
            "concrete-chain-sat".into(),
            vec![ExtBoolTerm::Eq(
                sel(store(store(mem(), c32(1), c8(10)), c32(2), c8(20)), c32(2)),
                c8(20),
            )],
        ),
    ];
    // Concrete-vs-symbolic mixes.
    for k in 0..4u128 {
        out.push((
            format!("mix{k}-sat"),
            vec![ExtBoolTerm::Ne(
                sel(store(mem(), c32(k), v8("v")), v32("j")),
                v8("v"),
            )],
        ));
    }
    out
}

fn verdict(q: &[ExtBoolTerm]) -> (&'static str, u128) {
    let t0 = std::time::Instant::now();
    let v = match Solver::from_sliver(q) {
        Ok(s) => match s.check_with_deadline(10_000) {
            CheckResult::Sat(_) => "sat",
            CheckResult::Unsat(_) => "unsat",
            CheckResult::Unknown => "unknown",
        },
        Err(_) => "refused",
    };
    (v, t0.elapsed().as_millis())
}

fn main() {
    let path = std::env::args().nth(1).expect("output path");
    let mut out = std::io::BufWriter::new(std::fs::File::create(path).expect("create"));
    let corpora: Vec<(String, Vec<Vec<ExtBoolTerm>>)> = vec![
        (
            "seed-5EED".into(),
            ordeal::oracle::gen_sliver_corpus(0x5111_5EED_A55A_0001, 300),
        ),
        (
            "seed-0231-lifted".into(),
            ordeal::oracle::gen_sliver_lifted_corpus(0x5111_0231_11FE_0001, 300),
        ),
        (
            "seed-0DFF".into(),
            ordeal::oracle::gen_sliver_corpus(0x5111_0DFF_1CE0_0002, 250),
        ),
    ];
    for (name, corpus) in &corpora {
        for (i, q) in corpus.iter().enumerate() {
            let (v, ms) = verdict(q);
            writeln!(out, "{name}\t{i}\t{v}\t{ms}").unwrap();
            out.flush().unwrap();
        }
    }
    for (name, q) in loom_shaped().into_iter().chain(trap_and_entry_shapes()) {
        let (v, ms) = verdict(&q);
        writeln!(out, "{name}\t0\t{v}\t{ms}").unwrap();
        out.flush().unwrap();
    }
}
