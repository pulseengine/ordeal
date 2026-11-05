//! The TR-075 bundle corpus: `ordeal-cert/v1`..`v4` bundles, UNSAT and
//! SAT, produced by the REAL solver through `ordeal`'s public API (the
//! same `to_cert_v*` emitters downstream uses). Shared by the
//! `recheck_cli` integration test and the `emit_corpus` example, which
//! writes them to disk (the byte-identity check across the ordeal-cert
//! extraction ran that example on both sides; on the pre-extraction tree
//! the one `ordeal_cert::cert_bundle` import reads `ordeal::cert_bundle`).
//!
//! `Attests` / `model_to_cert_v1` come from `ordeal_cert` (whose `json`
//! feature this crate enables), NOT from `ordeal`'s `cert-bundle` feature:
//! a dev-dependency on `ordeal` with `cert-bundle` would unify that
//! feature into every `cargo test --workspace` build and silently turn
//! ordeal's own default-feature test run into a cert-bundle one.

#![allow(dead_code)]

use ordeal::query::{QueryCheckResult, SliverCheckResult, TermCheckResult};
use ordeal::sliver::{ArrayTerm, ExtBoolTerm, ExtBvTerm, ExtOp};
use ordeal::witness::WitnessCheckResult;
use ordeal::{BoolTerm, BvTerm, CheckResult, Solver, Sort};
use ordeal_cert::cert_bundle::{Attests, model_to_cert_v1};

fn b<T>(t: T) -> Box<T> {
    Box::new(t)
}

fn var(name: &str, w: u32) -> BvTerm {
    BvTerm::Var {
        name: name.into(),
        sort: Sort::new(w),
    }
}

fn konst(value: u128, w: u32) -> BvTerm {
    BvTerm::Const {
        value,
        sort: Sort::new(w),
    }
}

fn attests() -> Attests {
    Attests {
        kind: "translation_validation".into(),
        claim: "ordeal-recheck corpus (TR-075)".into(),
        standards: vec!["ISO-26262:8-11".into()],
    }
}

/// `x * 2 ≠ x << 1` at width `w` — UNSAT (strength reduction).
fn unsat_query(w: u32) -> Solver {
    let mut s = Solver::new();
    s.assert(BoolTerm::Ne(
        b(BvTerm::Mul(b(var("x", w)), b(konst(2, w)))),
        b(BvTerm::Shl(b(var("x", w)), b(konst(1, w)))),
    ));
    s
}

/// `x + 2*3 > x + 6 ∧ a*b ≠ b*a` at width `w` — UNSAT, with a fold, a
/// mirror, a swap and hash-consing for the term map to carry.
fn unsat_term_query(w: u32) -> Solver {
    let mut s = Solver::new();
    s.assert(BoolTerm::Ugt(
        b(BvTerm::Add(
            b(var("x", w)),
            b(BvTerm::Mul(b(konst(2, w)), b(konst(3, w)))),
        )),
        b(BvTerm::Add(b(var("x", w)), b(konst(6, w)))),
    ));
    s.assert(BoolTerm::Ne(
        b(BvTerm::Mul(b(var("a", w)), b(var("b", w)))),
        b(BvTerm::Mul(b(var("b", w)), b(var("a", w)))),
    ));
    s
}

/// `a + b = 9 ∧ b > a ∧ a * 2 = b` at width `w` — SAT (`a = 3, b = 6`).
fn sat_query(w: u32) -> Solver {
    let mut s = Solver::new();
    s.assert(BoolTerm::Eq(
        b(BvTerm::Add(b(var("a", w)), b(var("b", w)))),
        b(konst(9, w)),
    ));
    s.assert(BoolTerm::Ugt(b(var("b", w)), b(var("a", w))));
    s.assert(BoolTerm::Eq(
        b(BvTerm::Mul(b(var("a", w)), b(konst(2, w)))),
        b(var("b", w)),
    ));
    s
}

fn ev(name: &str, w: u32) -> ExtBvTerm {
    ExtBvTerm::Core(var(name, w))
}

fn ec(v: u128, w: u32) -> ExtBvTerm {
    ExtBvTerm::Core(konst(v, w))
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

/// loom's shape: `mem[b+1 := v1][b+0 := v0][b+0] ≠ v0` — UNSAT.
fn unsat_sliver() -> Vec<ExtBoolTerm> {
    let add = |a, b| ExtBvTerm::Op(Box::new(ExtOp::Add(a, b)));
    let m = store(
        store(mem(), add(ev("b", 32), ec(1, 32)), ev("v1", 8)),
        add(ev("b", 32), ec(0, 32)),
        ev("v0", 8),
    );
    vec![ExtBoolTerm::Ne(
        sel(m, add(ev("b", 32), ec(0, 32))),
        ev("v0", 8),
    )]
}

/// `mem[i] ≠ mem[j] ∧ f(mem[i]) = 3` — SAT, two reads and a call.
fn sat_sliver() -> Vec<ExtBoolTerm> {
    vec![
        ExtBoolTerm::Ne(sel(mem(), ev("i", 32)), sel(mem(), ev("j", 32))),
        ExtBoolTerm::Eq(
            ExtBvTerm::PureCall {
                name: "f".into(),
                args: vec![sel(mem(), ev("i", 32))],
                sort: Sort::new(8),
            },
            ec(3, 8),
        ),
    ]
}

/// One corpus entry: a file name, the bundle JSON, and whether a sound
/// re-checker must accept it.
pub struct Entry {
    pub name: String,
    pub json: String,
    pub recheckable: bool,
}

fn entry(name: String, json: String) -> Entry {
    Entry {
        name,
        json,
        recheckable: true,
    }
}

/// The whole corpus. Odd widths (3, 5, 12) are in on purpose — the #182
/// lesson: encoding bugs hide at widths that are not a power of two.
pub fn corpus() -> Vec<Entry> {
    let a = attests();
    let mut out = Vec::new();
    for w in [3u32, 5, 8, 12] {
        // v1 UNSAT: the CNF + LRAT pair.
        match unsat_query(w).check() {
            CheckResult::Unsat(c) => {
                out.push(entry(format!("v1-unsat-w{w}.json"), c.to_cert_v1(&a)));
            }
            other => panic!("v1 unsat w{w}: {other:?}"),
        }
        // v2 UNSAT: plus the lowered query.
        match unsat_query(w).check_with_query() {
            QueryCheckResult::Unsat(c) => {
                out.push(entry(format!("v2-unsat-w{w}.json"), c.to_cert_v2(&a)));
            }
            other => panic!("v2 unsat w{w}: {other:?}"),
        }
        // v3 UNSAT: plus the term as asked.
        match unsat_term_query(w).check_with_term() {
            TermCheckResult::Unsat(c) => {
                out.push(entry(format!("v3-unsat-w{w}.json"), c.to_cert_v3(&a)));
            }
            other => panic!("v3 unsat w{w}: {other:?}"),
        }
    }
    for w in [5u32, 8, 12] {
        match sat_query(w).check_with_witness() {
            WitnessCheckResult::Sat(c) => {
                out.push(entry(format!("v1-sat-w{w}.json"), c.to_cert_v1(&a)));
                // The model-only SAT shape: emitted for the byte-identity
                // check, but it carries no witness, so a re-checker must
                // NOT accept it.
                out.push(Entry {
                    name: format!("v1-model-w{w}.json"),
                    json: model_to_cert_v1(&c.model, &a),
                    recheckable: false,
                });
            }
            other => panic!("v1 sat w{w}: {other:?}"),
        }
        match sat_query(w).check_with_query() {
            QueryCheckResult::Sat(c) => {
                out.push(entry(format!("v2-sat-w{w}.json"), c.to_cert_v2(&a)));
            }
            other => panic!("v2 sat w{w}: {other:?}"),
        }
        match sat_query(w).check_with_term() {
            TermCheckResult::Sat(c) => {
                out.push(entry(format!("v3-sat-w{w}.json"), c.to_cert_v3(&a)));
            }
            other => panic!("v3 sat w{w}: {other:?}"),
        }
    }
    match Solver::from_sliver(&unsat_sliver())
        .expect("in the sliver")
        .check_sliver_with_term()
    {
        SliverCheckResult::Unsat(c) => out.push(entry("v4-unsat.json".into(), c.to_cert_v4(&a))),
        other => panic!("v4 unsat: {other:?}"),
    }
    match Solver::from_sliver(&sat_sliver())
        .expect("in the sliver")
        .check_sliver_with_term()
    {
        SliverCheckResult::Sat(c) => out.push(entry("v4-sat.json".into(), c.to_cert_v4(&a))),
        other => panic!("v4 sat: {other:?}"),
    }
    out
}
