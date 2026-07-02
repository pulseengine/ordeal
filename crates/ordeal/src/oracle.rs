//! The differential oracle: Z3 as a cross-check, not the production engine.
//!
//! This module is compiled **only** when the `oracle` feature is enabled (and
//! never on wasm targets). When the feature is off it is entirely absent, so
//! the default build has zero external dependencies and always compiles.
//!
//! # Role
//!
//! `ordeal`'s production engine is an untrusted solver plus a formally-verified
//! LRAT checker (see `ARCHITECTURE.md`). Z3 is deliberately **demoted** to two
//! non-production roles:
//!
//! 1. A **differential oracle** — during development and CI, every query can be
//!    sent to Z3 as well, and any disagreement between `ordeal` and Z3 is a bug
//!    to investigate. This is a safety net, not part of the soundness argument.
//! 2. A **benchmark rival** — we compare integration latency against Z3. The
//!    honest win is amortized *per-op* latency (in-process, no SMT-LIB parse,
//!    no theory combination), NOT out-solving Z3's SAT engine.
//!
//! Note that the oracle is NOT part of the trust story: soundness rests on the
//! verified checker alone. A later roadmap phase (P4) drops Z3 from the
//! soundness argument entirely.
//!
//! # Pieces
//!
//! - [`to_z3`] / [`bv_to_z3`] — translate the closed loom #246 fragment into
//!   Z3 ASTs, preserving SMT-LIB semantics exactly (`bvudiv` by zero,
//!   out-of-range shifts, `bvrotr` by a variable amount mod width, ...). The
//!   translation is itself cross-checked against [`crate::eval`] in tests.
//! - [`z3_check`] — run Z3 on a conjunction of assertions; on SAT, extract a
//!   model binding every free variable of the query.
//! - [`gen_corpus`] — a seeded, reproducible generator of well-sorted random
//!   queries covering every operation in the fragment.
//! - [`differential_check`] — the entry point the engine wires up: run both
//!   the engine and Z3 and report any [`Disagreement`].

#![cfg(not(target_family = "wasm"))]

use crate::eval::{self, Env};
use crate::sliver::{self, ArrayTerm, ExtBoolTerm, ExtBvTerm, ExtOp};
use crate::term::{BoolTerm, BvTerm, Sort};
use std::collections::BTreeMap;
use z3::ast::{Array, Ast, BV, Bool};
use z3::{FuncDecl, Params, SatResult, Solver, Sort as Z3Sort};

// ─── Translation: closed fragment → Z3 ──────────────────────────────────────

fn mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

/// Build a Z3 bitvector constant of the given width, masking the value the
/// same way [`crate::eval`] does.
fn bv_const(value: u128, width: u32) -> BV {
    let masked = value & mask(width);
    if width <= 64 {
        BV::from_u64(masked as u64, width)
    } else {
        // Wide intermediates (e.g. a 64+64 concat operand) exceed u64; go
        // through Z3's decimal numeral parser instead.
        BV::from_str(width, &masked.to_string()).expect("decimal bitvector numeral")
    }
}

/// Translate a [`BvTerm`] of the closed fragment into a Z3 bitvector AST.
///
/// Every operation maps to the Z3 primitive with the exact SMT-LIB QF_BV
/// semantics the evaluator implements: `bvudiv` by zero is all-ones,
/// `bvshl`/`bvlshr`/`bvashr` saturate for out-of-range amounts, and `Rotr`
/// (a rotate by a *variable* bitvector amount) maps to Z3's
/// `ext_rotate_right`, which rotates by the amount modulo the width.
///
/// Z3 objects are created in the crate's implicit thread-local
/// [`z3::Context`], so the resulting AST must stay on the creating thread.
pub fn bv_to_z3(term: &BvTerm) -> BV {
    match term {
        BvTerm::Const { value, sort } => bv_const(*value, sort.width),
        BvTerm::Var { name, sort } => BV::new_const(name.as_str(), sort.width),
        BvTerm::Add(a, b) => bv_to_z3(a).bvadd(bv_to_z3(b)),
        BvTerm::Sub(a, b) => bv_to_z3(a).bvsub(bv_to_z3(b)),
        BvTerm::Mul(a, b) => bv_to_z3(a).bvmul(bv_to_z3(b)),
        // SMT-LIB bvudiv: division by zero yields all-ones — Z3's bvudiv
        // already has exactly this semantics.
        BvTerm::Udiv(a, b) => bv_to_z3(a).bvudiv(bv_to_z3(b)),
        BvTerm::And(a, b) => bv_to_z3(a).bvand(bv_to_z3(b)),
        BvTerm::Or(a, b) => bv_to_z3(a).bvor(bv_to_z3(b)),
        BvTerm::Xor(a, b) => bv_to_z3(a).bvxor(bv_to_z3(b)),
        // SMT-LIB shifts take the amount as a bitvector and saturate when it
        // is >= width — again Z3's primitives match directly.
        BvTerm::Shl(a, b) => bv_to_z3(a).bvshl(bv_to_z3(b)),
        BvTerm::Lshr(a, b) => bv_to_z3(a).bvlshr(bv_to_z3(b)),
        BvTerm::Ashr(a, b) => bv_to_z3(a).bvashr(bv_to_z3(b)),
        // `Rotr` rotates by a VARIABLE amount, so it maps to Z3's
        // ext_rotate_right (rotate by amount mod width), NOT the fixed-amount
        // SMT-LIB `rotate_right` indexed operator.
        BvTerm::Rotr(a, b) => bv_to_z3(a).bvrotr(bv_to_z3(b)),
        BvTerm::Extract { hi, lo, arg } => bv_to_z3(arg).extract(*hi, *lo),
        BvTerm::Concat(a, b) => bv_to_z3(a).concat(bv_to_z3(b)),
        BvTerm::ZeroExt { by, arg } => bv_to_z3(arg).zero_ext(*by),
        BvTerm::SignExt { by, arg } => bv_to_z3(arg).sign_ext(*by),
    }
}

/// Translate a [`BoolTerm`] of the closed fragment into a Z3 boolean AST.
///
/// Note: since z3 0.19 the crate manages an implicit thread-local
/// [`z3::Context`] and the AST types carry no `'ctx` lifetime, so this takes
/// no explicit context argument.
pub fn to_z3(term: &BoolTerm) -> Bool {
    match term {
        BoolTerm::Eq(a, b) => bv_to_z3(a).eq(bv_to_z3(b)),
        BoolTerm::Ne(a, b) => bv_to_z3(a).eq(bv_to_z3(b)).not(),
        BoolTerm::Ult(a, b) => bv_to_z3(a).bvult(bv_to_z3(b)),
        BoolTerm::Ule(a, b) => bv_to_z3(a).bvule(bv_to_z3(b)),
        BoolTerm::Ugt(a, b) => bv_to_z3(a).bvugt(bv_to_z3(b)),
        BoolTerm::Uge(a, b) => bv_to_z3(a).bvuge(bv_to_z3(b)),
        BoolTerm::Slt(a, b) => bv_to_z3(a).bvslt(bv_to_z3(b)),
        BoolTerm::Sle(a, b) => bv_to_z3(a).bvsle(bv_to_z3(b)),
        BoolTerm::Sgt(a, b) => bv_to_z3(a).bvsgt(bv_to_z3(b)),
        BoolTerm::Sge(a, b) => bv_to_z3(a).bvsge(bv_to_z3(b)),
        BoolTerm::Not(t) => to_z3(t).not(),
        BoolTerm::And(a, b) => Bool::and(&[to_z3(a), to_z3(b)]),
        BoolTerm::Or(a, b) => Bool::or(&[to_z3(a), to_z3(b)]),
    }
}

// ─── Translation: the sliver → Z3's array / UF theories ──────────────────────
//
// The differential check for the sliver (DES-015/016) needs a *reference*
// semantics for `select`/`store`/`pure_call` that is independent of ordeal's
// elimination. Z3's native (extensional) array theory and uninterpreted
// functions provide it: the non-extensional fragment ordeal supports is a
// subset, so on every in-sliver query Z3's verdict must match ordeal's on
// the lowered core.

/// Translate an [`ArrayTerm`] into a Z3 `Array(BV32 → BV8)` AST.
fn array_to_z3(array: &ArrayTerm) -> Array {
    match array {
        ArrayTerm::Var { name } => {
            Array::new_const(name.as_str(), &Z3Sort::bitvector(32), &Z3Sort::bitvector(8))
        }
        ArrayTerm::Store {
            array,
            index,
            value,
        } => array_to_z3(array).store(&ext_bv_to_z3(index), &ext_bv_to_z3(value)),
    }
}

/// Translate an [`ExtBvTerm`] into a Z3 bitvector AST, using Z3's array
/// `select` and an uninterpreted [`FuncDecl`] for each `pure_call`.
fn ext_bv_to_z3(term: &ExtBvTerm) -> BV {
    match term {
        ExtBvTerm::Core(bv) => bv_to_z3(bv),
        ExtBvTerm::Op(op) => ext_op_to_z3(op),
        ExtBvTerm::Select { array, index } => array_to_z3(array)
            .select(&ext_bv_to_z3(index))
            .as_bv()
            .expect("array range is a bitvector sort"),
        ExtBvTerm::PureCall { name, args, sort } => {
            let zargs: Vec<BV> = args.iter().map(ext_bv_to_z3).collect();
            let domain: Vec<Z3Sort> = zargs
                .iter()
                .map(|a| Z3Sort::bitvector(a.get_size()))
                .collect();
            let domain_refs: Vec<&Z3Sort> = domain.iter().collect();
            let f = FuncDecl::new(name.as_str(), &domain_refs, &Z3Sort::bitvector(sort.width));
            let arg_refs: Vec<&dyn Ast> = zargs.iter().map(|b| b as &dyn Ast).collect();
            f.apply(&arg_refs)
                .as_bv()
                .expect("pure_call result is a bitvector sort")
        }
    }
}

/// Translate a lifted core operation (children may be extended) into Z3.
fn ext_op_to_z3(op: &ExtOp) -> BV {
    match op {
        ExtOp::Add(a, b) => ext_bv_to_z3(a).bvadd(ext_bv_to_z3(b)),
        ExtOp::Sub(a, b) => ext_bv_to_z3(a).bvsub(ext_bv_to_z3(b)),
        ExtOp::Mul(a, b) => ext_bv_to_z3(a).bvmul(ext_bv_to_z3(b)),
        ExtOp::Udiv(a, b) => ext_bv_to_z3(a).bvudiv(ext_bv_to_z3(b)),
        ExtOp::And(a, b) => ext_bv_to_z3(a).bvand(ext_bv_to_z3(b)),
        ExtOp::Or(a, b) => ext_bv_to_z3(a).bvor(ext_bv_to_z3(b)),
        ExtOp::Xor(a, b) => ext_bv_to_z3(a).bvxor(ext_bv_to_z3(b)),
        ExtOp::Shl(a, b) => ext_bv_to_z3(a).bvshl(ext_bv_to_z3(b)),
        ExtOp::Lshr(a, b) => ext_bv_to_z3(a).bvlshr(ext_bv_to_z3(b)),
        ExtOp::Ashr(a, b) => ext_bv_to_z3(a).bvashr(ext_bv_to_z3(b)),
        ExtOp::Rotr(a, b) => ext_bv_to_z3(a).bvrotr(ext_bv_to_z3(b)),
        ExtOp::Extract { hi, lo, arg } => ext_bv_to_z3(arg).extract(*hi, *lo),
        ExtOp::Concat(a, b) => ext_bv_to_z3(a).concat(ext_bv_to_z3(b)),
        ExtOp::ZeroExt { by, arg } => ext_bv_to_z3(arg).zero_ext(*by),
        ExtOp::SignExt { by, arg } => ext_bv_to_z3(arg).sign_ext(*by),
    }
}

/// Translate an [`ExtBoolTerm`] into a Z3 boolean AST.
fn ext_bool_to_z3(term: &ExtBoolTerm) -> Bool {
    match term {
        ExtBoolTerm::Eq(a, b) => ext_bv_to_z3(a).eq(ext_bv_to_z3(b)),
        ExtBoolTerm::Ne(a, b) => ext_bv_to_z3(a).eq(ext_bv_to_z3(b)).not(),
        ExtBoolTerm::Ult(a, b) => ext_bv_to_z3(a).bvult(ext_bv_to_z3(b)),
        ExtBoolTerm::Ule(a, b) => ext_bv_to_z3(a).bvule(ext_bv_to_z3(b)),
        ExtBoolTerm::Ugt(a, b) => ext_bv_to_z3(a).bvugt(ext_bv_to_z3(b)),
        ExtBoolTerm::Uge(a, b) => ext_bv_to_z3(a).bvuge(ext_bv_to_z3(b)),
        ExtBoolTerm::Slt(a, b) => ext_bv_to_z3(a).bvslt(ext_bv_to_z3(b)),
        ExtBoolTerm::Sle(a, b) => ext_bv_to_z3(a).bvsle(ext_bv_to_z3(b)),
        ExtBoolTerm::Sgt(a, b) => ext_bv_to_z3(a).bvsgt(ext_bv_to_z3(b)),
        ExtBoolTerm::Sge(a, b) => ext_bv_to_z3(a).bvsge(ext_bv_to_z3(b)),
        ExtBoolTerm::Not(t) => ext_bool_to_z3(t).not(),
        ExtBoolTerm::And(a, b) => Bool::and(&[ext_bool_to_z3(a), ext_bool_to_z3(b)]),
        ExtBoolTerm::Or(a, b) => Bool::or(&[ext_bool_to_z3(a), ext_bool_to_z3(b)]),
    }
}

/// Run Z3's array/UF theories on a conjunction of [`ExtBoolTerm`]s and
/// return only the three-valued verdict (no model — verdict agreement is
/// all the sliver differential needs).
pub fn sliver_z3_check(assertions: &[ExtBoolTerm]) -> OracleVerdict {
    let solver = Solver::new();
    let mut params = Params::new();
    params.set_u32("timeout", 5_000);
    solver.set_params(&params);
    for a in assertions {
        solver.assert(ext_bool_to_z3(a));
    }
    match solver.check() {
        SatResult::Unsat => OracleVerdict::Unsat,
        SatResult::Unknown => OracleVerdict::Unknown,
        // The model is irrelevant to verdict agreement; report an empty env.
        SatResult::Sat => OracleVerdict::Sat(Env::new()),
    }
}

/// A sliver differential disagreement: ordeal-on-lowered-core vs Z3-on-ext.
#[derive(Clone, Debug)]
pub struct SliverDisagreement {
    /// ordeal's verdict on the lowered core.
    pub engine: EngineVerdict,
    /// Z3's verdict on the extended query.
    pub oracle: OracleVerdict,
    /// The extended query both were asked.
    pub assertions: Vec<ExtBoolTerm>,
}

/// Run a sliver query through BOTH paths and compare verdicts:
/// (a) [`sliver::lower`] then the ordeal engine on the resulting core, and
/// (b) Z3 on the [`ExtBoolTerm`] directly via its array/UF theories.
///
/// Out-of-sliver queries (a [`sliver::SliverError`]) are skipped (`None`) —
/// rejection is verified separately. As in [`differential_check`], an
/// `Unknown` from either side never counts as a disagreement.
pub fn sliver_differential(assertions: &[ExtBoolTerm]) -> Option<SliverDisagreement> {
    let core = match sliver::lower(assertions) {
        Ok(c) => c,
        Err(_) => return None,
    };
    let engine = ordeal_engine(&core);
    if engine == EngineVerdict::Unknown {
        return None;
    }
    let oracle = sliver_z3_check(assertions);
    let disagrees = match (&engine, &oracle) {
        (EngineVerdict::Unknown, _) | (_, OracleVerdict::Unknown) => false,
        (EngineVerdict::Sat(_), OracleVerdict::Unsat)
        | (EngineVerdict::Unsat, OracleVerdict::Sat(_)) => true,
        (EngineVerdict::Sat(_), OracleVerdict::Sat(_))
        | (EngineVerdict::Unsat, OracleVerdict::Unsat) => false,
    };
    disagrees.then(|| SliverDisagreement {
        engine,
        oracle,
        assertions: assertions.to_vec(),
    })
}

// ─── Seeded sliver corpus generation ─────────────────────────────────────────

/// Base-array names the sliver corpus reads/writes.
const ARRAYS: [&str; 2] = ["a", "b"];
/// Core BV8 variable names shared across generated terms.
const SLIVER_VARS: [&str; 2] = ["x", "y"];

/// Generate a BV8 extended term. `f` is arity 1 and `g` is arity 2 — the
/// only two uninterpreted functions, kept at fixed arity so every site is
/// consistent (the differential exercises verdicts, not rejection).
fn gen_ext_bv(rng: &mut XorShift64, depth: u32) -> ExtBvTerm {
    if depth == 0 || rng.below(2) == 0 {
        return match rng.below(4) {
            0 => ExtBvTerm::Core(BvTerm::Const {
                value: rng.below(256) as u128,
                sort: Sort::new(8),
            }),
            1 => ExtBvTerm::Core(BvTerm::Var {
                name: SLIVER_VARS[rng.below(2) as usize].into(),
                sort: Sort::new(8),
            }),
            2 => {
                let d = rng.below(3) as u32;
                let arr = gen_ext_array(rng, d);
                ExtBvTerm::Select {
                    array: Box::new(arr),
                    index: Box::new(concrete_index(rng)),
                }
            }
            _ => {
                if rng.below(2) == 0 {
                    ExtBvTerm::PureCall {
                        name: "f".into(),
                        args: vec![gen_ext_bv(rng, depth.saturating_sub(1))],
                        sort: Sort::new(8),
                    }
                } else {
                    ExtBvTerm::PureCall {
                        name: "g".into(),
                        args: vec![
                            gen_ext_bv(rng, depth.saturating_sub(1)),
                            gen_ext_bv(rng, depth.saturating_sub(1)),
                        ],
                        sort: Sort::new(8),
                    }
                }
            }
        };
    }
    let a = gen_ext_bv(rng, depth - 1);
    let b = gen_ext_bv(rng, depth - 1);
    ExtBvTerm::Op(Box::new(match rng.below(4) {
        0 => ExtOp::Add(a, b),
        1 => ExtOp::Sub(a, b),
        2 => ExtOp::Xor(a, b),
        _ => ExtOp::And(a, b),
    }))
}

/// A concrete BV32 index in a small range, to force collisions on the
/// store chain (so read-over-write's hit/miss branches both get exercised).
fn concrete_index(rng: &mut XorShift64) -> ExtBvTerm {
    ExtBvTerm::Core(BvTerm::Const {
        value: rng.below(4) as u128,
        sort: Sort::new(32),
    })
}

/// Build a store chain of the given depth over a random base array.
fn gen_ext_array(rng: &mut XorShift64, depth: u32) -> ArrayTerm {
    let base = ArrayTerm::Var {
        name: ARRAYS[rng.below(2) as usize].into(),
    };
    (0..depth).fold(base, |acc, _| ArrayTerm::Store {
        array: Box::new(acc),
        index: Box::new(concrete_index(rng)),
        value: Box::new(gen_ext_bv(rng, 1)),
    })
}

/// Generate a BV8 comparison / connective extended boolean term.
fn gen_ext_bool(rng: &mut XorShift64, depth: u32) -> ExtBoolTerm {
    if depth == 0 {
        let (a, b) = (gen_ext_bv(rng, 2), gen_ext_bv(rng, 2));
        return match rng.below(6) {
            0 => ExtBoolTerm::Eq(a, b),
            1 => ExtBoolTerm::Ne(a, b),
            2 => ExtBoolTerm::Ult(a, b),
            3 => ExtBoolTerm::Ule(a, b),
            4 => ExtBoolTerm::Slt(a, b),
            _ => ExtBoolTerm::Sle(a, b),
        };
    }
    match rng.below(3) {
        0 => ExtBoolTerm::Not(Box::new(gen_ext_bool(rng, depth - 1))),
        1 => ExtBoolTerm::And(
            Box::new(gen_ext_bool(rng, depth - 1)),
            Box::new(gen_ext_bool(rng, depth - 1)),
        ),
        _ => ExtBoolTerm::Or(
            Box::new(gen_ext_bool(rng, depth - 1)),
            Box::new(gen_ext_bool(rng, depth - 1)),
        ),
    }
}

/// Generate `n` seeded, reproducible sliver queries (stores/selects over
/// concrete offsets and shared-name `pure_call`s), each a conjunction of
/// 1–3 extended assertions. The same `(seed, n)` always yields the same
/// corpus, so a differential disagreement found in CI replays locally.
pub fn gen_sliver_corpus(seed: u64, n: usize) -> Vec<Vec<ExtBoolTerm>> {
    let mut rng = XorShift64::new(seed);
    (0..n)
        .map(|_| {
            let k = 1 + rng.below(3) as usize;
            (0..k).map(|_| gen_ext_bool(&mut rng, 2)).collect()
        })
        .collect()
}

// ─── Free-variable collection ────────────────────────────────────────────────

fn collect_bv_vars(term: &BvTerm, out: &mut BTreeMap<String, u32>) {
    match term {
        BvTerm::Const { .. } => {}
        BvTerm::Var { name, sort } => {
            out.insert(name.clone(), sort.width);
        }
        BvTerm::Add(a, b)
        | BvTerm::Sub(a, b)
        | BvTerm::Mul(a, b)
        | BvTerm::Udiv(a, b)
        | BvTerm::And(a, b)
        | BvTerm::Or(a, b)
        | BvTerm::Xor(a, b)
        | BvTerm::Shl(a, b)
        | BvTerm::Lshr(a, b)
        | BvTerm::Ashr(a, b)
        | BvTerm::Rotr(a, b)
        | BvTerm::Concat(a, b) => {
            collect_bv_vars(a, out);
            collect_bv_vars(b, out);
        }
        BvTerm::Extract { arg, .. } | BvTerm::ZeroExt { arg, .. } | BvTerm::SignExt { arg, .. } => {
            collect_bv_vars(arg, out);
        }
    }
}

fn collect_bool_vars(term: &BoolTerm, out: &mut BTreeMap<String, u32>) {
    match term {
        BoolTerm::Eq(a, b)
        | BoolTerm::Ne(a, b)
        | BoolTerm::Ult(a, b)
        | BoolTerm::Ule(a, b)
        | BoolTerm::Ugt(a, b)
        | BoolTerm::Uge(a, b)
        | BoolTerm::Slt(a, b)
        | BoolTerm::Sle(a, b)
        | BoolTerm::Sgt(a, b)
        | BoolTerm::Sge(a, b) => {
            collect_bv_vars(a, out);
            collect_bv_vars(b, out);
        }
        BoolTerm::Not(t) => collect_bool_vars(t, out),
        BoolTerm::And(a, b) | BoolTerm::Or(a, b) => {
            collect_bool_vars(a, out);
            collect_bool_vars(b, out);
        }
    }
}

/// Collect every free variable (name → width) of a query.
fn free_vars(assertions: &[BoolTerm]) -> BTreeMap<String, u32> {
    let mut out = BTreeMap::new();
    for a in assertions {
        collect_bool_vars(a, &mut out);
    }
    out
}

// ─── Running the oracle ──────────────────────────────────────────────────────

/// Z3's verdict on a query, with a full model on SAT.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OracleVerdict {
    /// Satisfiable; the [`Env`] binds **every** free variable of the query.
    Sat(Env),
    /// Unsatisfiable.
    Unsat,
    /// Z3 gave up (timeout / incompleteness) — never treated as disagreement.
    Unknown,
}

/// Run Z3 on the conjunction of `assertions`.
///
/// On SAT the returned [`Env`] binds every free variable of the query: the
/// terms are walked to collect variable names/widths and each one is
/// evaluated against the model with model completion, so variables Z3 left
/// unconstrained still get a (default) value. The fragment declares variables
/// at widths 8/32/64 only; widths above 64 are not supported here.
pub fn z3_check(assertions: &[BoolTerm]) -> OracleVerdict {
    let solver = Solver::new();
    // Bound each query: an old/slow Z3 on a CI runner must never hang the
    // harness. A timeout surfaces as `Unknown`, which never disagrees.
    let mut params = Params::new();
    params.set_u32("timeout", 2_000);
    solver.set_params(&params);
    for a in assertions {
        solver.assert(to_z3(a));
    }
    match solver.check() {
        SatResult::Unsat => OracleVerdict::Unsat,
        SatResult::Unknown => OracleVerdict::Unknown,
        SatResult::Sat => {
            let model = match solver.get_model() {
                Some(m) => m,
                None => return OracleVerdict::Unknown,
            };
            let mut env = Env::new();
            for (name, width) in free_vars(assertions) {
                assert!(width <= 64, "model extraction supports widths <= 64");
                let var = BV::new_const(name.as_str(), width);
                let value = model
                    .eval(&var, /* model_completion: */ true)
                    .and_then(|v| v.as_u64())
                    .expect("completed model must value every variable");
                env.insert(name, value as u128);
            }
            OracleVerdict::Sat(env)
        }
    }
}

// ─── Differential checking ───────────────────────────────────────────────────

/// The engine-side verdict fed into [`differential_check`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EngineVerdict {
    /// Engine claims SAT with the given model.
    Sat(Env),
    /// Engine claims UNSAT.
    Unsat,
    /// Engine gave up — sound by construction, never a disagreement.
    Unknown,
}

/// A reproducible engine-vs-oracle disagreement: a bug to investigate.
#[derive(Clone, Debug)]
pub struct Disagreement {
    /// What the engine said.
    pub engine: EngineVerdict,
    /// What Z3 said.
    pub oracle: OracleVerdict,
    /// The query both were asked.
    pub assertions: Vec<BoolTerm>,
}

/// Does `env` make every assertion evaluate to `true`?
fn model_checks_out(env: &Env, assertions: &[BoolTerm]) -> bool {
    assertions
        .iter()
        .all(|a| eval::eval_bool(a, env) == Ok(true))
}

/// Run both the engine and the Z3 oracle on a query and compare verdicts.
///
/// Rules:
/// - Engine (or oracle) `Unknown` never disagrees — `Unknown` is sound by
///   construction.
/// - Engine `Sat` vs oracle `Unsat` (and vice versa) is a disagreement.
/// - When both say `Sat`, **both** models are re-evaluated with
///   [`crate::eval::eval_bool`] on every assertion; a model that does not
///   check out is a disagreement (a bad engine model, or a translation bug on
///   the oracle side).
///
/// Returns `None` on agreement, or the full [`Disagreement`] to report.
pub fn differential_check(
    assertions: &[BoolTerm],
    engine: impl Fn(&[BoolTerm]) -> EngineVerdict,
) -> Option<Disagreement> {
    let engine_verdict = engine(assertions);
    if engine_verdict == EngineVerdict::Unknown {
        return None;
    }
    let oracle_verdict = z3_check(assertions);
    let disagrees = match (&engine_verdict, &oracle_verdict) {
        (EngineVerdict::Unknown, _) | (_, OracleVerdict::Unknown) => false,
        (EngineVerdict::Sat(_), OracleVerdict::Unsat)
        | (EngineVerdict::Unsat, OracleVerdict::Sat(_)) => true,
        (EngineVerdict::Unsat, OracleVerdict::Unsat) => false,
        (EngineVerdict::Sat(engine_env), OracleVerdict::Sat(oracle_env)) => {
            !model_checks_out(engine_env, assertions) || !model_checks_out(oracle_env, assertions)
        }
    };
    disagrees.then(|| Disagreement {
        engine: engine_verdict,
        oracle: oracle_verdict,
        assertions: assertions.to_vec(),
    })
}

/// The ordeal engine as a [`differential_check`] engine: runs the real
/// blast → AIG → Tseitin → CDCL pipeline and exposes its RAW verdict
/// (including engine-UNSAT, which the production `check` withholds until the
/// P2 verified checker lands). Dev/CI only — this is exactly the "raw
/// verdict API" UV-010 calls for; it must never become a production path.
pub fn ordeal_engine(assertions: &[BoolTerm]) -> EngineVerdict {
    let mut solver = crate::solver::Solver::new();
    for a in assertions {
        solver.assert(a.clone());
    }
    match solver.check_raw() {
        crate::solver::RawVerdict::Sat(env) => EngineVerdict::Sat(env),
        crate::solver::RawVerdict::Unsat => EngineVerdict::Unsat,
        crate::solver::RawVerdict::Unknown => EngineVerdict::Unknown,
    }
}

// ─── Seeded corpus generation ────────────────────────────────────────────────

/// The variable widths the loom/synth fragment declares.
const WIDTHS: [u32; 3] = [8, 32, 64];

/// Maximum term depth for generated queries.
const MAX_DEPTH: u32 = 5;

/// A tiny xorshift64 PRNG — local so the corpus needs no `rand` dependency
/// and stays byte-for-byte reproducible from the seed.
struct XorShift64 {
    state: u64,
}

impl XorShift64 {
    fn new(seed: u64) -> Self {
        Self {
            // xorshift has an all-zero fixed point; displace it.
            state: if seed == 0 {
                0x2545_F491_4F6C_DD1D
            } else {
                seed
            },
        }
    }

    fn next(&mut self) -> u64 {
        let mut x = self.state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.state = x;
        x
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    fn width(&mut self) -> u32 {
        WIDTHS[self.below(WIDTHS.len() as u64) as usize]
    }
}

/// Generate a leaf of the requested width: a free variable from the pool
/// (when one of that width exists) or a constant.
fn gen_leaf(rng: &mut XorShift64, width: u32, vars: &[(String, u32)]) -> BvTerm {
    let candidates: Vec<&(String, u32)> = vars.iter().filter(|(_, w)| *w == width).collect();
    if !candidates.is_empty() && rng.below(2) == 0 {
        let (name, w) = candidates[rng.below(candidates.len() as u64) as usize];
        BvTerm::Var {
            name: name.clone(),
            sort: Sort::new(*w),
        }
    } else {
        BvTerm::Const {
            value: rng.next() as u128,
            sort: Sort::new(width),
        }
    }
}

/// Generate a well-sorted [`BvTerm`] of exactly `width` bits.
fn gen_bv(rng: &mut XorShift64, width: u32, depth: u32, vars: &[(String, u32)]) -> BvTerm {
    if depth == 0 {
        return gen_leaf(rng, width, vars);
    }
    let bin = |rng: &mut XorShift64| {
        let a = Box::new(gen_bv(rng, width, depth - 1, vars));
        let b = Box::new(gen_bv(rng, width, depth - 1, vars));
        (a, b)
    };
    match rng.below(15) {
        0 => {
            let (a, b) = bin(rng);
            BvTerm::Add(a, b)
        }
        1 => {
            let (a, b) = bin(rng);
            BvTerm::Sub(a, b)
        }
        2 => {
            let (a, b) = bin(rng);
            BvTerm::Mul(a, b)
        }
        3 => {
            let (a, b) = bin(rng);
            BvTerm::Udiv(a, b)
        }
        4 => {
            let (a, b) = bin(rng);
            BvTerm::And(a, b)
        }
        5 => {
            let (a, b) = bin(rng);
            BvTerm::Or(a, b)
        }
        6 => {
            let (a, b) = bin(rng);
            BvTerm::Xor(a, b)
        }
        7 => {
            let (a, b) = bin(rng);
            BvTerm::Shl(a, b)
        }
        8 => {
            let (a, b) = bin(rng);
            BvTerm::Lshr(a, b)
        }
        9 => {
            let (a, b) = bin(rng);
            BvTerm::Ashr(a, b)
        }
        10 => {
            let (a, b) = bin(rng);
            BvTerm::Rotr(a, b)
        }
        11 => {
            // Extract `width` bits out of a fragment width >= `width`.
            let sources: Vec<u32> = WIDTHS.iter().copied().filter(|w| *w >= width).collect();
            let src = sources[rng.below(sources.len() as u64) as usize];
            let lo = rng.below((src - width + 1) as u64) as u32;
            BvTerm::Extract {
                hi: lo + width - 1,
                lo,
                arg: Box::new(gen_bv(rng, src, depth - 1, vars)),
            }
        }
        12 if width == 64 => {
            // Concat splits 64 into two fragment-width halves.
            BvTerm::Concat(
                Box::new(gen_bv(rng, 32, depth - 1, vars)),
                Box::new(gen_bv(rng, 32, depth - 1, vars)),
            )
        }
        13 | 14 if width > 8 => {
            let sources: Vec<u32> = WIDTHS.iter().copied().filter(|w| *w < width).collect();
            let src = sources[rng.below(sources.len() as u64) as usize];
            let arg = Box::new(gen_bv(rng, src, depth - 1, vars));
            if rng.below(2) == 0 {
                BvTerm::ZeroExt {
                    by: width - src,
                    arg,
                }
            } else {
                BvTerm::SignExt {
                    by: width - src,
                    arg,
                }
            }
        }
        // Structural op not expressible at this width — fall back to a leaf.
        _ => gen_leaf(rng, width, vars),
    }
}

/// Generate a well-sorted [`BoolTerm`] with terms of bounded depth.
fn gen_bool(rng: &mut XorShift64, depth: u32, vars: &[(String, u32)]) -> BoolTerm {
    let cmp = |rng: &mut XorShift64| {
        let w = rng.width();
        let a = Box::new(gen_bv(rng, w, depth.saturating_sub(1), vars));
        let b = Box::new(gen_bv(rng, w, depth.saturating_sub(1), vars));
        (a, b)
    };
    // At depth 0 only comparisons (the boolean "leaves") remain.
    let choices = if depth == 0 { 10 } else { 13 };
    match rng.below(choices) {
        0 => {
            let (a, b) = cmp(rng);
            BoolTerm::Eq(a, b)
        }
        1 => {
            let (a, b) = cmp(rng);
            BoolTerm::Ne(a, b)
        }
        2 => {
            let (a, b) = cmp(rng);
            BoolTerm::Ult(a, b)
        }
        3 => {
            let (a, b) = cmp(rng);
            BoolTerm::Ule(a, b)
        }
        4 => {
            let (a, b) = cmp(rng);
            BoolTerm::Ugt(a, b)
        }
        5 => {
            let (a, b) = cmp(rng);
            BoolTerm::Uge(a, b)
        }
        6 => {
            let (a, b) = cmp(rng);
            BoolTerm::Slt(a, b)
        }
        7 => {
            let (a, b) = cmp(rng);
            BoolTerm::Sle(a, b)
        }
        8 => {
            let (a, b) = cmp(rng);
            BoolTerm::Sgt(a, b)
        }
        9 => {
            let (a, b) = cmp(rng);
            BoolTerm::Sge(a, b)
        }
        10 => BoolTerm::Not(Box::new(gen_bool(rng, depth - 1, vars))),
        11 => BoolTerm::And(
            Box::new(gen_bool(rng, depth - 1, vars)),
            Box::new(gen_bool(rng, depth - 1, vars)),
        ),
        _ => BoolTerm::Or(
            Box::new(gen_bool(rng, depth - 1, vars)),
            Box::new(gen_bool(rng, depth - 1, vars)),
        ),
    }
}

/// Corpus generation with an explicit free-variable count (`n_vars == 0`
/// yields constant-only queries, which have a decidable-by-[`crate::eval`]
/// truth value — the translation-sanity test relies on that).
fn gen_corpus_with(seed: u64, n: usize, n_vars: usize) -> Vec<Vec<BoolTerm>> {
    let mut rng = XorShift64::new(seed);
    (0..n)
        .map(|_| {
            let vars: Vec<(String, u32)> = (0..n_vars)
                .map(|i| (format!("v{i}"), rng.width()))
                .collect();
            let n_assertions = 1 + rng.below(3);
            (0..n_assertions)
                .map(|_| gen_bool(&mut rng, MAX_DEPTH, &vars))
                .collect()
        })
        .collect()
}

/// Generate `n` seeded, reproducible, well-sorted random queries.
///
/// Each query is a conjunction of 1–3 assertions over a few free variables
/// (widths 8/32/64 only), with term depth bounded by [`MAX_DEPTH`]. Across a
/// reasonably sized corpus every [`BvTerm`] and [`BoolTerm`] variant is
/// exercised (asserted by a test). The same `(seed, n)` always produces the
/// same corpus — disagreements found in CI replay locally.
pub fn gen_corpus(seed: u64, n: usize) -> Vec<Vec<BoolTerm>> {
    let mut rng = XorShift64::new(seed);
    (0..n)
        .map(|_| {
            let n_vars = 2 + rng.below(2) as usize;
            let seed_i = rng.next();
            gen_corpus_with(seed_i, 1, n_vars).pop().expect("one query")
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval::eval_bool;

    /// Truth value of a constant-only query (conjunction of assertions).
    fn const_query_truth(query: &[BoolTerm]) -> bool {
        query
            .iter()
            .all(|a| eval_bool(a, &Env::new()).expect("well-sorted constant query"))
    }

    #[test]
    fn translation_matches_eval_on_constants() {
        // Constant-only queries have a ground truth computable by the
        // evaluator; Z3's verdict must match it on every corpus entry.
        let corpus = gen_corpus_with(0x0DDEA1, 150, 0);
        for (i, query) in corpus.iter().enumerate() {
            let expected_sat = const_query_truth(query);
            match z3_check(query) {
                OracleVerdict::Sat(_) => {
                    assert!(expected_sat, "query {i}: z3 Sat but eval says false")
                }
                OracleVerdict::Unsat => {
                    assert!(!expected_sat, "query {i}: z3 Unsat but eval says true")
                }
                OracleVerdict::Unknown => panic!("query {i}: z3 Unknown on a constant query"),
            }
        }
    }

    #[test]
    fn sat_models_satisfy_every_assertion() {
        let corpus = gen_corpus(0x0D1F_FCEC, 100);
        let mut sats = 0usize;
        for (i, query) in corpus.iter().enumerate() {
            if let OracleVerdict::Sat(env) = z3_check(query) {
                sats += 1;
                for (j, a) in query.iter().enumerate() {
                    assert_eq!(
                        eval_bool(a, &env),
                        Ok(true),
                        "query {i} assertion {j}: model does not satisfy it\nenv: {env:?}"
                    );
                }
            }
        }
        assert!(
            sats > 0,
            "corpus produced no SAT queries — generator broken"
        );
    }

    #[test]
    fn corpus_exercises_every_variant() {
        fn mark_bv(t: &BvTerm, bv: &mut [bool; 16]) {
            let (idx, children): (usize, Vec<&BvTerm>) = match t {
                BvTerm::Const { .. } => (0, vec![]),
                BvTerm::Var { .. } => (1, vec![]),
                BvTerm::Add(a, b) => (2, vec![a, b]),
                BvTerm::Sub(a, b) => (3, vec![a, b]),
                BvTerm::Mul(a, b) => (4, vec![a, b]),
                BvTerm::Udiv(a, b) => (5, vec![a, b]),
                BvTerm::And(a, b) => (6, vec![a, b]),
                BvTerm::Or(a, b) => (7, vec![a, b]),
                BvTerm::Xor(a, b) => (8, vec![a, b]),
                BvTerm::Shl(a, b) => (9, vec![a, b]),
                BvTerm::Lshr(a, b) => (10, vec![a, b]),
                BvTerm::Ashr(a, b) => (11, vec![a, b]),
                BvTerm::Rotr(a, b) => (12, vec![a, b]),
                BvTerm::Extract { arg, .. } => (13, vec![arg]),
                BvTerm::Concat(a, b) => (14, vec![a, b]),
                BvTerm::ZeroExt { arg, .. } | BvTerm::SignExt { arg, .. } => (15, vec![arg]),
            };
            bv[idx] = true;
            // Distinguish ZeroExt/SignExt via a second pass below.
            for c in children {
                mark_bv(c, bv);
            }
        }
        fn mark_bool(t: &BoolTerm, bl: &mut [bool; 13], bv: &mut [bool; 16], zs: &mut [bool; 2]) {
            let (idx, bvs, bools): (usize, Vec<&BvTerm>, Vec<&BoolTerm>) = match t {
                BoolTerm::Eq(a, b) => (0, vec![a, b], vec![]),
                BoolTerm::Ne(a, b) => (1, vec![a, b], vec![]),
                BoolTerm::Ult(a, b) => (2, vec![a, b], vec![]),
                BoolTerm::Ule(a, b) => (3, vec![a, b], vec![]),
                BoolTerm::Ugt(a, b) => (4, vec![a, b], vec![]),
                BoolTerm::Uge(a, b) => (5, vec![a, b], vec![]),
                BoolTerm::Slt(a, b) => (6, vec![a, b], vec![]),
                BoolTerm::Sle(a, b) => (7, vec![a, b], vec![]),
                BoolTerm::Sgt(a, b) => (8, vec![a, b], vec![]),
                BoolTerm::Sge(a, b) => (9, vec![a, b], vec![]),
                BoolTerm::Not(t) => (10, vec![], vec![t]),
                BoolTerm::And(a, b) => (11, vec![], vec![a, b]),
                BoolTerm::Or(a, b) => (12, vec![], vec![a, b]),
            };
            bl[idx] = true;
            for t in bvs {
                mark_bv(t, bv);
                mark_zs(t, zs);
            }
            for t in bools {
                mark_bool(t, bl, bv, zs);
            }
        }
        fn mark_zs(t: &BvTerm, zs: &mut [bool; 2]) {
            match t {
                BvTerm::ZeroExt { arg, .. } => {
                    zs[0] = true;
                    mark_zs(arg, zs);
                }
                BvTerm::SignExt { arg, .. } => {
                    zs[1] = true;
                    mark_zs(arg, zs);
                }
                BvTerm::Const { .. } | BvTerm::Var { .. } => {}
                BvTerm::Add(a, b)
                | BvTerm::Sub(a, b)
                | BvTerm::Mul(a, b)
                | BvTerm::Udiv(a, b)
                | BvTerm::And(a, b)
                | BvTerm::Or(a, b)
                | BvTerm::Xor(a, b)
                | BvTerm::Shl(a, b)
                | BvTerm::Lshr(a, b)
                | BvTerm::Ashr(a, b)
                | BvTerm::Rotr(a, b)
                | BvTerm::Concat(a, b) => {
                    mark_zs(a, zs);
                    mark_zs(b, zs);
                }
                BvTerm::Extract { arg, .. } => mark_zs(arg, zs),
            }
        }

        let mut bv = [false; 16];
        let mut bl = [false; 13];
        let mut zs = [false; 2];
        for query in gen_corpus(0xC0FFEE, 150) {
            for a in &query {
                mark_bool(a, &mut bl, &mut bv, &mut zs);
            }
        }
        assert!(bv.iter().all(|&c| c), "uncovered BvTerm variant: {bv:?}");
        assert!(bl.iter().all(|&c| c), "uncovered BoolTerm variant: {bl:?}");
        assert!(
            zs.iter().all(|&c| c),
            "ZeroExt/SignExt not both covered: {zs:?}"
        );
    }

    #[test]
    fn corpus_is_reproducible() {
        let a = format!("{:?}", gen_corpus(42, 10));
        let b = format!("{:?}", gen_corpus(42, 10));
        assert_eq!(a, b);
    }

    /// A query with one obvious model: x:8 == 5.
    fn x_is_five() -> Vec<BoolTerm> {
        vec![BoolTerm::Eq(
            Box::new(BvTerm::Var {
                name: "x".into(),
                sort: Sort::new(8),
            }),
            Box::new(BvTerm::Const {
                value: 5,
                sort: Sort::new(8),
            }),
        )]
    }

    #[test]
    fn unknown_engine_never_disagrees() {
        for query in gen_corpus(0xA6BEE, 20) {
            assert!(
                differential_check(&query, |_| EngineVerdict::Unknown).is_none(),
                "Unknown must never disagree"
            );
        }
    }

    #[test]
    fn wrong_sat_model_disagrees() {
        let query = x_is_five();
        // Correct model: agreement.
        let good = Env::from([("x".to_string(), 5u128)]);
        assert!(differential_check(&query, |_| EngineVerdict::Sat(good.clone())).is_none());
        // Wrong model: both say Sat, but the engine model does not check out.
        let bad = Env::from([("x".to_string(), 4u128)]);
        let d = differential_check(&query, |_| EngineVerdict::Sat(bad.clone()))
            .expect("bad model must disagree");
        assert_eq!(d.engine, EngineVerdict::Sat(bad));
        // Engine Unsat vs oracle Sat: verdict-level disagreement.
        let d = differential_check(&query, |_| EngineVerdict::Unsat)
            .expect("Unsat vs Sat must disagree");
        assert!(matches!(d.oracle, OracleVerdict::Sat(_)));
    }

    /// The P1 milestone (UV-010 / VER-001): ordeal's REAL pipeline against
    /// Z3 across the seeded corpus — any disagreement is an ordeal bug and
    /// fails the build (the kill criterion: that op gets disabled until its
    /// rule is fixed).
    #[test]
    fn differential_ordeal_vs_z3_on_corpus() {
        let corpus = gen_corpus(0xC0FF_EE00_5EED_0001, 300);
        let (mut sats, mut unsats, mut unknowns) = (0u32, 0u32, 0u32);
        for (i, query) in corpus.iter().enumerate() {
            match ordeal_engine(query) {
                EngineVerdict::Sat(_) => sats += 1,
                EngineVerdict::Unsat => unsats += 1,
                EngineVerdict::Unknown => unknowns += 1,
            }
            if let Some(d) = differential_check(query, ordeal_engine) {
                panic!("corpus query {i}: ordeal-vs-Z3 disagreement — {d:?}");
            }
        }
        // The corpus must actually exercise the engine on both verdicts —
        // a harness that only ever sees Unknown proves nothing.
        assert!(sats > 0, "corpus produced no engine-SAT verdicts");
        assert!(unsats > 0, "corpus produced no engine-UNSAT verdicts");
        // No P1 op is disabled, so nothing should be Unknown.
        assert_eq!(unknowns, 0, "unexpected Unknown verdicts: {unknowns}");
    }
}

// ─── Sliver differential tests (UV-014 / UV-015) ─────────────────────────────

#[cfg(test)]
mod sliver_oracle_tests {
    use super::*;
    use crate::sliver::{ArrayTerm, ExtBoolTerm, ExtBvTerm, SliverError};

    fn c8(v: u128) -> ExtBvTerm {
        ExtBvTerm::Core(BvTerm::Const {
            value: v,
            sort: Sort::new(8),
        })
    }
    fn v8(name: &str) -> ExtBvTerm {
        ExtBvTerm::Core(BvTerm::Var {
            name: name.into(),
            sort: Sort::new(8),
        })
    }
    fn call(name: &str, args: Vec<ExtBvTerm>) -> ExtBvTerm {
        ExtBvTerm::PureCall {
            name: name.into(),
            args,
            sort: Sort::new(8),
        }
    }

    /// UV-014: read-over-write lowered core vs Z3's array theory over the
    /// seeded corpus. Every in-sliver query's ordeal verdict must match Z3.
    #[test]
    fn sliver_diff() {
        let corpus = gen_sliver_corpus(0x5111_5EED_A55A_0001, 300);
        let (mut sats, mut unsats) = (0u32, 0u32);
        for (i, query) in corpus.iter().enumerate() {
            match ordeal_engine(&crate::sliver::lower(query).expect("in-sliver")) {
                EngineVerdict::Sat(_) => sats += 1,
                EngineVerdict::Unsat => unsats += 1,
                EngineVerdict::Unknown => {}
            }
            if let Some(d) = sliver_differential(query) {
                panic!("sliver corpus query {i}: ordeal-vs-Z3 disagreement — {d:?}");
            }
        }
        assert!(sats > 0, "corpus produced no SAT verdicts");
        assert!(unsats > 0, "corpus produced no UNSAT verdicts");
    }

    /// UV-014: symbolic index and bad sorts are rejected out of the sliver.
    #[test]
    fn sliver_diff_rejects_out_of_sliver() {
        let sym = ExtBoolTerm::Eq(
            ExtBvTerm::Select {
                array: Box::new(ArrayTerm::Var { name: "a".into() }),
                index: Box::new(v8("i_is_bv8")), // not BV32 and non-constant
            },
            c8(0),
        );
        // BV8 index is caught as a bad sort first.
        assert_eq!(
            crate::sliver::lower(&[sym]).err(),
            Some(SliverError::BadArraySort)
        );
        let sym32 = ExtBoolTerm::Eq(
            ExtBvTerm::Select {
                array: Box::new(ArrayTerm::Var { name: "a".into() }),
                index: Box::new(ExtBvTerm::Core(BvTerm::Var {
                    name: "i".into(),
                    sort: Sort::new(32),
                })),
            },
            c8(0),
        );
        assert_eq!(
            crate::sliver::lower(&[sym32]).err(),
            Some(SliverError::NonConcreteIndex)
        );
        // Skipped by the differential (returns None, not a disagreement).
        assert!(sliver_differential(&[sym32_query()]).is_none());
    }

    fn sym32_query() -> ExtBoolTerm {
        ExtBoolTerm::Eq(
            ExtBvTerm::Select {
                array: Box::new(ArrayTerm::Var { name: "a".into() }),
                index: Box::new(ExtBvTerm::Core(BvTerm::Var {
                    name: "i".into(),
                    sort: Sort::new(32),
                })),
            },
            c8(0),
        )
    }

    /// UV-015: uninterpreted-call lowered core vs Z3's UF theory, including
    /// hand-built congruence cases, over the seeded corpus.
    #[test]
    fn sliver_uf() {
        // Congruence: f(x)=5, f(y)=7, x=y is UNSAT on BOTH paths.
        let unsat = vec![
            ExtBoolTerm::Eq(call("f", vec![v8("x")]), c8(5)),
            ExtBoolTerm::Eq(call("f", vec![v8("y")]), c8(7)),
            ExtBoolTerm::Eq(v8("x"), v8("y")),
        ];
        assert!(sliver_differential(&unsat).is_none());
        assert_eq!(
            ordeal_engine(&crate::sliver::lower(&unsat).unwrap()),
            EngineVerdict::Unsat
        );
        assert_eq!(sliver_z3_check(&unsat), OracleVerdict::Unsat);

        // Distinct args leave results free: SAT on both.
        let sat = vec![
            ExtBoolTerm::Eq(call("f", vec![v8("x")]), c8(5)),
            ExtBoolTerm::Eq(call("f", vec![v8("y")]), c8(7)),
            ExtBoolTerm::Ne(v8("x"), v8("y")),
        ];
        assert!(sliver_differential(&sat).is_none());
        assert!(matches!(
            ordeal_engine(&crate::sliver::lower(&sat).unwrap()),
            EngineVerdict::Sat(_)
        ));

        // Corpus (which mixes f/g calls and array reads) must agree throughout.
        let corpus = gen_sliver_corpus(0x5111_0DFF_1CE0_0002, 250);
        let mut uf_seen = 0u32;
        for (i, query) in corpus.iter().enumerate() {
            if mentions_call(query) {
                uf_seen += 1;
            }
            if let Some(d) = sliver_differential(query) {
                panic!("sliver_uf corpus query {i}: disagreement — {d:?}");
            }
        }
        assert!(uf_seen > 0, "corpus exercised no pure_call sites");
    }

    /// UV-015: inconsistent call arity/sorts are rejected.
    #[test]
    fn sliver_uf_rejects_inconsistent_call() {
        let q = vec![
            ExtBoolTerm::Eq(call("f", vec![v8("x")]), c8(1)),
            ExtBoolTerm::Eq(call("f", vec![v8("x"), v8("y")]), c8(2)),
        ];
        assert_eq!(
            crate::sliver::lower(&q).err(),
            Some(SliverError::InconsistentCall { name: "f".into() })
        );
        assert!(sliver_differential(&q).is_none());
    }

    fn mentions_call(query: &[ExtBoolTerm]) -> bool {
        fn in_bv(t: &ExtBvTerm) -> bool {
            match t {
                ExtBvTerm::PureCall { .. } => true,
                ExtBvTerm::Core(_) => false,
                ExtBvTerm::Select { index, .. } => in_bv(index),
                ExtBvTerm::Op(op) => in_op(op),
            }
        }
        fn in_op(op: &crate::sliver::ExtOp) -> bool {
            use crate::sliver::ExtOp::*;
            match op {
                Add(a, b)
                | Sub(a, b)
                | Mul(a, b)
                | Udiv(a, b)
                | And(a, b)
                | Or(a, b)
                | Xor(a, b)
                | Shl(a, b)
                | Lshr(a, b)
                | Ashr(a, b)
                | Rotr(a, b)
                | Concat(a, b) => in_bv(a) || in_bv(b),
                Extract { arg, .. } | ZeroExt { arg, .. } | SignExt { arg, .. } => in_bv(arg),
            }
        }
        fn in_bool(t: &ExtBoolTerm) -> bool {
            use ExtBoolTerm::*;
            match t {
                Eq(a, b)
                | Ne(a, b)
                | Ult(a, b)
                | Ule(a, b)
                | Ugt(a, b)
                | Uge(a, b)
                | Slt(a, b)
                | Sle(a, b)
                | Sgt(a, b)
                | Sge(a, b) => in_bv(a) || in_bv(b),
                Not(x) => in_bool(x),
                And(a, b) | Or(a, b) => in_bool(a) || in_bool(b),
            }
        }
        query.iter().any(in_bool)
    }
}
