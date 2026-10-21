//! The copy of the caller's trees into the kernel's tree type (TR-073).
//!
//! The trusted crate's proven flattener (`ordeal_lrat::flatten_tree`,
//! `kernel.spec.flatten_tree_sound`) consumes its own tree type —
//! `TBv` / `TBool` / `TArray` / `TArgs`, names as byte strings, a call's
//! arguments as a cons-list — and [`crate::term::BoolTerm`] /
//! [`crate::sliver::ExtBoolTerm`] are copied into it here, one constructor
//! for one, `String` names as their bytes, with no interning, no ordering
//! and no decision of any kind. This copy is **the one remaining trusted
//! step** between a caller's constructor calls and the proofs
//! (`docs/design/flattener-proof.md`, option (A1)): it is a bijection
//! ([`to_bool`] / [`to_ext_bool`] are its inverses, pinned by the
//! round-trip tests), and the kernel's output over it is byte-identical to
//! what `dag::flatten` / `sliver::flatten_ext` produce (the differential
//! twins, pinned over every corpus).

use crate::sliver::{ArrayTerm, ExtBoolTerm, ExtBvTerm, ExtOp, ExtQuery};
use crate::term::{BoolTerm, BvTerm, Sort};
use ordeal_lrat::{Flat, TArgs, TArray, TBool, TBv};

fn bx<T>(t: T) -> Box<T> {
    Box::new(t)
}

/// A closed bitvector term, constructor for constructor.
pub fn of_bv(t: &BvTerm) -> TBv {
    use BvTerm as B;
    let c = |x: &BvTerm| bx(of_bv(x));
    match t {
        B::Const { value, sort } => TBv::Const(*value, sort.width as usize),
        B::Var { name, sort } => TBv::Var(name.as_bytes().to_vec(), sort.width as usize),
        B::Add(a, b) => TBv::Add(c(a), c(b)),
        B::Sub(a, b) => TBv::Sub(c(a), c(b)),
        B::Mul(a, b) => TBv::Mul(c(a), c(b)),
        B::Udiv(a, b) => TBv::Udiv(c(a), c(b)),
        B::Urem(a, b) => TBv::Urem(c(a), c(b)),
        B::And(a, b) => TBv::And(c(a), c(b)),
        B::Or(a, b) => TBv::Or(c(a), c(b)),
        B::Xor(a, b) => TBv::Xor(c(a), c(b)),
        B::Shl(a, b) => TBv::Shl(c(a), c(b)),
        B::Lshr(a, b) => TBv::Lshr(c(a), c(b)),
        B::Ashr(a, b) => TBv::Ashr(c(a), c(b)),
        B::Rotr(a, b) => TBv::Rotr(c(a), c(b)),
        B::Extract { hi, lo, arg } => TBv::Extract(*hi as usize, *lo as usize, c(arg)),
        B::Concat(a, b) => TBv::Concat(c(a), c(b)),
        B::ZeroExt { by, arg } => TBv::ZeroExt(*by as usize, c(arg)),
        B::SignExt { by, arg } => TBv::SignExt(*by as usize, c(arg)),
        B::Ite { cond, then_, else_ } => TBv::Ite(bx(of_bool(cond)), c(then_), c(else_)),
        B::Not(a) => TBv::BvNot(c(a)),
        B::Neg(a) => TBv::Neg(c(a)),
        B::Rotl(a, b) => TBv::Rotl(c(a), c(b)),
        B::Sdiv(a, b) => TBv::Sdiv(c(a), c(b)),
        B::Srem(a, b) => TBv::Srem(c(a), c(b)),
    }
}

/// A closed boolean term, constructor for constructor.
pub fn of_bool(t: &BoolTerm) -> TBool {
    use BoolTerm as T;
    let c = |x: &BvTerm| bx(of_bv(x));
    match t {
        T::Eq(a, b) => TBool::Eq(c(a), c(b)),
        T::Ne(a, b) => TBool::Ne(c(a), c(b)),
        T::Ult(a, b) => TBool::Ult(c(a), c(b)),
        T::Ule(a, b) => TBool::Ule(c(a), c(b)),
        T::Ugt(a, b) => TBool::Ugt(c(a), c(b)),
        T::Uge(a, b) => TBool::Uge(c(a), c(b)),
        T::Slt(a, b) => TBool::Slt(c(a), c(b)),
        T::Sle(a, b) => TBool::Sle(c(a), c(b)),
        T::Sgt(a, b) => TBool::Sgt(c(a), c(b)),
        T::Sge(a, b) => TBool::Sge(c(a), c(b)),
        T::Not(a) => TBool::Not(bx(of_bool(a))),
        T::And(a, b) => TBool::And(bx(of_bool(a)), bx(of_bool(b))),
        T::Or(a, b) => TBool::Or(bx(of_bool(a)), bx(of_bool(b))),
    }
}

/// The closed assertions, in order.
pub fn of_bools(ts: &[BoolTerm]) -> Vec<TBool> {
    ts.iter().map(of_bool).collect()
}

fn of_array(a: &ArrayTerm) -> TArray {
    match a {
        ArrayTerm::Var { name } => TArray::Var(name.as_bytes().to_vec()),
        ArrayTerm::Store {
            array,
            index,
            value,
        } => TArray::Store(
            bx(of_array(array)),
            bx(of_ext_bv(index)),
            bx(of_ext_bv(value)),
        ),
    }
}

fn of_op(op: &ExtOp) -> TBv {
    let c = |x: &ExtBvTerm| bx(of_ext_bv(x));
    match op {
        ExtOp::Add(a, b) => TBv::Add(c(a), c(b)),
        ExtOp::Sub(a, b) => TBv::Sub(c(a), c(b)),
        ExtOp::Mul(a, b) => TBv::Mul(c(a), c(b)),
        ExtOp::Udiv(a, b) => TBv::Udiv(c(a), c(b)),
        ExtOp::Urem(a, b) => TBv::Urem(c(a), c(b)),
        ExtOp::Sdiv(a, b) => TBv::Sdiv(c(a), c(b)),
        ExtOp::Srem(a, b) => TBv::Srem(c(a), c(b)),
        ExtOp::And(a, b) => TBv::And(c(a), c(b)),
        ExtOp::Or(a, b) => TBv::Or(c(a), c(b)),
        ExtOp::Xor(a, b) => TBv::Xor(c(a), c(b)),
        ExtOp::Shl(a, b) => TBv::Shl(c(a), c(b)),
        ExtOp::Lshr(a, b) => TBv::Lshr(c(a), c(b)),
        ExtOp::Ashr(a, b) => TBv::Ashr(c(a), c(b)),
        ExtOp::Rotr(a, b) => TBv::Rotr(c(a), c(b)),
        ExtOp::Rotl(a, b) => TBv::Rotl(c(a), c(b)),
        ExtOp::Not(a) => TBv::BvNot(c(a)),
        ExtOp::Neg(a) => TBv::Neg(c(a)),
        ExtOp::Extract { hi, lo, arg } => TBv::Extract(*hi as usize, *lo as usize, c(arg)),
        ExtOp::Concat(a, b) => TBv::Concat(c(a), c(b)),
        ExtOp::ZeroExt { by, arg } => TBv::ZeroExt(*by as usize, c(arg)),
        ExtOp::SignExt { by, arg } => TBv::SignExt(*by as usize, c(arg)),
        ExtOp::Ite { cond, then_, else_ } => TBv::Ite(bx(of_ext_bool(cond)), c(then_), c(else_)),
    }
}

/// An extended bitvector term: a closed leaf as [`of_bv`], a lifted
/// operator as the same constructor, a `select` over its store chain, a
/// call with its arguments as a list.
pub fn of_ext_bv(t: &ExtBvTerm) -> TBv {
    match t {
        ExtBvTerm::Core(bv) => of_bv(bv),
        ExtBvTerm::Op(op) => of_op(op),
        ExtBvTerm::Select { array, index } => {
            TBv::Select(bx(of_array(array)), bx(of_ext_bv(index)))
        }
        ExtBvTerm::PureCall { name, args, sort } => {
            let mut list = TArgs::Nil;
            for a in args.iter().rev() {
                list = TArgs::Cons(bx(of_ext_bv(a)), bx(list));
            }
            TBv::Call(name.as_bytes().to_vec(), sort.width as usize, bx(list))
        }
    }
}

/// An extended boolean term.
pub fn of_ext_bool(t: &ExtBoolTerm) -> TBool {
    use ExtBoolTerm as T;
    let c = |x: &ExtBvTerm| bx(of_ext_bv(x));
    match t {
        T::Eq(a, b) => TBool::Eq(c(a), c(b)),
        T::Ne(a, b) => TBool::Ne(c(a), c(b)),
        T::Ult(a, b) => TBool::Ult(c(a), c(b)),
        T::Ule(a, b) => TBool::Ule(c(a), c(b)),
        T::Ugt(a, b) => TBool::Ugt(c(a), c(b)),
        T::Uge(a, b) => TBool::Uge(c(a), c(b)),
        T::Slt(a, b) => TBool::Slt(c(a), c(b)),
        T::Sle(a, b) => TBool::Sle(c(a), c(b)),
        T::Sgt(a, b) => TBool::Sgt(c(a), c(b)),
        T::Sge(a, b) => TBool::Sge(c(a), c(b)),
        T::Not(a) => TBool::Not(bx(of_ext_bool(a))),
        T::And(a, b) => TBool::And(bx(of_ext_bool(a)), bx(of_ext_bool(b))),
        T::Or(a, b) => TBool::Or(bx(of_ext_bool(a)), bx(of_ext_bool(b))),
    }
}

/// The extended assertions, in order.
pub fn of_ext_bools(ts: &[ExtBoolTerm]) -> Vec<TBool> {
    ts.iter().map(of_ext_bool).collect()
}

/// A name from the kernel's byte arena (`None` if the bytes are not
/// UTF-8 — impossible for bytes that came from a `String`).
fn name_at(arena: &[u8], start: usize, len: usize) -> Option<String> {
    let bytes = arena.get(start..start.checked_add(len)?)?;
    String::from_utf8(bytes.to_vec()).ok()
}

/// The kernel's variable table as the `(name, width, node)` list the
/// `term` / `ext` blocks carry — verbatim, the names decoded.
pub fn var_table(f: &Flat) -> Option<Vec<(String, u32, usize)>> {
    (0..f.var_node.len())
        .map(|k| {
            let name = name_at(&f.names, *f.name_start.get(k)?, *f.name_len.get(k)?)?;
            Some((
                name,
                u32::try_from(*f.var_width.get(k)?).ok()?,
                f.var_node[k],
            ))
        })
        .collect()
}

/// The kernel's array table: names by id.
pub fn array_table(f: &Flat) -> Option<Vec<String>> {
    (0..f.aname_start.len())
        .map(|a| name_at(&f.anames, f.aname_start[a], *f.aname_len.get(a)?))
        .collect()
}

/// The kernel's function table: names and result widths by id.
pub fn func_table(f: &Flat) -> Option<Vec<(String, u32)>> {
    (0..f.fname_start.len())
        .map(|g| {
            let name = name_at(&f.fnames, f.fname_start[g], *f.fname_len.get(g)?)?;
            Some((name, u32::try_from(*f.func_width.get(g)?).ok()?))
        })
        .collect()
}

/// The kernel's flattening as the `ordeal-ext/v1` block
/// ([`crate::sliver::ExtQuery`]).
pub fn ext_query(f: &Flat) -> Option<ExtQuery> {
    Some(ExtQuery {
        nodes: f.nodes.clone(),
        bits: f.bits.clone(),
        side: f.side.clone(),
        roots: f.roots.clone(),
        vars: var_table(f)?,
        arrays: array_table(f)?,
        funcs: func_table(f)?,
    })
}

/// The kernel's constant memo: node → `(raw value, width)`, so the
/// untrusted mapper interns an extended constant under the SAME raw key
/// the kernel did (#262: reconstructing the value from its bits missed
/// the memo of a constant with bits above its width).
pub fn const_table(f: &Flat) -> std::collections::HashMap<usize, (u128, u32)> {
    (0..f.const_node.len())
        .filter_map(|k| {
            Some((
                f.const_node[k],
                (
                    *f.const_value.get(k)?,
                    u32::try_from(*f.const_width.get(k)?).ok()?,
                ),
            ))
        })
        .collect()
}

/* ── the inverses (tests pin the round trips) ── */

fn sort(w: usize) -> Sort {
    Sort::new(u32::try_from(w).unwrap_or(u32::MAX))
}

fn name(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

/// The closed term a kernel tree came from (`None` on a `select` or a
/// call: those have no closed spelling).
pub fn to_bv(t: &TBv) -> Option<BvTerm> {
    use BvTerm as B;
    let c = |x: &TBv| to_bv(x).map(Box::new);
    Some(match t {
        TBv::Const(value, w) => B::Const {
            value: *value,
            sort: sort(*w),
        },
        TBv::Var(n, w) => B::Var {
            name: name(n),
            sort: sort(*w),
        },
        TBv::Add(a, b) => B::Add(c(a)?, c(b)?),
        TBv::Sub(a, b) => B::Sub(c(a)?, c(b)?),
        TBv::Mul(a, b) => B::Mul(c(a)?, c(b)?),
        TBv::Udiv(a, b) => B::Udiv(c(a)?, c(b)?),
        TBv::Urem(a, b) => B::Urem(c(a)?, c(b)?),
        TBv::And(a, b) => B::And(c(a)?, c(b)?),
        TBv::Or(a, b) => B::Or(c(a)?, c(b)?),
        TBv::Xor(a, b) => B::Xor(c(a)?, c(b)?),
        TBv::Shl(a, b) => B::Shl(c(a)?, c(b)?),
        TBv::Lshr(a, b) => B::Lshr(c(a)?, c(b)?),
        TBv::Ashr(a, b) => B::Ashr(c(a)?, c(b)?),
        TBv::Rotr(a, b) => B::Rotr(c(a)?, c(b)?),
        TBv::Extract(hi, lo, a) => B::Extract {
            hi: u32::try_from(*hi).ok()?,
            lo: u32::try_from(*lo).ok()?,
            arg: c(a)?,
        },
        TBv::Concat(a, b) => B::Concat(c(a)?, c(b)?),
        TBv::ZeroExt(by, a) => B::ZeroExt {
            by: u32::try_from(*by).ok()?,
            arg: c(a)?,
        },
        TBv::SignExt(by, a) => B::SignExt {
            by: u32::try_from(*by).ok()?,
            arg: c(a)?,
        },
        TBv::Ite(cond, a, b) => B::Ite {
            cond: Box::new(to_bool(cond)?),
            then_: c(a)?,
            else_: c(b)?,
        },
        TBv::BvNot(a) => B::Not(c(a)?),
        TBv::Neg(a) => B::Neg(c(a)?),
        TBv::Rotl(a, b) => B::Rotl(c(a)?, c(b)?),
        TBv::Sdiv(a, b) => B::Sdiv(c(a)?, c(b)?),
        TBv::Srem(a, b) => B::Srem(c(a)?, c(b)?),
        TBv::Select(..) | TBv::Call(..) => return None,
    })
}

/// The closed assertion a kernel tree came from.
pub fn to_bool(t: &TBool) -> Option<BoolTerm> {
    use BoolTerm as T;
    let c = |x: &TBv| to_bv(x).map(Box::new);
    Some(match t {
        TBool::Eq(a, b) => T::Eq(c(a)?, c(b)?),
        TBool::Ne(a, b) => T::Ne(c(a)?, c(b)?),
        TBool::Ult(a, b) => T::Ult(c(a)?, c(b)?),
        TBool::Ule(a, b) => T::Ule(c(a)?, c(b)?),
        TBool::Ugt(a, b) => T::Ugt(c(a)?, c(b)?),
        TBool::Uge(a, b) => T::Uge(c(a)?, c(b)?),
        TBool::Slt(a, b) => T::Slt(c(a)?, c(b)?),
        TBool::Sle(a, b) => T::Sle(c(a)?, c(b)?),
        TBool::Sgt(a, b) => T::Sgt(c(a)?, c(b)?),
        TBool::Sge(a, b) => T::Sge(c(a)?, c(b)?),
        TBool::Not(a) => T::Not(Box::new(to_bool(a)?)),
        TBool::And(a, b) => T::And(Box::new(to_bool(a)?), Box::new(to_bool(b)?)),
        TBool::Or(a, b) => T::Or(Box::new(to_bool(a)?), Box::new(to_bool(b)?)),
    })
}

fn to_array(a: &TArray) -> ArrayTerm {
    match a {
        TArray::Var(n) => ArrayTerm::Var { name: name(n) },
        TArray::Store(array, index, value) => ArrayTerm::Store {
            array: Box::new(to_array(array)),
            index: Box::new(to_ext_bv(index)),
            value: Box::new(to_ext_bv(value)),
        },
    }
}

/// The extended term a kernel tree came from, in the canonical spelling
/// (a leaf as `Core`, every operator as an `Op`).
pub fn to_ext_bv(t: &TBv) -> ExtBvTerm {
    let c = to_ext_bv;
    let op = |o: ExtOp| ExtBvTerm::Op(Box::new(o));
    match t {
        TBv::Const(value, w) => ExtBvTerm::Core(BvTerm::Const {
            value: *value,
            sort: sort(*w),
        }),
        TBv::Var(n, w) => ExtBvTerm::Core(BvTerm::Var {
            name: name(n),
            sort: sort(*w),
        }),
        TBv::Add(a, b) => op(ExtOp::Add(c(a), c(b))),
        TBv::Sub(a, b) => op(ExtOp::Sub(c(a), c(b))),
        TBv::Mul(a, b) => op(ExtOp::Mul(c(a), c(b))),
        TBv::Udiv(a, b) => op(ExtOp::Udiv(c(a), c(b))),
        TBv::Urem(a, b) => op(ExtOp::Urem(c(a), c(b))),
        TBv::And(a, b) => op(ExtOp::And(c(a), c(b))),
        TBv::Or(a, b) => op(ExtOp::Or(c(a), c(b))),
        TBv::Xor(a, b) => op(ExtOp::Xor(c(a), c(b))),
        TBv::Shl(a, b) => op(ExtOp::Shl(c(a), c(b))),
        TBv::Lshr(a, b) => op(ExtOp::Lshr(c(a), c(b))),
        TBv::Ashr(a, b) => op(ExtOp::Ashr(c(a), c(b))),
        TBv::Rotr(a, b) => op(ExtOp::Rotr(c(a), c(b))),
        TBv::Extract(hi, lo, a) => op(ExtOp::Extract {
            hi: u32::try_from(*hi).unwrap_or(u32::MAX),
            lo: u32::try_from(*lo).unwrap_or(u32::MAX),
            arg: c(a),
        }),
        TBv::Concat(a, b) => op(ExtOp::Concat(c(a), c(b))),
        TBv::ZeroExt(by, a) => op(ExtOp::ZeroExt {
            by: u32::try_from(*by).unwrap_or(u32::MAX),
            arg: c(a),
        }),
        TBv::SignExt(by, a) => op(ExtOp::SignExt {
            by: u32::try_from(*by).unwrap_or(u32::MAX),
            arg: c(a),
        }),
        TBv::Ite(cond, a, b) => op(ExtOp::Ite {
            cond: to_ext_bool(cond),
            then_: c(a),
            else_: c(b),
        }),
        TBv::BvNot(a) => op(ExtOp::Not(c(a))),
        TBv::Neg(a) => op(ExtOp::Neg(c(a))),
        TBv::Rotl(a, b) => op(ExtOp::Rotl(c(a), c(b))),
        TBv::Sdiv(a, b) => op(ExtOp::Sdiv(c(a), c(b))),
        TBv::Srem(a, b) => op(ExtOp::Srem(c(a), c(b))),
        TBv::Select(array, index) => ExtBvTerm::Select {
            array: Box::new(to_array(array)),
            index: Box::new(c(index)),
        },
        TBv::Call(n, w, args) => {
            let mut out = Vec::new();
            let mut cur: &TArgs = args;
            while let TArgs::Cons(a, rest) = cur {
                out.push(c(a));
                cur = rest;
            }
            ExtBvTerm::PureCall {
                name: name(n),
                args: out,
                sort: sort(*w),
            }
        }
    }
}

/// The extended assertion a kernel tree came from.
pub fn to_ext_bool(t: &TBool) -> ExtBoolTerm {
    use ExtBoolTerm as T;
    let c = to_ext_bv;
    match t {
        TBool::Eq(a, b) => T::Eq(c(a), c(b)),
        TBool::Ne(a, b) => T::Ne(c(a), c(b)),
        TBool::Ult(a, b) => T::Ult(c(a), c(b)),
        TBool::Ule(a, b) => T::Ule(c(a), c(b)),
        TBool::Ugt(a, b) => T::Ugt(c(a), c(b)),
        TBool::Uge(a, b) => T::Uge(c(a), c(b)),
        TBool::Slt(a, b) => T::Slt(c(a), c(b)),
        TBool::Sle(a, b) => T::Sle(c(a), c(b)),
        TBool::Sgt(a, b) => T::Sgt(c(a), c(b)),
        TBool::Sge(a, b) => T::Sge(c(a), c(b)),
        TBool::Not(a) => T::Not(Box::new(to_ext_bool(a))),
        TBool::And(a, b) => T::And(Box::new(to_ext_bool(a)), Box::new(to_ext_bool(b))),
        TBool::Or(a, b) => T::Or(Box::new(to_ext_bool(a)), Box::new(to_ext_bool(b))),
    }
}

/// Structural equality of two kernel trees (the kernel type carries no
/// `PartialEq`: it lives in the translation unit).
pub fn tree_eq(a: &TBool, b: &TBool) -> bool {
    bool_eq(a, b)
}

fn bv_eq(a: &TBv, b: &TBv) -> bool {
    match (a, b) {
        (TBv::Const(v, w), TBv::Const(v2, w2)) => v == v2 && w == w2,
        (TBv::Var(n, w), TBv::Var(n2, w2)) => n == n2 && w == w2,
        (TBv::Add(x, y), TBv::Add(x2, y2))
        | (TBv::Sub(x, y), TBv::Sub(x2, y2))
        | (TBv::Mul(x, y), TBv::Mul(x2, y2))
        | (TBv::Udiv(x, y), TBv::Udiv(x2, y2))
        | (TBv::Urem(x, y), TBv::Urem(x2, y2))
        | (TBv::And(x, y), TBv::And(x2, y2))
        | (TBv::Or(x, y), TBv::Or(x2, y2))
        | (TBv::Xor(x, y), TBv::Xor(x2, y2))
        | (TBv::Shl(x, y), TBv::Shl(x2, y2))
        | (TBv::Lshr(x, y), TBv::Lshr(x2, y2))
        | (TBv::Ashr(x, y), TBv::Ashr(x2, y2))
        | (TBv::Rotr(x, y), TBv::Rotr(x2, y2))
        | (TBv::Concat(x, y), TBv::Concat(x2, y2))
        | (TBv::Rotl(x, y), TBv::Rotl(x2, y2))
        | (TBv::Sdiv(x, y), TBv::Sdiv(x2, y2))
        | (TBv::Srem(x, y), TBv::Srem(x2, y2)) => bv_eq(x, x2) && bv_eq(y, y2),
        (TBv::Extract(h, l, x), TBv::Extract(h2, l2, x2)) => h == h2 && l == l2 && bv_eq(x, x2),
        (TBv::ZeroExt(n, x), TBv::ZeroExt(n2, x2)) | (TBv::SignExt(n, x), TBv::SignExt(n2, x2)) => {
            n == n2 && bv_eq(x, x2)
        }
        (TBv::Ite(c, x, y), TBv::Ite(c2, x2, y2)) => bool_eq(c, c2) && bv_eq(x, x2) && bv_eq(y, y2),
        (TBv::BvNot(x), TBv::BvNot(x2)) | (TBv::Neg(x), TBv::Neg(x2)) => bv_eq(x, x2),
        (TBv::Select(arr, i), TBv::Select(arr2, i2)) => array_eq(arr, arr2) && bv_eq(i, i2),
        (TBv::Call(n, w, args), TBv::Call(n2, w2, args2)) => {
            n == n2 && w == w2 && args_eq(args, args2)
        }
        _ => false,
    }
}

fn array_eq(a: &TArray, b: &TArray) -> bool {
    match (a, b) {
        (TArray::Var(n), TArray::Var(n2)) => n == n2,
        (TArray::Store(arr, i, v), TArray::Store(arr2, i2, v2)) => {
            array_eq(arr, arr2) && bv_eq(i, i2) && bv_eq(v, v2)
        }
        _ => false,
    }
}

fn args_eq(a: &TArgs, b: &TArgs) -> bool {
    match (a, b) {
        (TArgs::Nil, TArgs::Nil) => true,
        (TArgs::Cons(x, r), TArgs::Cons(x2, r2)) => bv_eq(x, x2) && args_eq(r, r2),
        _ => false,
    }
}

fn bool_eq(a: &TBool, b: &TBool) -> bool {
    match (a, b) {
        (TBool::Eq(x, y), TBool::Eq(x2, y2))
        | (TBool::Ne(x, y), TBool::Ne(x2, y2))
        | (TBool::Ult(x, y), TBool::Ult(x2, y2))
        | (TBool::Ule(x, y), TBool::Ule(x2, y2))
        | (TBool::Ugt(x, y), TBool::Ugt(x2, y2))
        | (TBool::Uge(x, y), TBool::Uge(x2, y2))
        | (TBool::Slt(x, y), TBool::Slt(x2, y2))
        | (TBool::Sle(x, y), TBool::Sle(x2, y2))
        | (TBool::Sgt(x, y), TBool::Sgt(x2, y2))
        | (TBool::Sge(x, y), TBool::Sge(x2, y2)) => bv_eq(x, x2) && bv_eq(y, y2),
        (TBool::Not(x), TBool::Not(x2)) => bool_eq(x, x2),
        (TBool::And(x, y), TBool::And(x2, y2)) | (TBool::Or(x, y), TBool::Or(x2, y2)) => {
            bool_eq(x, x2) && bool_eq(y, y2)
        }
        _ => false,
    }
}
