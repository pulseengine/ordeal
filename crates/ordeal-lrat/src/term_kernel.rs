//! The proven flattener (TR-073): the caller's query AS A TREE, and its
//! flattening into the node lists every other trusted check is stated
//! over — so that an answer rests on the query as the caller built it,
//! names included, and not on an untrusted serialization of it.
//!
//! `#[path]`-included into `kernel.rs` as its submodule `term_kernel`, so
//! Charon/Aeneas translate it in the same unit as the checker, the
//! lowering and the sliver check (`kernel.term_kernel.*` in
//! `lean/Kernel.lean`); the proofs are `lean/TreeFlatten.lean`. Written in
//! the kernel's fragment — with ONE addition: recursion over the tree.
//! Every `Result` is matched explicitly (no `?`), every loop is its own
//! function, no `String`, no map; names are byte strings compared by a
//! loop.
//!
//! # The tree
//!
//! [`TBv`] / [`TBool`] are the closed fragment (`ordeal::term::BvTerm` /
//! `BoolTerm`) constructor for constructor, plus the sliver's two
//! constructs — [`TBv::Select`] over a store chain ([`TArray`]) and
//! [`TBv::Call`] with its arguments as a cons-list ([`TArgs`]: a `Vec` of
//! subtrees inside the tree is not a valid Lean inductive through the
//! Aeneas `Vec`, see `docs/design/flattener-proof.md`). A variable is a
//! byte-string name at a width; an array and a function are byte-string
//! names. The untrusted side copies its `BoolTerm` / `ExtBoolTerm` into
//! this type one constructor at a time (`ordeal::mirror`) — the one
//! remaining trusted step of the term direction, and a bijection.
//!
//! # The flattening
//!
//! [`flatten_tree`] is the post-order, left-to-right walk `dag::flatten`
//! and `sliver::flatten_ext` perform (operands before operators, an
//! `ite`'s condition first, a `select`'s index then its chain outermost
//! store first, each level's index then its value; a call's arguments in
//! order), with variables shared BY NAME (one node per name; a second
//! width for a name is refused — [`FlatError::NameWidth`]), constants
//! interned by value and width, arrays and functions numbered by first
//! appearance, every operator its own node. Its output is the
//! `ordeal-ext/v1` node list; [`project_core`] is the `ordeal-term/v1`
//! term of a closed tree (every node a `Core` node). The variable table
//! it builds — name, width, node — is what binds a model value to a
//! NAME on `sat` ([`check_tree_model`], [`check_tree_model_ext`]).
//!
//! # What it establishes
//!
//! > If `flatten_tree(ts)` returns `Ok(f)`, then under any assignment to
//! > the tree's named variables (and any array / function interpretation
//! > by name) every root of `f` has the value of the tree it came from,
//! > and the assignment transports both ways through the variable table
//! > (`flatten_tree_sound`, `lean/TreeFlatten.lean`); composed with the
//! > term, query and sliver checks: `tree_unsat_sound` /
//! > `tree_model_sound` (closed trees), `ext_tree_unsat_sound` /
//! > `ext_tree_model_sound` (extended trees).

use super::blast_kernel::DagNode;
use super::sliver_kernel::ExtNode;
use super::{check_input_value, map_at, var_offset};

/// A bitvector tree: the closed fragment plus `select` and `pure_call`.
pub enum TBv {
    /// A constant: `(value, width)`; the node's bits are the value's low
    /// `width` bits.
    Const(u128, usize),
    /// A variable: `(name, width)`.
    Var(Vec<u8>, usize),
    /// `bvadd`.
    Add(Box<TBv>, Box<TBv>),
    /// `bvsub`.
    Sub(Box<TBv>, Box<TBv>),
    /// `bvmul`.
    Mul(Box<TBv>, Box<TBv>),
    /// `bvudiv`.
    Udiv(Box<TBv>, Box<TBv>),
    /// `bvurem`.
    Urem(Box<TBv>, Box<TBv>),
    /// `bvand`.
    And(Box<TBv>, Box<TBv>),
    /// `bvor`.
    Or(Box<TBv>, Box<TBv>),
    /// `bvxor`.
    Xor(Box<TBv>, Box<TBv>),
    /// `bvshl`.
    Shl(Box<TBv>, Box<TBv>),
    /// `bvlshr`.
    Lshr(Box<TBv>, Box<TBv>),
    /// `bvashr`.
    Ashr(Box<TBv>, Box<TBv>),
    /// `rotate_right` by a word amount.
    Rotr(Box<TBv>, Box<TBv>),
    /// `extract[hi:lo]`: `Extract(hi, lo, arg)`.
    Extract(usize, usize, Box<TBv>),
    /// `concat` — the first operand becomes the high bits.
    Concat(Box<TBv>, Box<TBv>),
    /// `zero_extend` by `by` bits: `ZeroExt(by, arg)`.
    ZeroExt(usize, Box<TBv>),
    /// `sign_extend` by `by` bits: `SignExt(by, arg)`.
    SignExt(usize, Box<TBv>),
    /// `ite(cond, then, else)`.
    Ite(Box<TBool>, Box<TBv>, Box<TBv>),
    /// `bvnot`.
    BvNot(Box<TBv>),
    /// `bvneg`.
    Neg(Box<TBv>),
    /// `rotate_left` by a word amount.
    Rotl(Box<TBv>, Box<TBv>),
    /// `bvsdiv` (SMT-LIB).
    Sdiv(Box<TBv>, Box<TBv>),
    /// `bvsrem` (SMT-LIB).
    Srem(Box<TBv>, Box<TBv>),
    /// `select(array, index)` — the BV8 at BV32 `index` (the sliver).
    Select(Box<TArray>, Box<TBv>),
    /// `pure_call`: `Call(name, result width, args)` (the sliver).
    Call(Vec<u8>, usize, Box<TArgs>),
}

/// An array tree: a base array or a store chain (`Store(array, index,
/// value)`, index BV32, value BV8).
pub enum TArray {
    /// A base array, by name.
    Var(Vec<u8>),
    /// `store(array, index, value)`.
    Store(Box<TArray>, Box<TBv>, Box<TBv>),
}

/// The arguments of a call, as a list.
pub enum TArgs {
    /// No more arguments.
    Nil,
    /// One argument, then the rest.
    Cons(Box<TBv>, Box<TArgs>),
}

/// A boolean tree: the predicates asserted.
pub enum TBool {
    /// `=`.
    Eq(Box<TBv>, Box<TBv>),
    /// `distinct`.
    Ne(Box<TBv>, Box<TBv>),
    /// `bvult`.
    Ult(Box<TBv>, Box<TBv>),
    /// `bvule`.
    Ule(Box<TBv>, Box<TBv>),
    /// `bvugt`.
    Ugt(Box<TBv>, Box<TBv>),
    /// `bvuge`.
    Uge(Box<TBv>, Box<TBv>),
    /// `bvslt`.
    Slt(Box<TBv>, Box<TBv>),
    /// `bvsle`.
    Sle(Box<TBv>, Box<TBv>),
    /// `bvsgt`.
    Sgt(Box<TBv>, Box<TBv>),
    /// `bvsge`.
    Sge(Box<TBv>, Box<TBv>),
    /// Boolean `not`.
    Not(Box<TBool>),
    /// Boolean `and`.
    And(Box<TBool>, Box<TBool>),
    /// Boolean `or`.
    Or(Box<TBool>, Box<TBool>),
}

/// Why a tree was refused. Data-only, like the other kernel errors.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FlatError {
    /// A width outside `1..=128`, disagreeing operand widths, `extract`
    /// bounds out of range, or an extension / concatenation past 128.
    BadWidth,
    /// A name used at two widths: one name is one variable.
    NameWidth,
    /// A `select` / `store` index that is not BV32, or a store value that
    /// is not BV8.
    BadArraySort,
    /// A function called at two result widths.
    FuncWidth,
    /// A `select` or a call where a closed node was required
    /// ([`project_core`]).
    NotCore,
}

/// The flattened query: the `ordeal-ext/v1` node list and the tables
/// that name its variables, arrays and functions.
pub struct Flat {
    /// The nodes, operands before operators.
    pub nodes: Vec<ExtNode>,
    /// The constant table (LSB first).
    pub bits: Vec<bool>,
    /// The side table: store chains (index, value pairs) and call
    /// arguments.
    pub side: Vec<usize>,
    /// The asserted nodes, one per tree, in order.
    pub roots: Vec<usize>,
    /// The variable table: variable `k` is the name
    /// `names[name_start[k] .. name_start[k] + name_len[k]]`, of width
    /// `var_width[k]`, at node `var_node[k]` (a `Core(Var)` node). No two
    /// entries carry one name.
    pub names: Vec<u8>,
    /// See `names`.
    pub name_start: Vec<usize>,
    /// See `names`.
    pub name_len: Vec<usize>,
    /// See `names`.
    pub var_node: Vec<usize>,
    /// See `names`.
    pub var_width: Vec<usize>,
    /// The constant memo: constant `k` has value `const_value[k]` at width
    /// `const_width[k]` and node `const_node[k]`.
    pub const_value: Vec<u128>,
    /// See `const_value`.
    pub const_width: Vec<usize>,
    /// See `const_value`.
    pub const_node: Vec<usize>,
    /// The array table: array id `a` is the name
    /// `anames[aname_start[a] .. + aname_len[a]]`, by first appearance.
    pub anames: Vec<u8>,
    /// See `anames`.
    pub aname_start: Vec<usize>,
    /// See `anames`.
    pub aname_len: Vec<usize>,
    /// The function table: function id `f` is the name
    /// `fnames[fname_start[f] .. + fname_len[f]]` with result width
    /// `func_width[f]`, by first appearance.
    pub fnames: Vec<u8>,
    /// See `fnames`.
    pub fname_start: Vec<usize>,
    /// See `fnames`.
    pub fname_len: Vec<usize>,
    /// See `fnames`.
    pub func_width: Vec<usize>,
}

/// An empty flattening.
pub fn flat_new() -> Flat {
    Flat {
        nodes: Vec::new(),
        bits: Vec::new(),
        side: Vec::new(),
        roots: Vec::new(),
        names: Vec::new(),
        name_start: Vec::new(),
        name_len: Vec::new(),
        var_node: Vec::new(),
        var_width: Vec::new(),
        const_value: Vec::new(),
        const_width: Vec::new(),
        const_node: Vec::new(),
        anames: Vec::new(),
        aname_start: Vec::new(),
        aname_len: Vec::new(),
        fnames: Vec::new(),
        fname_start: Vec::new(),
        fname_len: Vec::new(),
        func_width: Vec::new(),
    }
}

/* ══════════════════ NAME TABLES ══════════════════ */

/// Are the `len` bytes of `arena` from `start` the bytes of `name`?
/// (`false`, never a panic, when `name` has another length or the range
/// is outside the arena.)
fn name_is(arena: &[u8], start: usize, len: usize, name: &[u8]) -> bool {
    if len != name.len() || start > arena.len() || len > arena.len() - start {
        return false;
    }
    let mut j = 0usize;
    while j < len {
        if arena[start + j] != name[j] {
            return false;
        }
        j += 1;
    }
    true
}

/// The first table entry whose name is `name`, or `usize::MAX`.
fn table_find(arena: &[u8], starts: &[usize], lens: &[usize], name: &[u8]) -> usize {
    let n = starts.len();
    let mut k = 0usize;
    let mut found = usize::MAX;
    while k < n {
        if found == usize::MAX && k < lens.len() && name_is(arena, starts[k], lens[k], name) {
            found = k;
        }
        k += 1;
    }
    found
}

/// Append the bytes of `name` to `arena`.
fn arena_push(arena: &mut Vec<u8>, name: &[u8]) {
    let mut j = 0usize;
    while j < name.len() {
        arena.push(name[j]);
        j += 1;
    }
}

/// Push a constant's low `w` bits onto the bit table.
fn bits_push(bits: &mut Vec<bool>, value: u128, w: usize) {
    let mut j = 0usize;
    while j < w {
        let bit = (value >> j) & 1;
        bits.push(bit == 1);
        j += 1;
    }
}

/// The constant memo entry for `(value, w)`, or `usize::MAX`.
fn const_find(values: &[u128], widths: &[usize], value: u128, w: usize) -> usize {
    let n = values.len();
    let mut k = 0usize;
    let mut found = usize::MAX;
    while k < n {
        if found == usize::MAX && k < widths.len() && values[k] == value && widths[k] == w {
            found = k;
        }
        k += 1;
    }
    found
}

/// Append `ids` to `side`.
fn side_extend(side: &mut Vec<usize>, ids: &[usize]) {
    let mut j = 0usize;
    while j < ids.len() {
        side.push(ids[j]);
        j += 1;
    }
}

/// A width is `1..=128`.
fn width_ok(w: usize) -> bool {
    w != 0 && w <= 128
}

/* ══════════════════ THE LEAVES ══════════════════ */

/// The node of the constant `(value, w)`: the memo's, or a new `Const`
/// over the value's low `w` bits.
fn flat_const(f: &mut Flat, value: u128, w: usize) -> usize {
    let k = const_find(&f.const_value, &f.const_width, value, w);
    if k != usize::MAX && k < f.const_node.len() {
        return f.const_node[k];
    }
    let s = f.bits.len();
    bits_push(&mut f.bits, value, w);
    let i = f.nodes.len();
    f.nodes.push(ExtNode::Core(DagNode::Const(s, w)));
    f.const_value.push(value);
    f.const_width.push(w);
    f.const_node.push(i);
    i
}

/// The node of the variable `name` at width `w`: the table's (at the same
/// width), or a new `Var`.
fn flat_var(f: &mut Flat, name: &[u8], w: usize) -> Result<usize, FlatError> {
    let k = table_find(&f.names, &f.name_start, &f.name_len, name);
    if k != usize::MAX {
        if k >= f.var_width.len() || k >= f.var_node.len() {
            return Err(FlatError::NameWidth);
        }
        if f.var_width[k] != w {
            return Err(FlatError::NameWidth);
        }
        return Ok(f.var_node[k]);
    }
    let start = f.names.len();
    arena_push(&mut f.names, name);
    let i = f.nodes.len();
    f.nodes.push(ExtNode::Core(DagNode::Var(w)));
    f.name_start.push(start);
    f.name_len.push(name.len());
    f.var_node.push(i);
    f.var_width.push(w);
    Ok(i)
}

/// The id of array `name`: the table's, or the next.
fn flat_array_id(f: &mut Flat, name: &[u8]) -> usize {
    let a = table_find(&f.anames, &f.aname_start, &f.aname_len, name);
    if a != usize::MAX {
        return a;
    }
    let start = f.anames.len();
    arena_push(&mut f.anames, name);
    let a = f.aname_start.len();
    f.aname_start.push(start);
    f.aname_len.push(name.len());
    a
}

/// The id of function `name` at result width `w`: the table's (at the
/// same width), or the next.
fn flat_func_id(f: &mut Flat, name: &[u8], w: usize) -> Result<usize, FlatError> {
    let g = table_find(&f.fnames, &f.fname_start, &f.fname_len, name);
    if g != usize::MAX {
        if g >= f.func_width.len() || f.func_width[g] != w {
            return Err(FlatError::FuncWidth);
        }
        return Ok(g);
    }
    let start = f.fnames.len();
    arena_push(&mut f.fnames, name);
    let g = f.fname_start.len();
    f.fname_start.push(start);
    f.fname_len.push(name.len());
    f.func_width.push(w);
    Ok(g)
}

/* ══════════════════ THE WALK ══════════════════ */

/// Push a closed operator node; returns its index.
fn push_core(f: &mut Flat, nd: DagNode) -> usize {
    let i = f.nodes.len();
    f.nodes.push(ExtNode::Core(nd));
    i
}

/// Flatten a bitvector tree: its node and its width.
#[allow(clippy::question_mark)] // `?` goes through `Try`/`ControlFlow`, which the pinned Aeneas has no model for; the explicit match keeps the Lean term a plain `match`
pub fn flat_bv(t: &TBv, f: &mut Flat) -> Result<(usize, usize), FlatError> {
    match t {
        TBv::Const(value, w) => {
            let w = *w;
            if !width_ok(w) {
                return Err(FlatError::BadWidth);
            }
            let i = flat_const(f, *value, w);
            Ok((i, w))
        }
        TBv::Var(name, w) => {
            let w = *w;
            if !width_ok(w) {
                return Err(FlatError::BadWidth);
            }
            match flat_var(f, name, w) {
                Ok(i) => Ok((i, w)),
                Err(e) => Err(e),
            }
        }
        TBv::Add(a, b) => flat_bin(a, b, f, 0),
        TBv::Sub(a, b) => flat_bin(a, b, f, 1),
        TBv::Mul(a, b) => flat_bin(a, b, f, 2),
        TBv::Udiv(a, b) => flat_bin(a, b, f, 3),
        TBv::Urem(a, b) => flat_bin(a, b, f, 4),
        TBv::And(a, b) => flat_bin(a, b, f, 5),
        TBv::Or(a, b) => flat_bin(a, b, f, 6),
        TBv::Xor(a, b) => flat_bin(a, b, f, 7),
        TBv::Shl(a, b) => flat_bin(a, b, f, 8),
        TBv::Lshr(a, b) => flat_bin(a, b, f, 9),
        TBv::Ashr(a, b) => flat_bin(a, b, f, 10),
        TBv::Rotr(a, b) => flat_bin(a, b, f, 11),
        TBv::Rotl(a, b) => flat_bin(a, b, f, 12),
        TBv::Sdiv(a, b) => flat_bin(a, b, f, 13),
        TBv::Srem(a, b) => flat_bin(a, b, f, 14),
        TBv::Extract(hi, lo, a) => {
            let (hi, lo) = (*hi, *lo);
            let (x, wa) = match flat_bv(a, f) {
                Ok(p) => p,
                Err(e) => return Err(e),
            };
            if hi < lo || hi >= wa {
                return Err(FlatError::BadWidth);
            }
            let i = push_core(f, DagNode::Extract(hi, lo, x));
            Ok((i, hi - lo + 1))
        }
        TBv::Concat(a, b) => {
            let (x, wa) = match flat_bv(a, f) {
                Ok(p) => p,
                Err(e) => return Err(e),
            };
            let (y, wb) = match flat_bv(b, f) {
                Ok(p) => p,
                Err(e) => return Err(e),
            };
            if !width_ok(wa + wb) {
                return Err(FlatError::BadWidth);
            }
            let i = push_core(f, DagNode::Concat(x, y));
            Ok((i, wa + wb))
        }
        TBv::ZeroExt(by, a) => {
            let by = *by;
            let (x, wa) = match flat_bv(a, f) {
                Ok(p) => p,
                Err(e) => return Err(e),
            };
            if by > 128 || !width_ok(wa + by) {
                return Err(FlatError::BadWidth);
            }
            let i = push_core(f, DagNode::ZeroExt(x, by));
            Ok((i, wa + by))
        }
        TBv::SignExt(by, a) => {
            let by = *by;
            let (x, wa) = match flat_bv(a, f) {
                Ok(p) => p,
                Err(e) => return Err(e),
            };
            if by > 128 || !width_ok(wa + by) {
                return Err(FlatError::BadWidth);
            }
            let i = push_core(f, DagNode::SignExt(x, by));
            Ok((i, wa + by))
        }
        TBv::Ite(c, a, b) => {
            let cn = match flat_bool(c, f) {
                Ok(i) => i,
                Err(e) => return Err(e),
            };
            let (x, wa) = match flat_bv(a, f) {
                Ok(p) => p,
                Err(e) => return Err(e),
            };
            let (y, wb) = match flat_bv(b, f) {
                Ok(p) => p,
                Err(e) => return Err(e),
            };
            if wa != wb {
                return Err(FlatError::BadWidth);
            }
            let i = push_core(f, DagNode::Ite(cn, x, y));
            Ok((i, wa))
        }
        TBv::BvNot(a) => {
            let (x, wa) = match flat_bv(a, f) {
                Ok(p) => p,
                Err(e) => return Err(e),
            };
            let i = push_core(f, DagNode::BvNot(x));
            Ok((i, wa))
        }
        TBv::Neg(a) => {
            let (x, wa) = match flat_bv(a, f) {
                Ok(p) => p,
                Err(e) => return Err(e),
            };
            let i = push_core(f, DagNode::Neg(x));
            Ok((i, wa))
        }
        TBv::Select(array, index) => {
            let (j, wj) = match flat_bv(index, f) {
                Ok(p) => p,
                Err(e) => return Err(e),
            };
            if wj != 32 {
                return Err(FlatError::BadArraySort);
            }
            let mut levels: Vec<usize> = Vec::new();
            let aid = match flat_array(array, f, &mut levels) {
                Ok(a) => a,
                Err(e) => return Err(e),
            };
            let s = f.side.len();
            side_extend(&mut f.side, &levels);
            let n = levels.len() / 2;
            let i = f.nodes.len();
            f.nodes.push(ExtNode::Select(aid, j, s, n));
            Ok((i, 8))
        }
        TBv::Call(name, w, args) => {
            let w = *w;
            let mut ids: Vec<usize> = Vec::new();
            match flat_args(args, f, &mut ids) {
                Ok(()) => {}
                Err(e) => return Err(e),
            }
            if !width_ok(w) {
                return Err(FlatError::BadWidth);
            }
            let fid = match flat_func_id(f, name, w) {
                Ok(g) => g,
                Err(e) => return Err(e),
            };
            let s = f.side.len();
            side_extend(&mut f.side, &ids);
            let n = ids.len();
            let i = f.nodes.len();
            f.nodes.push(ExtNode::Call(fid, w, s, n));
            Ok((i, w))
        }
    }
}

/// The node of a width-preserving binary operator `op` (its tag, in the
/// order of [`flat_bv`]'s arms) over the operands' nodes.
fn bin_node(op: usize, x: usize, y: usize) -> DagNode {
    if op == 0 {
        DagNode::Add(x, y)
    } else if op == 1 {
        DagNode::Sub(x, y)
    } else if op == 2 {
        DagNode::Mul(x, y)
    } else if op == 3 {
        DagNode::Udiv(x, y)
    } else if op == 4 {
        DagNode::Urem(x, y)
    } else if op == 5 {
        DagNode::And(x, y)
    } else if op == 6 {
        DagNode::Or(x, y)
    } else if op == 7 {
        DagNode::Xor(x, y)
    } else if op == 8 {
        DagNode::Shl(x, y)
    } else if op == 9 {
        DagNode::Lshr(x, y)
    } else if op == 10 {
        DagNode::Ashr(x, y)
    } else if op == 11 {
        DagNode::Rotr(x, y)
    } else if op == 12 {
        DagNode::Rotl(x, y)
    } else if op == 13 {
        DagNode::Sdiv(x, y)
    } else {
        DagNode::Srem(x, y)
    }
}

/// Flatten a width-preserving binary operator: both operands, equal
/// widths, then the node.
#[allow(clippy::question_mark)] // `?` goes through `Try`/`ControlFlow`, which the pinned Aeneas has no model for; the explicit match keeps the Lean term a plain `match`
fn flat_bin(a: &TBv, b: &TBv, f: &mut Flat, op: usize) -> Result<(usize, usize), FlatError> {
    let (x, wa) = match flat_bv(a, f) {
        Ok(p) => p,
        Err(e) => return Err(e),
    };
    let (y, wb) = match flat_bv(b, f) {
        Ok(p) => p,
        Err(e) => return Err(e),
    };
    if wa != wb {
        return Err(FlatError::BadWidth);
    }
    let i = push_core(f, bin_node(op, x, y));
    Ok((i, wa))
}

/// Flatten a store chain, outermost store first — each level's index
/// (BV32) then its value (BV8) appended to `levels` — down to the base
/// array, whose id is returned.
#[allow(clippy::question_mark)] // `?` goes through `Try`/`ControlFlow`, which the pinned Aeneas has no model for; the explicit match keeps the Lean term a plain `match`
pub fn flat_array(a: &TArray, f: &mut Flat, levels: &mut Vec<usize>) -> Result<usize, FlatError> {
    match a {
        TArray::Var(name) => Ok(flat_array_id(f, name)),
        TArray::Store(array, index, value) => {
            let (ii, wi) = match flat_bv(index, f) {
                Ok(p) => p,
                Err(e) => return Err(e),
            };
            if wi != 32 {
                return Err(FlatError::BadArraySort);
            }
            let (iv, wv) = match flat_bv(value, f) {
                Ok(p) => p,
                Err(e) => return Err(e),
            };
            if wv != 8 {
                return Err(FlatError::BadArraySort);
            }
            levels.push(ii);
            levels.push(iv);
            flat_array(array, f, levels)
        }
    }
}

/// Flatten every argument in order, appending the nodes to `ids`.
#[allow(clippy::question_mark)] // `?` goes through `Try`/`ControlFlow`, which the pinned Aeneas has no model for; the explicit match keeps the Lean term a plain `match`
pub fn flat_args(a: &TArgs, f: &mut Flat, ids: &mut Vec<usize>) -> Result<(), FlatError> {
    match a {
        TArgs::Nil => Ok(()),
        TArgs::Cons(t, rest) => {
            let (x, _w) = match flat_bv(t, f) {
                Ok(p) => p,
                Err(e) => return Err(e),
            };
            ids.push(x);
            flat_args(rest, f, ids)
        }
    }
}

/// The node of a comparison `op` (its tag, in the order of
/// [`flat_bool`]'s arms) over the operands' nodes.
fn cmp_node(op: usize, x: usize, y: usize) -> DagNode {
    if op == 0 {
        DagNode::Eq(x, y)
    } else if op == 1 {
        DagNode::Ne(x, y)
    } else if op == 2 {
        DagNode::Ult(x, y)
    } else if op == 3 {
        DagNode::Ule(x, y)
    } else if op == 4 {
        DagNode::Ugt(x, y)
    } else if op == 5 {
        DagNode::Uge(x, y)
    } else if op == 6 {
        DagNode::Slt(x, y)
    } else if op == 7 {
        DagNode::Sle(x, y)
    } else if op == 8 {
        DagNode::Sgt(x, y)
    } else {
        DagNode::Sge(x, y)
    }
}

/// Flatten a comparison: both operands, equal widths, then the node.
#[allow(clippy::question_mark)] // `?` goes through `Try`/`ControlFlow`, which the pinned Aeneas has no model for; the explicit match keeps the Lean term a plain `match`
fn flat_cmp(a: &TBv, b: &TBv, f: &mut Flat, op: usize) -> Result<usize, FlatError> {
    let (x, wa) = match flat_bv(a, f) {
        Ok(p) => p,
        Err(e) => return Err(e),
    };
    let (y, wb) = match flat_bv(b, f) {
        Ok(p) => p,
        Err(e) => return Err(e),
    };
    if wa != wb {
        return Err(FlatError::BadWidth);
    }
    Ok(push_core(f, cmp_node(op, x, y)))
}

/// Flatten a boolean tree: its node.
#[allow(clippy::question_mark)] // `?` goes through `Try`/`ControlFlow`, which the pinned Aeneas has no model for; the explicit match keeps the Lean term a plain `match`
pub fn flat_bool(t: &TBool, f: &mut Flat) -> Result<usize, FlatError> {
    match t {
        TBool::Eq(a, b) => flat_cmp(a, b, f, 0),
        TBool::Ne(a, b) => flat_cmp(a, b, f, 1),
        TBool::Ult(a, b) => flat_cmp(a, b, f, 2),
        TBool::Ule(a, b) => flat_cmp(a, b, f, 3),
        TBool::Ugt(a, b) => flat_cmp(a, b, f, 4),
        TBool::Uge(a, b) => flat_cmp(a, b, f, 5),
        TBool::Slt(a, b) => flat_cmp(a, b, f, 6),
        TBool::Sle(a, b) => flat_cmp(a, b, f, 7),
        TBool::Sgt(a, b) => flat_cmp(a, b, f, 8),
        TBool::Sge(a, b) => flat_cmp(a, b, f, 9),
        TBool::Not(a) => {
            let x = match flat_bool(a, f) {
                Ok(i) => i,
                Err(e) => return Err(e),
            };
            Ok(push_core(f, DagNode::Not(x)))
        }
        TBool::And(a, b) => {
            let x = match flat_bool(a, f) {
                Ok(i) => i,
                Err(e) => return Err(e),
            };
            let y = match flat_bool(b, f) {
                Ok(i) => i,
                Err(e) => return Err(e),
            };
            Ok(push_core(f, DagNode::BoolAnd(x, y)))
        }
        TBool::Or(a, b) => {
            let x = match flat_bool(a, f) {
                Ok(i) => i,
                Err(e) => return Err(e),
            };
            let y = match flat_bool(b, f) {
                Ok(i) => i,
                Err(e) => return Err(e),
            };
            Ok(push_core(f, DagNode::BoolOr(x, y)))
        }
    }
}

/// Flatten the asserted trees in order, each becoming a root.
#[allow(clippy::question_mark)] // `?` goes through `Try`/`ControlFlow`, which the pinned Aeneas has no model for; the explicit match keeps the Lean term a plain `match`
fn flatten_roots(ts: &[TBool], f: &mut Flat) -> Result<(), FlatError> {
    let n = ts.len();
    let mut k = 0usize;
    while k < n {
        match flat_bool(&ts[k], f) {
            Ok(r) => f.roots.push(r),
            Err(e) => return Err(e),
        }
        k += 1;
    }
    Ok(())
}

/// **The flattening.** The query as the caller built it — the asserted
/// trees, in order — as the `ordeal-ext/v1` node list with its tables.
pub fn flatten_tree(ts: &[TBool]) -> Result<Flat, FlatError> {
    let mut f = flat_new();
    match flatten_roots(ts, &mut f) {
        Ok(()) => Ok(f),
        Err(e) => Err(e),
    }
}

/// The `ordeal-term/v1` term of a closed flattening: every node a `Core`
/// node, as a `DagNode` list (a `select` or a call is
/// [`FlatError::NotCore`]).
pub fn project_core(nodes: &[ExtNode]) -> Result<Vec<DagNode>, FlatError> {
    let mut out: Vec<DagNode> = Vec::new();
    let n = nodes.len();
    let mut i = 0usize;
    while i < n {
        let node = nodes[i];
        let core = match node {
            ExtNode::Core(nd) => nd,
            ExtNode::Select(_, _, _, _) => return Err(FlatError::NotCore),
            ExtNode::Call(_, _, _, _) => return Err(FlatError::NotCore),
        };
        out.push(core);
        i += 1;
    }
    Ok(out)
}

/* ══════════════════ THE MODEL BINDING ══════════════════ */

/// Is `nd` a `Var` of width `w`?
#[allow(clippy::collapsible_match, clippy::needless_bool)] // a bare `v == w` in match-arm position came out of Aeneas as an unresolved `Decidable` instance; the if/else is a plain `if` in the model
fn var_of_width(nd: DagNode, w: usize) -> bool {
    match nd {
        DagNode::Var(v) => {
            if v == w {
                true
            } else {
                false
            }
        }
        _ => false,
    }
}

/// Is `value` the `w` input bits at the `Var` node `m` of `ns`?
fn bound_at(ns: &[DagNode], inp: &[bool], m: usize, w: usize, value: u128) -> bool {
    match var_offset(ns, m) {
        Ok(offset) => {
            if w > inp.len() || offset > inp.len() - w {
                false
            } else {
                check_input_value(inp, offset, w, value)
            }
        }
        Err(_) => false,
    }
}

/// **The model binding of a closed tree.** Every variable of the table
/// whose node has an image in the DAG (`map`, the term map; `usize::MAX`
/// = none) reads `values[k]` at its image's input block of `inp`: a
/// variable the solver's DAG dropped is unconstrained and skipped.
pub fn check_tree_model(
    var_node: &[usize],
    var_width: &[usize],
    map: &[usize],
    ns: &[DagNode],
    inp: &[bool],
    values: &[u128],
) -> bool {
    let n = var_node.len();
    if var_width.len() != n || values.len() != n {
        return false;
    }
    let mut k = 0usize;
    let mut ok = true;
    while k < n {
        let m = map_at(map, var_node[k]);
        if m != usize::MAX && !bound_at(ns, inp, m, var_width[k], values[k]) {
            ok = false;
        }
        k += 1;
    }
    ok
}

/// **The model binding of an extended tree**: through the extended map
/// (`emap`: extended node → core node `t`, which must be a `Var` of the
/// variable's width there — what lets the proof chain the two
/// agreements) and then the term map (`map`: core node → DAG node).
pub fn check_tree_model_ext(
    var_node: &[usize],
    var_width: &[usize],
    emap: &[usize],
    t: &[DagNode],
    map: &[usize],
    ns: &[DagNode],
    inp: &[bool],
    values: &[u128],
) -> bool {
    let n = var_node.len();
    if var_width.len() != n || values.len() != n {
        return false;
    }
    let mut k = 0usize;
    let mut ok = true;
    while k < n {
        let m1 = map_at(emap, var_node[k]);
        if m1 != usize::MAX {
            if m1 >= t.len() {
                ok = false;
            } else {
                let tn = t[m1];
                if !var_of_width(tn, var_width[k]) {
                    ok = false;
                }
                let m = map_at(map, m1);
                if m != usize::MAX && !bound_at(ns, inp, m, var_width[k], values[k]) {
                    ok = false;
                }
            }
        }
        k += 1;
    }
    ok
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(n: &str, w: usize) -> Box<TBv> {
        Box::new(TBv::Var(n.as_bytes().to_vec(), w))
    }

    fn konst(v: u128, w: usize) -> Box<TBv> {
        Box::new(TBv::Const(v, w))
    }

    #[test]
    fn shares_a_name_and_a_constant_and_refuses_a_second_width() {
        // x + 5 = 5 + x : one Var node, one Const node, operators each their own.
        let t = TBool::Eq(
            Box::new(TBv::Add(var("x", 8), konst(5, 8))),
            Box::new(TBv::Add(konst(5, 8), var("x", 8))),
        );
        let f = flatten_tree(&[t]).unwrap();
        let core = project_core(&f.nodes).unwrap();
        assert!(
            core == vec![
                DagNode::Var(8),
                DagNode::Const(0, 8),
                DagNode::Add(0, 1),
                DagNode::Add(1, 0),
                DagNode::Eq(2, 3)
            ]
        );
        assert_eq!(
            f.bits,
            vec![true, false, true, false, false, false, false, false]
        );
        assert_eq!(f.roots, vec![4]);
        assert_eq!(
            (f.var_node.clone(), f.var_width.clone()),
            (vec![0], vec![8])
        );
        assert_eq!(&f.names, b"x");
        // The F2 shape: one name at two widths is refused by the kernel itself.
        let t2 = TBool::Ult(var("x", 8), Box::new(TBv::Extract(7, 0, var("x", 32))));
        assert_eq!(flatten_tree(&[t2]).err(), Some(FlatError::NameWidth));
    }

    #[test]
    fn two_names_two_nodes_and_an_unmasked_constant_is_two_entries() {
        let t = TBool::Ne(
            Box::new(TBv::Add(var("ab", 8), konst(0x1FF, 8))),
            Box::new(TBv::Add(var("a", 8), konst(0xFF, 8))),
        );
        let f = flatten_tree(&[t]).unwrap();
        assert_eq!(f.var_node, vec![0, 3]);
        assert_eq!(&f.names, b"aba");
        assert_eq!(f.name_start, vec![0, 2]);
        assert_eq!(f.name_len, vec![2, 1]);
        // Raw interning: 0x1FF and 0xFF at width 8 are two constant nodes.
        assert_eq!(f.const_node, vec![1, 4]);
        assert_eq!(f.bits.len(), 16);
    }

    #[test]
    fn select_and_call_flatten_in_the_sliver_order() {
        // select(store(a, i, v), j) with a call f(x) as v.
        let chain = TArray::Store(
            Box::new(TArray::Var(b"a".to_vec())),
            var("i", 32),
            Box::new(TBv::Call(
                b"f".to_vec(),
                8,
                Box::new(TArgs::Cons(var("x", 8), Box::new(TArgs::Nil))),
            )),
        );
        let t = TBool::Eq(
            Box::new(TBv::Select(Box::new(chain), var("j", 32))),
            konst(0, 8),
        );
        let f = flatten_tree(&[t]).unwrap();
        // j, i, x, call, select, const, eq
        assert!(matches!(f.nodes[0], ExtNode::Core(DagNode::Var(32))));
        assert!(matches!(f.nodes[1], ExtNode::Core(DagNode::Var(32))));
        assert!(matches!(f.nodes[2], ExtNode::Core(DagNode::Var(8))));
        assert!(f.nodes[3] == ExtNode::Call(0, 8, 0, 1));
        assert!(f.nodes[4] == ExtNode::Select(0, 0, 1, 1));
        assert_eq!(f.side, vec![2, 1, 3]);
        assert_eq!(&f.anames, b"a");
        assert_eq!((&f.fnames[..], f.func_width.clone()), (&b"f"[..], vec![8]));
        assert_eq!(project_core(&f.nodes).err(), Some(FlatError::NotCore));
        // A second width for f is refused; a non-BV32 index too.
        let bad = TBool::Eq(
            Box::new(TBv::Call(b"f".to_vec(), 16, Box::new(TArgs::Nil))),
            konst(0, 16),
        );
        let bad_f = TBool::Eq(
            Box::new(TBv::Call(b"f".to_vec(), 8, Box::new(TArgs::Nil))),
            konst(0, 8),
        );
        assert_eq!(
            flatten_tree(&[bad_f, bad]).err(),
            Some(FlatError::FuncWidth)
        );
        let bad_idx = TBool::Eq(
            Box::new(TBv::Select(
                Box::new(TArray::Var(b"a".to_vec())),
                var("k", 8),
            )),
            konst(0, 8),
        );
        assert_eq!(
            flatten_tree(&[bad_idx]).err(),
            Some(FlatError::BadArraySort)
        );
    }

    #[test]
    fn widths_are_checked_as_the_evaluator_checks_them() {
        let cases: Vec<(TBool, FlatError)> = vec![
            (TBool::Eq(var("x", 0), var("y", 0)), FlatError::BadWidth),
            (TBool::Eq(var("x", 129), var("y", 129)), FlatError::BadWidth),
            (TBool::Eq(var("x", 8), var("y", 9)), FlatError::BadWidth),
            (
                TBool::Eq(Box::new(TBv::Extract(8, 0, var("x", 8))), var("y", 9)),
                FlatError::BadWidth,
            ),
            (
                TBool::Eq(
                    Box::new(TBv::Concat(var("x", 64), var("y", 65))),
                    var("z", 129),
                ),
                FlatError::BadWidth,
            ),
            (
                TBool::Eq(Box::new(TBv::ZeroExt(121, var("x", 8))), var("z", 129)),
                FlatError::BadWidth,
            ),
            (
                TBool::Eq(
                    Box::new(TBv::Ite(
                        Box::new(TBool::Eq(var("c", 1), konst(1, 1))),
                        var("x", 8),
                        var("y", 16),
                    )),
                    var("z", 8),
                ),
                FlatError::BadWidth,
            ),
        ];
        for (t, e) in cases {
            assert_eq!(flatten_tree(&[t]).err(), Some(e));
        }
    }

    #[test]
    fn model_binding_reads_the_values_at_the_images() {
        // Term: Var(8) at 0, Var(8) at 1; DAG: the same, swapped by the map.
        let ns = [DagNode::Var(8), DagNode::Var(8)];
        let map = [1usize, 0];
        let mut inp = vec![false; 16];
        // DAG var 0 (offset 0) = 3, DAG var 1 (offset 8) = 200.
        inp[0] = true;
        inp[1] = true;
        for j in 0..8 {
            inp[8 + j] = (200u128 >> j) & 1 == 1;
        }
        let var_node = [0usize, 1];
        let var_width = [8usize, 8];
        assert!(check_tree_model(
            &var_node,
            &var_width,
            &map,
            &ns,
            &inp,
            &[200, 3]
        ));
        assert!(!check_tree_model(
            &var_node,
            &var_width,
            &map,
            &ns,
            &inp,
            &[3, 200]
        ));
        // An unmapped variable is skipped; a length mismatch is refused.
        assert!(check_tree_model(
            &var_node,
            &var_width,
            &[1, usize::MAX],
            &ns,
            &inp,
            &[200, 7]
        ));
        assert!(!check_tree_model(
            &var_node,
            &var_width,
            &map,
            &ns,
            &inp,
            &[200]
        ));
        // Through two maps.
        let emap = [1usize, 0];
        let t = [DagNode::Var(8), DagNode::Var(8)];
        assert!(check_tree_model_ext(
            &var_node,
            &var_width,
            &emap,
            &t,
            &[0, 1],
            &ns,
            &inp,
            &[200, 3]
        ));
        assert!(!check_tree_model_ext(
            &var_node,
            &var_width,
            &emap,
            &t,
            &[0, 1],
            &ns,
            &inp,
            &[3, 200]
        ));
        // The core image must be a `Var` of the variable's width.
        let t16 = [DagNode::Var(8), DagNode::Var(16)];
        assert!(!check_tree_model_ext(
            &var_node,
            &var_width,
            &emap,
            &t16,
            &[0, 1],
            &ns,
            &inp,
            &[200, 3]
        ));
    }
}
