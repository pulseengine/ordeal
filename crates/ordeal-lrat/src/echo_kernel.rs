//! The certified query echo (issue #281, phase E1): the node lists a
//! certificate is about — the `ordeal-term/v1` term or the `ordeal-ext/v1`
//! extended query, with their name tables — printed back as an SMT-LIB 2.6
//! script, so that someone other than ordeal can read what was certified.
//!
//! `#[path]`-included into `kernel.rs` as its submodule `echo_kernel`, so
//! Charon/Aeneas translate it in the same unit as the checker, the
//! lowering, the sliver check and the flattener (`kernel.echo_kernel.*` in
//! `lean/Kernel.lean`); the SMT-LIB model is `lean/EchoSpec.lean` and the
//! proofs are `lean/Echo.lean`. Written in the kernel's fragment, in
//! `term_kernel.rs`'s style: every `Result` is matched explicitly (no `?`),
//! every loop is its own function, and there is no `String`, `str`,
//! `format!` or `fmt` — bytes are pushed into a `Vec<u8>`, names come from
//! `&[u8]` arenas, the vocabulary is byte literals.
//!
//! # The script
//!
//! ```text
//! (set-logic QF_BV)                    ; QF_ABV with arrays, QF_AUFBV with functions
//! (declare-const |x| (_ BitVec 8))     ; the variable table, in table order
//! (declare-const |m| (Array (_ BitVec 32) (_ BitVec 8)))
//! (declare-fun |f| ((_ BitVec 8) (_ BitVec 32)) (_ BitVec 16))
//! (assert <root 0>)                    ; one assert per root, in root order
//! (check-sat)
//! ```
//!
//! One space separates tokens and one newline ends each command; there
//! are no comments, `let`s or `define-fun`s, so the output is a function
//! of the block. A name is always quoted (`|bytes|`). A constant is `#b`
//! and exactly `w` digits, most significant first. Widths and indices are
//! decimal numerals from one loop ([`push_dec`]). There is one symbol per
//! [`DagNode`] arm ([`push_sym`]). A rotate prints as the indexed
//! `rotate_left` / `rotate_right` with `k = amount mod w`, for a constant
//! amount only. A `select` prints its store chain nested, innermost store
//! last in the side table; a call prints `(|f| a₁ … aₙ)`.
//!
//! # Refusals
//!
//! The printer is not on the verdict path: a refusal ([`EchoError`]) means
//! "no echo", never a verdict. It refuses a list that is not well formed
//! ([`ext_wf`]); a name that is empty, has a byte outside `0x20..=0x7E` or
//! a `|` or `\`, equals a reserved word or a theory symbol
//! ([`is_reserved`]) or collides with another name in any of the three
//! tables (SMT-LIB has one namespace); a boolean node where a bitvector is
//! expected or the reverse; a `Var` node the table does not name at its
//! width; a rotate by a non-constant amount; an operator node that is the
//! operand of two nodes ([`unshared`]: the echo of a hash-consed list
//! could be exponentially larger than the list); a function called at two
//! signatures.
//!
//! # What it establishes
//!
//! > If `echo_ext(…)` returns `Ok(text)`, then `text` is the rendering of
//! > a script that lexes back to itself, and under every SMT-LIB
//! > interpretation of its declared symbols the script is satisfied
//! > exactly when every root of the node list is true under the
//! > assignment, array and function interpretations read off that
//! > interpretation through the tables (`echo_ext_sound`,
//! > `lean/Echo.lean`); composed with the term and sliver capstones, an
//! > accepted `unsat` certificate makes the echoed script unsatisfiable
//! > (`echo_unsat_sound`, `echo_ext_unsat_sound`).

use super::blast_kernel::DagNode;
use super::sliver_kernel::{ExtNode, ext_wf};

/// Why a node list was not echoed. Data-only, like the other kernel
/// errors. Never a verdict.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EchoError {
    /// The list is not well formed (`ext_wf`), a table's columns disagree
    /// in length, a root is not a node, or a `select` / call names an
    /// array / function outside its table.
    Malformed,
    /// A name is empty, has a byte SMT-LIB's quoted symbols exclude, is a
    /// reserved word or a theory symbol, or collides with another name.
    Name,
    /// A boolean node where a bitvector is expected, or the reverse.
    Sort,
    /// A `Var` node the variable table does not name at its width, or a
    /// table variable of width 0.
    Var,
    /// A rotate whose amount is not a `Const` node (or whose width is past
    /// the bound the amount is reduced under).
    Rotate,
    /// An operator node is the operand of two nodes (or asserted twice).
    Shared,
    /// A function is called at two signatures, at a result width its table
    /// entry does not carry, or never.
    Signature,
}

/* ══════════════════ BYTES ══════════════════ */

/// Append `src[start .. start + len]` to `out` (nothing when the range is
/// outside `src`).
fn push_range(out: &mut Vec<u8>, src: &[u8], start: usize, len: usize) {
    if start > src.len() || len > src.len() - start {
        return;
    }
    let mut j = 0usize;
    while j < len {
        out.push(src[start + j]);
        j += 1;
    }
}

/// Append the bytes of `w` to `out`.
fn push_word(out: &mut Vec<u8>, w: &[u8]) {
    push_range(out, w, 0, w.len());
}

/// Are `a[sa .. sa + la]` and `b[sb .. sb + lb]` the same bytes? (`false`,
/// never a panic, when the lengths differ or a range is outside.)
fn range_eq(a: &[u8], sa: usize, la: usize, b: &[u8], sb: usize, lb: usize) -> bool {
    if la != lb || sa > a.len() || la > a.len() - sa || sb > b.len() || lb > b.len() - sb {
        return false;
    }
    let mut j = 0usize;
    while j < la {
        if a[sa + j] != b[sb + j] {
            return false;
        }
        j += 1;
    }
    true
}

/// Is `arena[start .. start + len]` the word `w`?
fn word_is(arena: &[u8], start: usize, len: usize, w: &[u8]) -> bool {
    range_eq(arena, start, len, w, 0, w.len())
}

/// A byte SMT-LIB 2.6 allows inside a quoted symbol, restricted to
/// printable ASCII: `0x20..=0x7E` other than `|` and `\`.
#[allow(clippy::manual_range_contains)] // `RangeInclusive::contains` is outside the translated fragment
fn byte_ok(c: u8) -> bool {
    c >= 0x20 && c <= 0x7E && c != b'|' && c != b'\\'
}

/// Is every byte of `arena[start .. start + len]` allowed in a quoted
/// symbol? (`false` when the range is outside the arena.)
fn bytes_ok(arena: &[u8], start: usize, len: usize) -> bool {
    if start > arena.len() || len > arena.len() - start {
        return false;
    }
    let mut j = 0usize;
    while j < len {
        if !byte_ok(arena[start + j]) {
            return false;
        }
        j += 1;
    }
    true
}

/// Append the decimal numeral of `n` (no leading zeros; `0` is `0`).
fn push_dec(out: &mut Vec<u8>, n: usize) {
    let mut tmp: Vec<u8> = Vec::new();
    let mut m = n;
    while m >= 10 {
        tmp.push(b'0' + (m % 10) as u8);
        m /= 10;
    }
    tmp.push(b'0' + m as u8);
    push_rev(out, &tmp);
}

/// Append the bytes of `tmp`, last first.
fn push_rev(out: &mut Vec<u8>, tmp: &[u8]) {
    let mut j = tmp.len();
    while j > 0 {
        j -= 1;
        out.push(tmp[j]);
    }
}

/// Append the constant `bits[s .. s + w]` as `#b` and `w` digits, most
/// significant first (nothing after `#b` when the range is outside).
fn push_bits(out: &mut Vec<u8>, bits: &[bool], s: usize, w: usize) {
    out.push(b'#');
    out.push(b'b');
    if s > bits.len() || w > bits.len() - s {
        return;
    }
    let mut j = w;
    while j > 0 {
        j -= 1;
        if bits[s + j] {
            out.push(b'1');
        } else {
            out.push(b'0');
        }
    }
}

/// Append `|name|` for the name `arena[start .. start + len]`.
fn push_name(out: &mut Vec<u8>, arena: &[u8], start: usize, len: usize) {
    out.push(b'|');
    push_range(out, arena, start, len);
    out.push(b'|');
}

/// Append the sort `(_ BitVec w)`.
fn push_sort(out: &mut Vec<u8>, w: usize) {
    push_word(out, b"(_ BitVec ");
    push_dec(out, w);
    out.push(b')');
}

/* ══════════════════ RESERVED WORDS ══════════════════ */

// The words a declared name may not be, although it is printed quoted:
// SMT-LIB 2.6 makes `|w|` and `w` the same symbol. The reserved words of
// §3.1 (general and command names), then the symbols of the theories and
// the logic the script is read in (Core, FixedSizeBitVectors, ArraysEx,
// QF_BV's extensions) and the logic names. `lean/EchoSpec.lean` carries
// the same list (`reservedWords`); `is_reserved_ok` (`lean/Echo.lean`)
// proves a name this function passes is not on it.

/// The general reserved words and the first command names.
fn reserved_0(a: &[u8], s: usize, l: usize) -> bool {
    word_is(a, s, l, b"!")
        || word_is(a, s, l, b"_")
        || word_is(a, s, l, b"as")
        || word_is(a, s, l, b"BINARY")
        || word_is(a, s, l, b"DECIMAL")
        || word_is(a, s, l, b"exists")
        || word_is(a, s, l, b"HEXADECIMAL")
        || word_is(a, s, l, b"forall")
        || word_is(a, s, l, b"let")
        || word_is(a, s, l, b"match")
        || word_is(a, s, l, b"NUMERAL")
        || word_is(a, s, l, b"par")
        || word_is(a, s, l, b"STRING")
        || word_is(a, s, l, b"assert")
        || word_is(a, s, l, b"check-sat")
        || word_is(a, s, l, b"check-sat-assuming")
        || word_is(a, s, l, b"declare-const")
        || word_is(a, s, l, b"declare-datatype")
        || word_is(a, s, l, b"declare-datatypes")
        || word_is(a, s, l, b"declare-fun")
        || word_is(a, s, l, b"declare-sort")
        || word_is(a, s, l, b"define-fun")
        || word_is(a, s, l, b"define-fun-rec")
        || word_is(a, s, l, b"define-funs-rec")
}

/// The remaining command names.
fn reserved_1(a: &[u8], s: usize, l: usize) -> bool {
    word_is(a, s, l, b"define-sort")
        || word_is(a, s, l, b"echo")
        || word_is(a, s, l, b"exit")
        || word_is(a, s, l, b"get-assertions")
        || word_is(a, s, l, b"get-assignment")
        || word_is(a, s, l, b"get-info")
        || word_is(a, s, l, b"get-model")
        || word_is(a, s, l, b"get-option")
        || word_is(a, s, l, b"get-proof")
        || word_is(a, s, l, b"get-unsat-assumptions")
        || word_is(a, s, l, b"get-unsat-core")
        || word_is(a, s, l, b"get-value")
        || word_is(a, s, l, b"pop")
        || word_is(a, s, l, b"push")
        || word_is(a, s, l, b"reset")
        || word_is(a, s, l, b"reset-assertions")
        || word_is(a, s, l, b"set-info")
        || word_is(a, s, l, b"set-logic")
        || word_is(a, s, l, b"set-option")
}

/// The Core theory, the logic names, and the first bitvector symbols.
fn reserved_2(a: &[u8], s: usize, l: usize) -> bool {
    word_is(a, s, l, b"Bool")
        || word_is(a, s, l, b"true")
        || word_is(a, s, l, b"false")
        || word_is(a, s, l, b"not")
        || word_is(a, s, l, b"=>")
        || word_is(a, s, l, b"and")
        || word_is(a, s, l, b"or")
        || word_is(a, s, l, b"xor")
        || word_is(a, s, l, b"=")
        || word_is(a, s, l, b"distinct")
        || word_is(a, s, l, b"ite")
        || word_is(a, s, l, b"QF_BV")
        || word_is(a, s, l, b"QF_ABV")
        || word_is(a, s, l, b"QF_AUFBV")
        || word_is(a, s, l, b"Array")
        || word_is(a, s, l, b"select")
        || word_is(a, s, l, b"store")
        || word_is(a, s, l, b"BitVec")
        || word_is(a, s, l, b"concat")
        || word_is(a, s, l, b"extract")
        || word_is(a, s, l, b"repeat")
        || word_is(a, s, l, b"zero_extend")
        || word_is(a, s, l, b"sign_extend")
        || word_is(a, s, l, b"rotate_left")
        || word_is(a, s, l, b"rotate_right")
}

/// The remaining bitvector symbols.
fn reserved_3(a: &[u8], s: usize, l: usize) -> bool {
    word_is(a, s, l, b"bvnot")
        || word_is(a, s, l, b"bvneg")
        || word_is(a, s, l, b"bvand")
        || word_is(a, s, l, b"bvor")
        || word_is(a, s, l, b"bvxor")
        || word_is(a, s, l, b"bvnand")
        || word_is(a, s, l, b"bvnor")
        || word_is(a, s, l, b"bvxnor")
        || word_is(a, s, l, b"bvcomp")
        || word_is(a, s, l, b"bvadd")
        || word_is(a, s, l, b"bvsub")
        || word_is(a, s, l, b"bvmul")
        || word_is(a, s, l, b"bvudiv")
        || word_is(a, s, l, b"bvurem")
        || word_is(a, s, l, b"bvsdiv")
        || word_is(a, s, l, b"bvsrem")
        || word_is(a, s, l, b"bvsmod")
        || word_is(a, s, l, b"bvshl")
        || word_is(a, s, l, b"bvlshr")
        || word_is(a, s, l, b"bvashr")
        || word_is(a, s, l, b"bvult")
        || word_is(a, s, l, b"bvule")
        || word_is(a, s, l, b"bvugt")
        || word_is(a, s, l, b"bvuge")
        || word_is(a, s, l, b"bvslt")
        || word_is(a, s, l, b"bvsle")
        || word_is(a, s, l, b"bvsgt")
        || word_is(a, s, l, b"bvsge")
}

/// Is the name `a[s .. s + l]` a reserved word or a theory symbol?
fn is_reserved(a: &[u8], s: usize, l: usize) -> bool {
    reserved_0(a, s, l) || reserved_1(a, s, l) || reserved_2(a, s, l) || reserved_3(a, s, l)
}

/* ══════════════════ NAME TABLES ══════════════════ */

/// Does one of the first `upto` entries of the table carry the bytes
/// `b[sb .. sb + lb]`?
fn table_has(
    arena: &[u8],
    starts: &[usize],
    lens: &[usize],
    upto: usize,
    b: &[u8],
    sb: usize,
    lb: usize,
) -> bool {
    let mut j = 0usize;
    let mut found = false;
    while j < upto {
        if j < starts.len() && j < lens.len() && range_eq(arena, starts[j], lens[j], b, sb, lb) {
            found = true;
        }
        j += 1;
    }
    found
}

/// Is entry `k` of the table a non-empty range of quotable bytes, not
/// reserved, different from every earlier name of the table and from
/// every name of the two tables before it (`a1`, `a2`)?
#[allow(clippy::too_many_arguments)] // the fragment has no structs to bundle them
fn entry_ok(
    arena: &[u8],
    starts: &[usize],
    lens: &[usize],
    a1: &[u8],
    s1: &[usize],
    l1: &[usize],
    a2: &[u8],
    s2: &[usize],
    l2: &[usize],
    k: usize,
) -> bool {
    if k >= starts.len() || k >= lens.len() {
        return false;
    }
    let s = starts[k];
    let l = lens[k];
    if l == 0 {
        return false;
    }
    if !bytes_ok(arena, s, l) {
        return false;
    }
    if is_reserved(arena, s, l) {
        return false;
    }
    if table_has(arena, starts, lens, k, arena, s, l) {
        return false;
    }
    if table_has(a1, s1, l1, s1.len(), arena, s, l) {
        return false;
    }
    if table_has(a2, s2, l2, s2.len(), arena, s, l) {
        return false;
    }
    true
}

/// Is every entry of the table [`entry_ok`]?
#[allow(clippy::too_many_arguments)] // the fragment has no structs to bundle them
fn table_ok(
    arena: &[u8],
    starts: &[usize],
    lens: &[usize],
    a1: &[u8],
    s1: &[usize],
    l1: &[usize],
    a2: &[u8],
    s2: &[usize],
    l2: &[usize],
) -> bool {
    let n = starts.len();
    if lens.len() != n {
        return false;
    }
    let mut k = 0usize;
    while k < n {
        if !entry_ok(arena, starts, lens, a1, s1, l1, a2, s2, l2, k) {
            return false;
        }
        k += 1;
    }
    true
}

/// The first table entry whose node is `i`, or `usize::MAX`.
fn find_node(var_node: &[usize], i: usize) -> usize {
    let n = var_node.len();
    let mut k = 0usize;
    while k < n {
        if var_node[k] == i {
            return k;
        }
        k += 1;
    }
    usize::MAX
}

/// Is `node` a call of function `g`?
#[allow(clippy::collapsible_match, clippy::needless_bool)] // a bare `f == g` in match-arm position comes out of Aeneas as an unresolved `Decidable` instance (see `term_kernel::var_of_width`)
fn call_of(node: ExtNode, g: usize) -> bool {
    match node {
        ExtNode::Call(f, _, _, _) => {
            if f == g {
                true
            } else {
                false
            }
        }
        _ => false,
    }
}

/// The first node that calls function `g`, or `usize::MAX`: the call
/// whose arguments give `g` its declared signature.
fn find_call(nodes: &[ExtNode], g: usize) -> usize {
    let n = nodes.len();
    let mut c = 0usize;
    while c < n {
        let node = nodes[c];
        if call_of(node, g) {
            return c;
        }
        c += 1;
    }
    usize::MAX
}

/// The width of node `x`, or 0 (no node has width 0) past the list.
fn width_at(ws: &[usize], x: usize) -> usize {
    if x < ws.len() { ws[x] } else { 0 }
}

/// Do the `n` argument nodes from `side[s]` have the widths of the `n`
/// from `side[s0]`?
fn args_match(ws: &[usize], side: &[usize], s: usize, s0: usize, n: usize) -> bool {
    let m = side.len();
    if s > m || n > m - s || s0 > m || n > m - s0 {
        return false;
    }
    let mut j = 0usize;
    while j < n {
        if width_at(ws, side[s + j]) != width_at(ws, side[s0 + j]) {
            return false;
        }
        j += 1;
    }
    true
}

/* ══════════════════ THE SHARING GUARD ══════════════════ */

/// Count one more use of node `i`, saturating at 2.
#[allow(clippy::ptr_arg)] // a `Vec` like every other buffer the fragment writes to; `&mut [usize]` would add an unsizing at each call
fn bump(uses: &mut Vec<usize>, i: usize) {
    if i < uses.len() {
        let c = uses[i];
        if c == 0 {
            uses[i] = 1;
        } else {
            uses[i] = 2;
        }
    }
}

/// Count a use of each of the `n` side-table nodes from `side[s]`.
fn bump_side(uses: &mut Vec<usize>, side: &[usize], s: usize, n: usize) {
    let m = side.len();
    let mut off = s;
    let mut j = 0usize;
    while j < n && off < m {
        bump(uses, side[off]);
        off += 1;
        j += 1;
    }
}

/// Count a use of every operand of a closed node.
fn bump_core(uses: &mut Vec<usize>, nd: DagNode) {
    match nd {
        DagNode::Var(_) => {}
        DagNode::Const(_, _) => {}
        DagNode::Add(a, b)
        | DagNode::Sub(a, b)
        | DagNode::Mul(a, b)
        | DagNode::Udiv(a, b)
        | DagNode::Urem(a, b)
        | DagNode::And(a, b)
        | DagNode::Or(a, b)
        | DagNode::Xor(a, b)
        | DagNode::Shl(a, b)
        | DagNode::Lshr(a, b)
        | DagNode::Ashr(a, b)
        | DagNode::Rotr(a, b)
        | DagNode::Concat(a, b)
        | DagNode::Eq(a, b)
        | DagNode::Ne(a, b)
        | DagNode::Ult(a, b)
        | DagNode::Ule(a, b)
        | DagNode::Ugt(a, b)
        | DagNode::Uge(a, b)
        | DagNode::Slt(a, b)
        | DagNode::Sle(a, b)
        | DagNode::Sgt(a, b)
        | DagNode::Sge(a, b)
        | DagNode::BoolAnd(a, b)
        | DagNode::BoolOr(a, b)
        | DagNode::Rotl(a, b)
        | DagNode::Sdiv(a, b)
        | DagNode::Srem(a, b) => {
            bump(uses, a);
            bump(uses, b);
        }
        DagNode::Extract(_, _, a) => bump(uses, a),
        DagNode::ZeroExt(a, _)
        | DagNode::SignExt(a, _)
        | DagNode::Not(a)
        | DagNode::BvNot(a)
        | DagNode::Neg(a) => bump(uses, a),
        DagNode::Ite(c, t, e) => {
            bump(uses, c);
            bump(uses, t);
            bump(uses, e);
        }
    }
}

/// Count a use of every operand of a node: a `select`'s index and its
/// chain (two side-table nodes per level), a call's arguments.
fn bump_node(uses: &mut Vec<usize>, side: &[usize], node: ExtNode) {
    match node {
        ExtNode::Core(nd) => bump_core(uses, nd),
        ExtNode::Select(_, j, s, n) => {
            bump(uses, j);
            bump_side(uses, side, s, n);
            if s <= side.len() && n <= side.len() - s {
                bump_side(uses, side, s + n, n);
            }
        }
        ExtNode::Call(_, _, s, n) => bump_side(uses, side, s, n),
    }
}

/// Is `node` a leaf (a `Var` or a `Const`)? Leaves are the only nodes the
/// flattener shares.
#[allow(clippy::match_like_matches_macro)] // `matches!` is outside the kernel's house style
fn is_leaf(node: ExtNode) -> bool {
    match node {
        ExtNode::Core(nd) => match nd {
            DagNode::Var(_) => true,
            DagNode::Const(_, _) => true,
            _ => false,
        },
        _ => false,
    }
}

/// `n` zeros.
fn zeros(n: usize) -> Vec<usize> {
    let mut v: Vec<usize> = Vec::new();
    let mut i = 0usize;
    while i < n {
        v.push(0);
        i += 1;
    }
    v
}

/// Count the uses of every node as an operand.
fn count_operands(uses: &mut Vec<usize>, nodes: &[ExtNode], side: &[usize]) {
    let n = nodes.len();
    let mut i = 0usize;
    while i < n {
        let node = nodes[i];
        bump_node(uses, side, node);
        i += 1;
    }
}

/// Count the uses of every node as a root.
fn count_roots(uses: &mut Vec<usize>, roots: &[usize]) {
    let n = roots.len();
    let mut k = 0usize;
    while k < n {
        bump(uses, roots[k]);
        k += 1;
    }
}

/// Is no operator node used twice?
fn no_shared(uses: &[usize], nodes: &[ExtNode]) -> bool {
    let n = nodes.len();
    let mut i = 0usize;
    while i < n {
        let node = nodes[i];
        if i < uses.len() && uses[i] > 1 && !is_leaf(node) {
            return false;
        }
        i += 1;
    }
    true
}

/// **The sharing guard.** Is every operator node the operand of at most
/// one node (a root counts as a use)? `flatten_tree` output always is
/// (every operator its own node; only `Var` / `Const` leaves are shared),
/// so unfolding the list from its roots is linear in the list. A
/// hash-consed list is refused: its echo could be exponentially larger.
/// This is a resource guard, not part of the echo theorem.
fn unshared(nodes: &[ExtNode], side: &[usize], roots: &[usize]) -> bool {
    let mut uses = zeros(nodes.len());
    count_operands(&mut uses, nodes, side);
    count_roots(&mut uses, roots);
    no_shared(&uses, nodes)
}

/* ══════════════════ SYMBOLS AND ROTATE AMOUNTS ══════════════════ */

/// Append the SMT-LIB symbol of a closed operator node: one symbol per
/// [`DagNode`] arm (nothing for a `Var` or a `Const`, which are not
/// applications).
fn push_sym(out: &mut Vec<u8>, nd: DagNode) {
    match nd {
        DagNode::Var(_) => {}
        DagNode::Const(_, _) => {}
        DagNode::Add(_, _) => push_word(out, b"bvadd"),
        DagNode::Sub(_, _) => push_word(out, b"bvsub"),
        DagNode::Mul(_, _) => push_word(out, b"bvmul"),
        DagNode::Udiv(_, _) => push_word(out, b"bvudiv"),
        DagNode::Urem(_, _) => push_word(out, b"bvurem"),
        DagNode::And(_, _) => push_word(out, b"bvand"),
        DagNode::Or(_, _) => push_word(out, b"bvor"),
        DagNode::Xor(_, _) => push_word(out, b"bvxor"),
        DagNode::Shl(_, _) => push_word(out, b"bvshl"),
        DagNode::Lshr(_, _) => push_word(out, b"bvlshr"),
        DagNode::Ashr(_, _) => push_word(out, b"bvashr"),
        DagNode::Rotr(_, _) => push_word(out, b"rotate_right"),
        DagNode::Extract(_, _, _) => push_word(out, b"extract"),
        DagNode::Concat(_, _) => push_word(out, b"concat"),
        DagNode::ZeroExt(_, _) => push_word(out, b"zero_extend"),
        DagNode::SignExt(_, _) => push_word(out, b"sign_extend"),
        DagNode::Ite(_, _, _) => push_word(out, b"ite"),
        DagNode::Eq(_, _) => push_word(out, b"="),
        DagNode::Ne(_, _) => push_word(out, b"distinct"),
        DagNode::Ult(_, _) => push_word(out, b"bvult"),
        DagNode::Ule(_, _) => push_word(out, b"bvule"),
        DagNode::Ugt(_, _) => push_word(out, b"bvugt"),
        DagNode::Uge(_, _) => push_word(out, b"bvuge"),
        DagNode::Slt(_, _) => push_word(out, b"bvslt"),
        DagNode::Sle(_, _) => push_word(out, b"bvsle"),
        DagNode::Sgt(_, _) => push_word(out, b"bvsgt"),
        DagNode::Sge(_, _) => push_word(out, b"bvsge"),
        DagNode::Not(_) => push_word(out, b"not"),
        DagNode::BoolAnd(_, _) => push_word(out, b"and"),
        DagNode::BoolOr(_, _) => push_word(out, b"or"),
        DagNode::BvNot(_) => push_word(out, b"bvnot"),
        DagNode::Neg(_) => push_word(out, b"bvneg"),
        DagNode::Rotl(_, _) => push_word(out, b"rotate_left"),
        DagNode::Sdiv(_, _) => push_word(out, b"bvsdiv"),
        DagNode::Srem(_, _) => push_word(out, b"bvsrem"),
    }
}

/// The constant `bits[s .. s + wb]` (LSB first) modulo `w`, for
/// `1 <= w <= 65536` (so the arithmetic stays far inside `usize`) and a
/// range inside `bits`.
fn rot_amount(bits: &[bool], s: usize, wb: usize, w: usize) -> usize {
    let mut k = 0usize;
    let mut p = 1 % w;
    let mut j = 0usize;
    while j < wb {
        if bits[s + j] {
            k = (k + p) % w;
        }
        p = (p * 2) % w;
        j += 1;
    }
    k
}

/// The rotate amount of a rotate of width `w` by node `amt`: the amount's
/// constant modulo `w`, or a refusal when it is not a `Const` (or `w` is
/// past the bound [`rot_amount`] reduces under).
#[allow(clippy::collapsible_match)] // one `match` per enum, as the model's nested `match` (see `is_leaf`)
fn rot_of(bits: &[bool], amt: ExtNode, w: usize) -> Result<usize, EchoError> {
    match amt {
        ExtNode::Core(nd) => match nd {
            DagNode::Const(s, wb) => {
                if w == 0 || w > 65536 || s > bits.len() || wb > bits.len() - s {
                    return Err(EchoError::Rotate);
                }
                Ok(rot_amount(bits, s, wb, w))
            }
            _ => Err(EchoError::Rotate),
        },
        _ => Err(EchoError::Rotate),
    }
}

/// The side-table range `(s, n)` of the arguments of node `node` when it
/// is a call; a refusal otherwise.
fn call_args(node: ExtNode) -> Result<(usize, usize), EchoError> {
    match node {
        ExtNode::Call(_, _, s, n) => Ok((s, n)),
        _ => Err(EchoError::Signature),
    }
}

/// Append `n` times `(store `: the opening of a chain of `n` stores.
fn push_stores(out: &mut Vec<u8>, n: usize) {
    let mut j = 0usize;
    while j < n {
        push_word(out, b"(store ");
        j += 1;
    }
}

/* ══════════════════ THE WALK ══════════════════ */

/// Echo node `i` as a term of the expected sort (`want_bool`: a formula;
/// otherwise a bitvector term), recursing into its operands — earlier
/// nodes, by `ext_wf`, whose widths `ws` holds.
#[allow(clippy::too_many_arguments)] // the fragment has no structs to bundle them
#[allow(clippy::question_mark)] // `?` goes through `Try`/`ControlFlow`, which the pinned Aeneas has no model for; the explicit match keeps the Lean term a plain `match`
fn echo_node(
    nodes: &[ExtNode],
    bits: &[bool],
    side: &[usize],
    ws: &[usize],
    names: &[u8],
    name_start: &[usize],
    name_len: &[usize],
    var_node: &[usize],
    var_width: &[usize],
    anames: &[u8],
    aname_start: &[usize],
    aname_len: &[usize],
    fnames: &[u8],
    fname_start: &[usize],
    fname_len: &[usize],
    func_width: &[usize],
    i: usize,
    want_bool: bool,
    out: &mut Vec<u8>,
) -> Result<(), EchoError> {
    if i >= nodes.len() || i >= ws.len() {
        return Err(EchoError::Malformed);
    }
    let node = nodes[i];
    match node {
        ExtNode::Core(nd) => match nd {
            DagNode::Var(w) => {
                if want_bool {
                    return Err(EchoError::Sort);
                }
                let k = find_node(var_node, i);
                if k >= name_start.len() || k >= name_len.len() || k >= var_width.len() {
                    return Err(EchoError::Var);
                }
                if var_width[k] != w {
                    return Err(EchoError::Var);
                }
                push_name(out, names, name_start[k], name_len[k]);
                Ok(())
            }
            DagNode::Const(s, w) => {
                if want_bool {
                    return Err(EchoError::Sort);
                }
                push_bits(out, bits, s, w);
                Ok(())
            }
            DagNode::Add(a, b)
            | DagNode::Sub(a, b)
            | DagNode::Mul(a, b)
            | DagNode::Udiv(a, b)
            | DagNode::Urem(a, b)
            | DagNode::And(a, b)
            | DagNode::Or(a, b)
            | DagNode::Xor(a, b)
            | DagNode::Shl(a, b)
            | DagNode::Lshr(a, b)
            | DagNode::Ashr(a, b)
            | DagNode::Concat(a, b)
            | DagNode::Sdiv(a, b)
            | DagNode::Srem(a, b) => {
                if want_bool {
                    return Err(EchoError::Sort);
                }
                out.push(b'(');
                push_sym(out, nd);
                echo_two(
                    nodes,
                    bits,
                    side,
                    ws,
                    names,
                    name_start,
                    name_len,
                    var_node,
                    var_width,
                    anames,
                    aname_start,
                    aname_len,
                    fnames,
                    fname_start,
                    fname_len,
                    func_width,
                    a,
                    b,
                    false,
                    out,
                )
            }
            DagNode::Eq(a, b)
            | DagNode::Ne(a, b)
            | DagNode::Ult(a, b)
            | DagNode::Ule(a, b)
            | DagNode::Ugt(a, b)
            | DagNode::Uge(a, b)
            | DagNode::Slt(a, b)
            | DagNode::Sle(a, b)
            | DagNode::Sgt(a, b)
            | DagNode::Sge(a, b) => {
                if !want_bool {
                    return Err(EchoError::Sort);
                }
                out.push(b'(');
                push_sym(out, nd);
                echo_two(
                    nodes,
                    bits,
                    side,
                    ws,
                    names,
                    name_start,
                    name_len,
                    var_node,
                    var_width,
                    anames,
                    aname_start,
                    aname_len,
                    fnames,
                    fname_start,
                    fname_len,
                    func_width,
                    a,
                    b,
                    false,
                    out,
                )
            }
            DagNode::BoolAnd(a, b) | DagNode::BoolOr(a, b) => {
                if !want_bool {
                    return Err(EchoError::Sort);
                }
                out.push(b'(');
                push_sym(out, nd);
                echo_two(
                    nodes,
                    bits,
                    side,
                    ws,
                    names,
                    name_start,
                    name_len,
                    var_node,
                    var_width,
                    anames,
                    aname_start,
                    aname_len,
                    fnames,
                    fname_start,
                    fname_len,
                    func_width,
                    a,
                    b,
                    true,
                    out,
                )
            }
            DagNode::BvNot(a) | DagNode::Neg(a) => {
                if want_bool {
                    return Err(EchoError::Sort);
                }
                out.push(b'(');
                push_sym(out, nd);
                echo_one(
                    nodes,
                    bits,
                    side,
                    ws,
                    names,
                    name_start,
                    name_len,
                    var_node,
                    var_width,
                    anames,
                    aname_start,
                    aname_len,
                    fnames,
                    fname_start,
                    fname_len,
                    func_width,
                    a,
                    false,
                    out,
                )
            }
            DagNode::Not(a) => {
                if !want_bool {
                    return Err(EchoError::Sort);
                }
                out.push(b'(');
                push_sym(out, nd);
                echo_one(
                    nodes,
                    bits,
                    side,
                    ws,
                    names,
                    name_start,
                    name_len,
                    var_node,
                    var_width,
                    anames,
                    aname_start,
                    aname_len,
                    fnames,
                    fname_start,
                    fname_len,
                    func_width,
                    a,
                    true,
                    out,
                )
            }
            DagNode::Extract(hi, lo, a) => {
                if want_bool {
                    return Err(EchoError::Sort);
                }
                push_word(out, b"((_ ");
                push_sym(out, nd);
                out.push(b' ');
                push_dec(out, hi);
                out.push(b' ');
                push_dec(out, lo);
                out.push(b')');
                echo_one(
                    nodes,
                    bits,
                    side,
                    ws,
                    names,
                    name_start,
                    name_len,
                    var_node,
                    var_width,
                    anames,
                    aname_start,
                    aname_len,
                    fnames,
                    fname_start,
                    fname_len,
                    func_width,
                    a,
                    false,
                    out,
                )
            }
            DagNode::ZeroExt(a, by) | DagNode::SignExt(a, by) => {
                if want_bool {
                    return Err(EchoError::Sort);
                }
                push_word(out, b"((_ ");
                push_sym(out, nd);
                out.push(b' ');
                push_dec(out, by);
                out.push(b')');
                echo_one(
                    nodes,
                    bits,
                    side,
                    ws,
                    names,
                    name_start,
                    name_len,
                    var_node,
                    var_width,
                    anames,
                    aname_start,
                    aname_len,
                    fnames,
                    fname_start,
                    fname_len,
                    func_width,
                    a,
                    false,
                    out,
                )
            }
            DagNode::Rotr(a, b) | DagNode::Rotl(a, b) => {
                if want_bool {
                    return Err(EchoError::Sort);
                }
                if b >= nodes.len() {
                    return Err(EchoError::Malformed);
                }
                let amt = nodes[b];
                let k = match rot_of(bits, amt, ws[i]) {
                    Ok(k) => k,
                    Err(e) => return Err(e),
                };
                push_word(out, b"((_ ");
                push_sym(out, nd);
                out.push(b' ');
                push_dec(out, k);
                out.push(b')');
                echo_one(
                    nodes,
                    bits,
                    side,
                    ws,
                    names,
                    name_start,
                    name_len,
                    var_node,
                    var_width,
                    anames,
                    aname_start,
                    aname_len,
                    fnames,
                    fname_start,
                    fname_len,
                    func_width,
                    a,
                    false,
                    out,
                )
            }
            DagNode::Ite(c, t, e) => {
                if want_bool {
                    return Err(EchoError::Sort);
                }
                out.push(b'(');
                push_sym(out, nd);
                out.push(b' ');
                match echo_node(
                    nodes,
                    bits,
                    side,
                    ws,
                    names,
                    name_start,
                    name_len,
                    var_node,
                    var_width,
                    anames,
                    aname_start,
                    aname_len,
                    fnames,
                    fname_start,
                    fname_len,
                    func_width,
                    c,
                    true,
                    out,
                ) {
                    Ok(()) => {}
                    Err(e) => return Err(e),
                }
                echo_two(
                    nodes,
                    bits,
                    side,
                    ws,
                    names,
                    name_start,
                    name_len,
                    var_node,
                    var_width,
                    anames,
                    aname_start,
                    aname_len,
                    fnames,
                    fname_start,
                    fname_len,
                    func_width,
                    t,
                    e,
                    false,
                    out,
                )
            }
        },
        ExtNode::Select(aid, j, s, n) => {
            if want_bool {
                return Err(EchoError::Sort);
            }
            if aid >= aname_start.len() || aid >= aname_len.len() {
                return Err(EchoError::Malformed);
            }
            push_word(out, b"(select ");
            push_stores(out, n);
            push_name(out, anames, aname_start[aid], aname_len[aid]);
            match echo_levels(
                nodes,
                bits,
                side,
                ws,
                names,
                name_start,
                name_len,
                var_node,
                var_width,
                anames,
                aname_start,
                aname_len,
                fnames,
                fname_start,
                fname_len,
                func_width,
                s,
                n,
                out,
            ) {
                Ok(()) => {}
                Err(e) => return Err(e),
            }
            echo_one(
                nodes,
                bits,
                side,
                ws,
                names,
                name_start,
                name_len,
                var_node,
                var_width,
                anames,
                aname_start,
                aname_len,
                fnames,
                fname_start,
                fname_len,
                func_width,
                j,
                false,
                out,
            )
        }
        ExtNode::Call(fid, w, s, n) => {
            if want_bool {
                return Err(EchoError::Sort);
            }
            if fid >= fname_start.len() || fid >= fname_len.len() || fid >= func_width.len() {
                return Err(EchoError::Malformed);
            }
            if func_width[fid] != w {
                return Err(EchoError::Signature);
            }
            let c = find_call(nodes, fid);
            if c >= nodes.len() {
                return Err(EchoError::Signature);
            }
            let first = nodes[c];
            let (s0, n0) = match call_args(first) {
                Ok(p) => p,
                Err(e) => return Err(e),
            };
            if n0 != n {
                return Err(EchoError::Signature);
            }
            if !args_match(ws, side, s, s0, n) {
                return Err(EchoError::Signature);
            }
            if n == 0 {
                push_name(out, fnames, fname_start[fid], fname_len[fid]);
                return Ok(());
            }
            out.push(b'(');
            push_name(out, fnames, fname_start[fid], fname_len[fid]);
            match echo_args(
                nodes,
                bits,
                side,
                ws,
                names,
                name_start,
                name_len,
                var_node,
                var_width,
                anames,
                aname_start,
                aname_len,
                fnames,
                fname_start,
                fname_len,
                func_width,
                s,
                n,
                out,
            ) {
                Ok(()) => {}
                Err(e) => return Err(e),
            }
            out.push(b')');
            Ok(())
        }
    }
}

/// Echo ` A)`: the last operand of an application and its closing
/// parenthesis.
#[allow(clippy::too_many_arguments)] // the fragment has no structs to bundle them
fn echo_one(
    nodes: &[ExtNode],
    bits: &[bool],
    side: &[usize],
    ws: &[usize],
    names: &[u8],
    name_start: &[usize],
    name_len: &[usize],
    var_node: &[usize],
    var_width: &[usize],
    anames: &[u8],
    aname_start: &[usize],
    aname_len: &[usize],
    fnames: &[u8],
    fname_start: &[usize],
    fname_len: &[usize],
    func_width: &[usize],
    a: usize,
    a_bool: bool,
    out: &mut Vec<u8>,
) -> Result<(), EchoError> {
    out.push(b' ');
    match echo_node(
        nodes,
        bits,
        side,
        ws,
        names,
        name_start,
        name_len,
        var_node,
        var_width,
        anames,
        aname_start,
        aname_len,
        fnames,
        fname_start,
        fname_len,
        func_width,
        a,
        a_bool,
        out,
    ) {
        Ok(()) => {}
        Err(e) => return Err(e),
    }
    out.push(b')');
    Ok(())
}

/// Echo ` A B)`: the last two operands of an application, both of the
/// sort `ops_bool` says, and its closing parenthesis.
#[allow(clippy::too_many_arguments)] // the fragment has no structs to bundle them
fn echo_two(
    nodes: &[ExtNode],
    bits: &[bool],
    side: &[usize],
    ws: &[usize],
    names: &[u8],
    name_start: &[usize],
    name_len: &[usize],
    var_node: &[usize],
    var_width: &[usize],
    anames: &[u8],
    aname_start: &[usize],
    aname_len: &[usize],
    fnames: &[u8],
    fname_start: &[usize],
    fname_len: &[usize],
    func_width: &[usize],
    a: usize,
    b: usize,
    ops_bool: bool,
    out: &mut Vec<u8>,
) -> Result<(), EchoError> {
    out.push(b' ');
    match echo_node(
        nodes,
        bits,
        side,
        ws,
        names,
        name_start,
        name_len,
        var_node,
        var_width,
        anames,
        aname_start,
        aname_len,
        fnames,
        fname_start,
        fname_len,
        func_width,
        a,
        ops_bool,
        out,
    ) {
        Ok(()) => {}
        Err(e) => return Err(e),
    }
    echo_one(
        nodes,
        bits,
        side,
        ws,
        names,
        name_start,
        name_len,
        var_node,
        var_width,
        anames,
        aname_start,
        aname_len,
        fnames,
        fname_start,
        fname_len,
        func_width,
        b,
        ops_bool,
        out,
    )
}

/// Echo the closings of the first `l` levels of the store chain at
/// `side[s]`, innermost of them first: for level `l - 1` down to `0`,
/// ` I V)` with `I = side[s + 2·level]` and `V = side[s + 2·level + 1]`.
#[allow(clippy::too_many_arguments)] // the fragment has no structs to bundle them
fn echo_levels(
    nodes: &[ExtNode],
    bits: &[bool],
    side: &[usize],
    ws: &[usize],
    names: &[u8],
    name_start: &[usize],
    name_len: &[usize],
    var_node: &[usize],
    var_width: &[usize],
    anames: &[u8],
    aname_start: &[usize],
    aname_len: &[usize],
    fnames: &[u8],
    fname_start: &[usize],
    fname_len: &[usize],
    func_width: &[usize],
    s: usize,
    l: usize,
    out: &mut Vec<u8>,
) -> Result<(), EchoError> {
    if l == 0 {
        return Ok(());
    }
    let l1 = l - 1;
    let m = side.len();
    if s > m || l1 >= (m - s) / 2 {
        return Err(EchoError::Malformed);
    }
    let off = s + 2 * l1;
    let x = side[off];
    let y = side[off + 1];
    match echo_two(
        nodes,
        bits,
        side,
        ws,
        names,
        name_start,
        name_len,
        var_node,
        var_width,
        anames,
        aname_start,
        aname_len,
        fnames,
        fname_start,
        fname_len,
        func_width,
        x,
        y,
        false,
        out,
    ) {
        Ok(()) => {}
        Err(e) => return Err(e),
    }
    echo_levels(
        nodes,
        bits,
        side,
        ws,
        names,
        name_start,
        name_len,
        var_node,
        var_width,
        anames,
        aname_start,
        aname_len,
        fnames,
        fname_start,
        fname_len,
        func_width,
        s,
        l1,
        out,
    )
}

/// Echo the first `n` arguments of the call at `side[s]`, each after a
/// space, in order.
#[allow(clippy::too_many_arguments)] // the fragment has no structs to bundle them
fn echo_args(
    nodes: &[ExtNode],
    bits: &[bool],
    side: &[usize],
    ws: &[usize],
    names: &[u8],
    name_start: &[usize],
    name_len: &[usize],
    var_node: &[usize],
    var_width: &[usize],
    anames: &[u8],
    aname_start: &[usize],
    aname_len: &[usize],
    fnames: &[u8],
    fname_start: &[usize],
    fname_len: &[usize],
    func_width: &[usize],
    s: usize,
    n: usize,
    out: &mut Vec<u8>,
) -> Result<(), EchoError> {
    if n == 0 {
        return Ok(());
    }
    let n1 = n - 1;
    match echo_args(
        nodes,
        bits,
        side,
        ws,
        names,
        name_start,
        name_len,
        var_node,
        var_width,
        anames,
        aname_start,
        aname_len,
        fnames,
        fname_start,
        fname_len,
        func_width,
        s,
        n1,
        out,
    ) {
        Ok(()) => {}
        Err(e) => return Err(e),
    }
    let m = side.len();
    if s > m || n1 >= m - s {
        return Err(EchoError::Malformed);
    }
    let x = side[s + n1];
    out.push(b' ');
    echo_node(
        nodes,
        bits,
        side,
        ws,
        names,
        name_start,
        name_len,
        var_node,
        var_width,
        anames,
        aname_start,
        aname_len,
        fnames,
        fname_start,
        fname_len,
        func_width,
        x,
        false,
        out,
    )
}

/* ══════════════════ THE SCRIPT ══════════════════ */

/// Declare the variables, in table order:
/// `(declare-const |x| (_ BitVec w))`. `false` for a variable of width 0.
fn decl_vars(
    out: &mut Vec<u8>,
    names: &[u8],
    name_start: &[usize],
    name_len: &[usize],
    var_width: &[usize],
) -> bool {
    let n = name_start.len();
    if name_len.len() != n || var_width.len() != n {
        return false;
    }
    let mut k = 0usize;
    while k < n {
        let w = var_width[k];
        if w == 0 {
            return false;
        }
        push_word(out, b"(declare-const ");
        push_name(out, names, name_start[k], name_len[k]);
        out.push(b' ');
        push_sort(out, w);
        push_word(out, b")\n");
        k += 1;
    }
    true
}

/// Declare the arrays, in table order:
/// `(declare-const |m| (Array (_ BitVec 32) (_ BitVec 8)))`.
fn decl_arrays(
    out: &mut Vec<u8>,
    anames: &[u8],
    aname_start: &[usize],
    aname_len: &[usize],
) -> bool {
    let n = aname_start.len();
    if aname_len.len() != n {
        return false;
    }
    let mut k = 0usize;
    while k < n {
        push_word(out, b"(declare-const ");
        push_name(out, anames, aname_start[k], aname_len[k]);
        push_word(out, b" (Array (_ BitVec 32) (_ BitVec 8)))\n");
        k += 1;
    }
    true
}

/// Append the sorts of the `n` argument nodes from `side[s]`, separated
/// by one space. `false` when an argument is outside the tables or has
/// width 0.
fn push_arg_sorts(out: &mut Vec<u8>, ws: &[usize], side: &[usize], s: usize, n: usize) -> bool {
    let m = side.len();
    if s > m || n > m - s {
        return false;
    }
    let mut j = 0usize;
    while j < n {
        let w = width_at(ws, side[s + j]);
        if w == 0 {
            return false;
        }
        if j > 0 {
            out.push(b' ');
        }
        push_sort(out, w);
        j += 1;
    }
    true
}

/// Declare function `g`, the name `fnames[start .. start + len]` of
/// result width `w`: `(declare-fun |f| (<argument sorts>) (_ BitVec w))`,
/// the argument sorts those of the first call of `g` ([`find_call`]).
/// `false` for a result width 0 or a function no node calls.
#[allow(clippy::too_many_arguments)] // the fragment has no structs to bundle them
fn decl_func(
    out: &mut Vec<u8>,
    nodes: &[ExtNode],
    side: &[usize],
    ws: &[usize],
    fnames: &[u8],
    start: usize,
    len: usize,
    w: usize,
    g: usize,
) -> bool {
    if w == 0 {
        return false;
    }
    let c = find_call(nodes, g);
    if c >= nodes.len() {
        return false;
    }
    let first = nodes[c];
    let (s0, n0) = match call_args(first) {
        Ok(p) => p,
        Err(_) => return false,
    };
    push_word(out, b"(declare-fun ");
    push_name(out, fnames, start, len);
    push_word(out, b" (");
    if !push_arg_sorts(out, ws, side, s0, n0) {
        return false;
    }
    push_word(out, b") ");
    push_sort(out, w);
    push_word(out, b")\n");
    true
}

/// Declare the functions, in table order ([`decl_func`]).
#[allow(clippy::too_many_arguments)] // the fragment has no structs to bundle them
fn decl_funcs(
    out: &mut Vec<u8>,
    nodes: &[ExtNode],
    side: &[usize],
    ws: &[usize],
    fnames: &[u8],
    fname_start: &[usize],
    fname_len: &[usize],
    func_width: &[usize],
) -> bool {
    let n = fname_start.len();
    if fname_len.len() != n || func_width.len() != n {
        return false;
    }
    let mut g = 0usize;
    while g < n {
        if !decl_func(
            out,
            nodes,
            side,
            ws,
            fnames,
            fname_start[g],
            fname_len[g],
            func_width[g],
            g,
        ) {
            return false;
        }
        g += 1;
    }
    true
}

/// Assert the roots, in order: `(assert <root>)`.
#[allow(clippy::too_many_arguments)] // the fragment has no structs to bundle them
fn echo_roots(
    nodes: &[ExtNode],
    bits: &[bool],
    side: &[usize],
    ws: &[usize],
    names: &[u8],
    name_start: &[usize],
    name_len: &[usize],
    var_node: &[usize],
    var_width: &[usize],
    anames: &[u8],
    aname_start: &[usize],
    aname_len: &[usize],
    fnames: &[u8],
    fname_start: &[usize],
    fname_len: &[usize],
    func_width: &[usize],
    roots: &[usize],
    out: &mut Vec<u8>,
) -> Result<(), EchoError> {
    let n = roots.len();
    let mut k = 0usize;
    while k < n {
        push_word(out, b"(assert ");
        match echo_node(
            nodes,
            bits,
            side,
            ws,
            names,
            name_start,
            name_len,
            var_node,
            var_width,
            anames,
            aname_start,
            aname_len,
            fnames,
            fname_start,
            fname_len,
            func_width,
            roots[k],
            true,
            out,
        ) {
            Ok(()) => {}
            Err(e) => return Err(e),
        }
        push_word(out, b")\n");
        k += 1;
    }
    Ok(())
}

/// Append the `set-logic` command: `QF_BV`, `QF_ABV` when the query has
/// arrays, `QF_AUFBV` when it has functions.
fn push_logic(out: &mut Vec<u8>, narrays: usize, nfuncs: usize) {
    push_word(out, b"(set-logic ");
    if nfuncs > 0 {
        push_word(out, b"QF_AUFBV");
    } else if narrays > 0 {
        push_word(out, b"QF_ABV");
    } else {
        push_word(out, b"QF_BV");
    }
    push_word(out, b")\n");
}

/// **The echo of an extended query** (`ordeal-ext/v1`): the node list
/// `nodes` / `bits` / `side` / `roots` with its variable table (`names`,
/// `name_start`, `name_len`, `var_node`, `var_width` — the layout of
/// `term_kernel::Flat`), array table and function table, as an SMT-LIB
/// script. See the module docs for the script and the refusals.
#[allow(clippy::too_many_arguments)] // the fragment has no structs to bundle them
pub fn echo_ext(
    nodes: &[ExtNode],
    bits: &[bool],
    side: &[usize],
    roots: &[usize],
    names: &[u8],
    name_start: &[usize],
    name_len: &[usize],
    var_node: &[usize],
    var_width: &[usize],
    anames: &[u8],
    aname_start: &[usize],
    aname_len: &[usize],
    fnames: &[u8],
    fname_start: &[usize],
    fname_len: &[usize],
    func_width: &[usize],
) -> Result<Vec<u8>, EchoError> {
    let ws = match ext_wf(nodes, bits.len(), side) {
        Ok(ws) => ws,
        Err(_) => return Err(EchoError::Malformed),
    };
    let nv = name_start.len();
    if name_len.len() != nv || var_node.len() != nv || var_width.len() != nv {
        return Err(EchoError::Malformed);
    }
    let na = aname_start.len();
    if aname_len.len() != na {
        return Err(EchoError::Malformed);
    }
    let nf = fname_start.len();
    if fname_len.len() != nf || func_width.len() != nf {
        return Err(EchoError::Malformed);
    }
    let nob: Vec<u8> = Vec::new();
    let noi: Vec<usize> = Vec::new();
    if !table_ok(
        names, name_start, name_len, &nob, &noi, &noi, &nob, &noi, &noi,
    ) {
        return Err(EchoError::Name);
    }
    if !table_ok(
        anames,
        aname_start,
        aname_len,
        names,
        name_start,
        name_len,
        &nob,
        &noi,
        &noi,
    ) {
        return Err(EchoError::Name);
    }
    if !table_ok(
        fnames,
        fname_start,
        fname_len,
        names,
        name_start,
        name_len,
        anames,
        aname_start,
        aname_len,
    ) {
        return Err(EchoError::Name);
    }
    if !unshared(nodes, side, roots) {
        return Err(EchoError::Shared);
    }
    let mut out: Vec<u8> = Vec::new();
    push_logic(&mut out, na, nf);
    if !decl_vars(&mut out, names, name_start, name_len, var_width) {
        return Err(EchoError::Var);
    }
    if !decl_arrays(&mut out, anames, aname_start, aname_len) {
        return Err(EchoError::Malformed);
    }
    if !decl_funcs(
        &mut out,
        nodes,
        side,
        &ws,
        fnames,
        fname_start,
        fname_len,
        func_width,
    ) {
        return Err(EchoError::Signature);
    }
    match echo_roots(
        nodes,
        bits,
        side,
        &ws,
        names,
        name_start,
        name_len,
        var_node,
        var_width,
        anames,
        aname_start,
        aname_len,
        fnames,
        fname_start,
        fname_len,
        func_width,
        roots,
        &mut out,
    ) {
        Ok(()) => {}
        Err(e) => return Err(e),
    }
    push_word(&mut out, b"(check-sat)\n");
    Ok(out)
}

/// The closed node list as an extended one: every node a `Core` node.
fn lift_core(t: &[DagNode]) -> Vec<ExtNode> {
    let mut out: Vec<ExtNode> = Vec::new();
    let n = t.len();
    let mut i = 0usize;
    while i < n {
        let nd = t[i];
        out.push(ExtNode::Core(nd));
        i += 1;
    }
    out
}

/// **The echo of a term** (`ordeal-term/v1`): the node list `t` / `tbits`
/// / `troots` with its variable table, as an SMT-LIB script in `QF_BV` —
/// [`echo_ext`] of the same list with no arrays and no functions.
#[allow(clippy::too_many_arguments)] // the fragment has no structs to bundle them
pub fn echo_term(
    t: &[DagNode],
    tbits: &[bool],
    troots: &[usize],
    names: &[u8],
    name_start: &[usize],
    name_len: &[usize],
    var_node: &[usize],
    var_width: &[usize],
) -> Result<Vec<u8>, EchoError> {
    let nodes = lift_core(t);
    let nob: Vec<u8> = Vec::new();
    let noi: Vec<usize> = Vec::new();
    echo_ext(
        &nodes, tbits, &noi, troots, names, name_start, name_len, var_node, var_width, &nob, &noi,
        &noi, &nob, &noi, &noi, &noi,
    )
}

#[cfg(test)]
mod tests {
    use super::super::term_kernel::{Flat, TArgs, TArray, TBool, TBv, flatten_tree, project_core};
    use super::*;

    fn var(n: &str, w: usize) -> Box<TBv> {
        Box::new(TBv::Var(n.as_bytes().to_vec(), w))
    }

    fn konst(v: u128, w: usize) -> Box<TBv> {
        Box::new(TBv::Const(v, w))
    }

    fn echo_flat(f: &Flat) -> Result<Vec<u8>, EchoError> {
        echo_ext(
            &f.nodes,
            &f.bits,
            &f.side,
            &f.roots,
            &f.names,
            &f.name_start,
            &f.name_len,
            &f.var_node,
            &f.var_width,
            &f.anames,
            &f.aname_start,
            &f.aname_len,
            &f.fnames,
            &f.fname_start,
            &f.fname_len,
            &f.func_width,
        )
    }

    /// The echo of the trees, as text.
    fn text(ts: &[TBool]) -> String {
        let f = flatten_tree(ts).unwrap();
        String::from_utf8(echo_flat(&f).unwrap()).unwrap()
    }

    /// The refusal of the trees.
    fn refusal(ts: &[TBool]) -> Option<EchoError> {
        let f = flatten_tree(ts).unwrap();
        echo_flat(&f).err()
    }

    /// A hand-built closed list with a variable table `(name, node, width)`.
    fn term(
        t: &[DagNode],
        bits: &[bool],
        roots: &[usize],
        vars: &[(&str, usize, usize)],
    ) -> Result<String, EchoError> {
        let mut names: Vec<u8> = Vec::new();
        let mut start = Vec::new();
        let mut len = Vec::new();
        let mut node = Vec::new();
        let mut width = Vec::new();
        for (n, i, w) in vars {
            start.push(names.len());
            len.push(n.len());
            names.extend_from_slice(n.as_bytes());
            node.push(*i);
            width.push(*w);
        }
        match echo_term(t, bits, roots, &names, &start, &len, &node, &width) {
            Ok(b) => Ok(String::from_utf8(b).unwrap()),
            Err(e) => Err(e),
        }
    }

    #[test]
    fn golden_core_script() {
        // x + 5 = 5 + x: the variable and the constant shared, every operator its own node.
        let t = TBool::Eq(
            Box::new(TBv::Add(var("x", 8), konst(5, 8))),
            Box::new(TBv::Add(konst(5, 8), var("x", 8))),
        );
        assert_eq!(
            text(&[t]),
            "(set-logic QF_BV)\n\
             (declare-const |x| (_ BitVec 8))\n\
             (assert (= (bvadd |x| #b00000101) (bvadd #b00000101 |x|)))\n\
             (check-sat)\n"
        );
        // No assertion at all is still a script.
        assert_eq!(text(&[]), "(set-logic QF_BV)\n(check-sat)\n");
    }

    #[test]
    fn golden_one_symbol_per_operator() {
        type Bin = fn(Box<TBv>, Box<TBv>) -> TBv;
        let bins: Vec<(Bin, &str)> = vec![
            (TBv::Add, "bvadd"),
            (TBv::Sub, "bvsub"),
            (TBv::Mul, "bvmul"),
            (TBv::Udiv, "bvudiv"),
            (TBv::Urem, "bvurem"),
            (TBv::And, "bvand"),
            (TBv::Or, "bvor"),
            (TBv::Xor, "bvxor"),
            (TBv::Shl, "bvshl"),
            (TBv::Lshr, "bvlshr"),
            (TBv::Ashr, "bvashr"),
            (TBv::Sdiv, "bvsdiv"),
            (TBv::Srem, "bvsrem"),
        ];
        let mut ts = Vec::new();
        let mut want = String::from(
            "(set-logic QF_BV)\n(declare-const |x| (_ BitVec 12))\n(declare-const |y| (_ BitVec 12))\n",
        );
        for (mk, sym) in &bins {
            ts.push(TBool::Eq(
                Box::new(mk(var("x", 12), var("y", 12))),
                var("x", 12),
            ));
            want.push_str(&format!("(assert (= ({sym} |x| |y|) |x|))\n"));
        }
        type Cmp = fn(Box<TBv>, Box<TBv>) -> TBool;
        let cmps: Vec<(Cmp, &str)> = vec![
            (TBool::Eq, "="),
            (TBool::Ne, "distinct"),
            (TBool::Ult, "bvult"),
            (TBool::Ule, "bvule"),
            (TBool::Ugt, "bvugt"),
            (TBool::Uge, "bvuge"),
            (TBool::Slt, "bvslt"),
            (TBool::Sle, "bvsle"),
            (TBool::Sgt, "bvsgt"),
            (TBool::Sge, "bvsge"),
        ];
        for (mk, sym) in &cmps {
            ts.push(mk(var("x", 12), var("y", 12)));
            want.push_str(&format!("(assert ({sym} |x| |y|))\n"));
        }
        want.push_str("(check-sat)\n");
        assert_eq!(text(&ts), want);
    }

    #[test]
    fn golden_structural_and_boolean_operators() {
        let p = || Box::new(TBool::Ult(var("x", 8), var("y", 8)));
        let ts = vec![
            // not / and / or, nested as built.
            TBool::Not(Box::new(TBool::And(Box::new(TBool::Or(p(), p())), p()))),
            // bvnot / bvneg / concat.
            TBool::Eq(
                Box::new(TBv::Concat(
                    Box::new(TBv::BvNot(var("x", 8))),
                    Box::new(TBv::Neg(var("y", 8))),
                )),
                var("z", 16),
            ),
            // extract and the two extensions carry decimal indices.
            TBool::Eq(
                Box::new(TBv::Extract(15, 8, var("z", 16))),
                Box::new(TBv::Extract(7, 0, Box::new(TBv::ZeroExt(100, var("x", 8))))),
            ),
            TBool::Eq(Box::new(TBv::SignExt(8, var("x", 8))), var("z", 16)),
            // ite: a formula, then two terms.
            TBool::Eq(
                Box::new(TBv::Ite(p(), var("x", 8), var("y", 8))),
                var("x", 8),
            ),
        ];
        assert_eq!(
            text(&ts),
            "(set-logic QF_BV)\n\
             (declare-const |x| (_ BitVec 8))\n\
             (declare-const |y| (_ BitVec 8))\n\
             (declare-const |z| (_ BitVec 16))\n\
             (assert (not (and (or (bvult |x| |y|) (bvult |x| |y|)) (bvult |x| |y|))))\n\
             (assert (= (concat (bvnot |x|) (bvneg |y|)) |z|))\n\
             (assert (= ((_ extract 15 8) |z|) ((_ extract 7 0) ((_ zero_extend 100) |x|))))\n\
             (assert (= ((_ sign_extend 8) |x|) |z|))\n\
             (assert (= (ite (bvult |x| |y|) |x| |y|) |x|))\n\
             (check-sat)\n"
        );
    }

    #[test]
    fn golden_constants_are_msb_first_and_exactly_w_digits() {
        let ts = vec![
            TBool::Eq(var("a", 1), konst(1, 1)),
            // 0x1FF at width 8 is its low 8 bits; 6 at width 5 keeps its leading zeros.
            TBool::Eq(var("b", 8), konst(0x1FF, 8)),
            TBool::Eq(var("c", 5), konst(6, 5)),
            TBool::Eq(var("d", 128), konst(1u128 << 127, 128)),
        ];
        let d = format!("#b1{}", "0".repeat(127));
        assert_eq!(
            text(&ts),
            format!(
                "(set-logic QF_BV)\n\
                 (declare-const |a| (_ BitVec 1))\n\
                 (declare-const |b| (_ BitVec 8))\n\
                 (declare-const |c| (_ BitVec 5))\n\
                 (declare-const |d| (_ BitVec 128))\n\
                 (assert (= |a| #b1))\n\
                 (assert (= |b| #b11111111))\n\
                 (assert (= |c| #b00110))\n\
                 (assert (= |d| {d}))\n\
                 (check-sat)\n"
            )
        );
    }

    #[test]
    fn golden_rotates_are_indexed_modulo_the_width() {
        let ts = vec![
            // 11 mod 8 = 3; 7 mod 5 = 2; 0 stays 0; 2^100 + 5 mod 128 = 5.
            TBool::Eq(Box::new(TBv::Rotr(var("x", 8), konst(11, 8))), var("x", 8)),
            TBool::Eq(Box::new(TBv::Rotl(var("y", 5), konst(7, 5))), var("y", 5)),
            TBool::Eq(Box::new(TBv::Rotl(var("x", 8), konst(0, 8))), var("x", 8)),
            TBool::Eq(
                Box::new(TBv::Rotr(var("z", 128), konst((1u128 << 100) + 5, 128))),
                var("z", 128),
            ),
        ];
        assert_eq!(
            text(&ts),
            "(set-logic QF_BV)\n\
             (declare-const |x| (_ BitVec 8))\n\
             (declare-const |y| (_ BitVec 5))\n\
             (declare-const |z| (_ BitVec 128))\n\
             (assert (= ((_ rotate_right 3) |x|) |x|))\n\
             (assert (= ((_ rotate_left 2) |y|) |y|))\n\
             (assert (= ((_ rotate_left 0) |x|) |x|))\n\
             (assert (= ((_ rotate_right 5) |z|) |z|))\n\
             (check-sat)\n"
        );
        // A rotate by a term is refused (the API path only).
        let t = TBool::Eq(Box::new(TBv::Rotr(var("x", 8), var("k", 8))), var("x", 8));
        assert_eq!(refusal(&[t]), Some(EchoError::Rotate));
    }

    #[test]
    fn golden_arrays_and_functions() {
        // select(store(store(m, i, v), j, u), k): the chain nests, the innermost store first in the text.
        let chain = TArray::Store(
            Box::new(TArray::Store(
                Box::new(TArray::Var(b"m".to_vec())),
                var("i", 32),
                var("v", 8),
            )),
            var("j", 32),
            var("u", 8),
        );
        let sel = TBool::Eq(
            Box::new(TBv::Select(Box::new(chain), var("k", 32))),
            konst(0, 8),
        );
        assert_eq!(
            text(&[sel]),
            "(set-logic QF_ABV)\n\
             (declare-const |k| (_ BitVec 32))\n\
             (declare-const |j| (_ BitVec 32))\n\
             (declare-const |u| (_ BitVec 8))\n\
             (declare-const |i| (_ BitVec 32))\n\
             (declare-const |v| (_ BitVec 8))\n\
             (declare-const |m| (Array (_ BitVec 32) (_ BitVec 8)))\n\
             (assert (= (select (store (store |m| |i| |v|) |j| |u|) |k|) #b00000000))\n\
             (check-sat)\n"
        );
        // A base read, a binary call, a nullary call.
        let args = TArgs::Cons(
            var("x", 8),
            Box::new(TArgs::Cons(var("i", 32), Box::new(TArgs::Nil))),
        );
        let ts = vec![
            TBool::Eq(
                Box::new(TBv::Call(b"f".to_vec(), 16, Box::new(args))),
                Box::new(TBv::Call(b"g".to_vec(), 16, Box::new(TArgs::Nil))),
            ),
            TBool::Eq(
                Box::new(TBv::Select(
                    Box::new(TArray::Var(b"m".to_vec())),
                    var("i", 32),
                )),
                var("x", 8),
            ),
        ];
        assert_eq!(
            text(&ts),
            "(set-logic QF_AUFBV)\n\
             (declare-const |x| (_ BitVec 8))\n\
             (declare-const |i| (_ BitVec 32))\n\
             (declare-const |m| (Array (_ BitVec 32) (_ BitVec 8)))\n\
             (declare-fun |f| ((_ BitVec 8) (_ BitVec 32)) (_ BitVec 16))\n\
             (declare-fun |g| () (_ BitVec 16))\n\
             (assert (= (|f| |x| |i|) |g|))\n\
             (assert (= (select |m| |i|) |x|))\n\
             (check-sat)\n"
        );
    }

    #[test]
    fn names_are_always_quoted_and_verus_names_pass() {
        let t = TBool::Ult(var("%%location_label%%0", 8), var("cpu_id!", 8));
        assert_eq!(
            text(&[t]),
            "(set-logic QF_BV)\n\
             (declare-const |%%location_label%%0| (_ BitVec 8))\n\
             (declare-const |cpu_id!| (_ BitVec 8))\n\
             (assert (bvult |%%location_label%%0| |cpu_id!|))\n\
             (check-sat)\n"
        );
        // A space, a digit start and a parenthesis are all fine inside the bars.
        let t = TBool::Ult(var("a b", 8), var("0(x)", 8));
        assert!(text(&[t]).contains("(assert (bvult |a b| |0(x)|))"));
    }

    #[test]
    fn refuses_bad_reserved_and_colliding_names() {
        let lt = |a: &str| TBool::Ult(var(a, 8), konst(1, 8));
        for bad in ["", "a|b", "a\\b", "tab\tx", "nl\nx", "del\x7f", "é"] {
            assert_eq!(refusal(&[lt(bad)]), Some(EchoError::Name), "{bad:?}");
        }
        // |let| is the symbol let: reserved words and theory symbols are refused.
        for bad in [
            "let",
            "_",
            "!",
            "par",
            "assert",
            "check-sat",
            "set-logic",
            "declare-fun",
            "true",
            "false",
            "not",
            "and",
            "=",
            "ite",
            "bvadd",
            "bvsle",
            "concat",
            "extract",
            "select",
            "store",
            "Array",
            "BitVec",
            "Bool",
            "QF_BV",
            "rotate_left",
            "bvsmod",
            "get-model",
        ] {
            assert_eq!(refusal(&[lt(bad)]), Some(EchoError::Name), "{bad:?}");
        }
        // Near misses are names.
        for good in ["Let", "let_", "bvadd1", "x", "assertion", "=="] {
            assert_eq!(refusal(&[lt(good)]), None, "{good:?}");
        }
        // One namespace: a variable and an array, a variable and a function,
        // an array and a function may not share a name.
        let arr = |a: &str, i: &str| {
            TBool::Eq(
                Box::new(TBv::Select(
                    Box::new(TArray::Var(a.as_bytes().to_vec())),
                    var(i, 32),
                )),
                konst(0, 8),
            )
        };
        let call = |f: &str| {
            TBool::Eq(
                Box::new(TBv::Call(f.as_bytes().to_vec(), 8, Box::new(TArgs::Nil))),
                konst(0, 8),
            )
        };
        assert_eq!(refusal(&[arr("m", "m")]), Some(EchoError::Name));
        assert_eq!(refusal(&[lt("f"), call("f")]), Some(EchoError::Name));
        assert_eq!(refusal(&[arr("m", "i"), call("m")]), Some(EchoError::Name));
        assert_eq!(refusal(&[arr("m", "i"), call("f")]), None);
        // Two table entries with one name (a crafted table: the flattener never builds one).
        let t = [DagNode::Var(8), DagNode::Var(8), DagNode::Ult(0, 1)];
        assert_eq!(
            term(&t, &[], &[2], &[("x", 0, 8), ("x", 1, 8)]),
            Err(EchoError::Name)
        );
        assert!(term(&t, &[], &[2], &[("x", 0, 8), ("y", 1, 8)]).is_ok());
    }

    #[test]
    fn refuses_a_sort_mismatch() {
        // A bitvector node asserted; a formula where a term is expected; a
        // term where a formula is expected. All are well formed for `ext_wf`
        // (a formula is a one-bit word there), none is SMT-LIB.
        let vars = [("x", 0, 1), ("y", 1, 1)];
        let t = [DagNode::Var(1), DagNode::Var(1), DagNode::Eq(0, 1)];
        assert_eq!(term(&t, &[], &[0], &vars), Err(EchoError::Sort));
        let t = [
            DagNode::Var(1),
            DagNode::Var(1),
            DagNode::Eq(0, 1),
            DagNode::Add(2, 0),
            DagNode::Eq(3, 1),
        ];
        assert_eq!(term(&t, &[], &[4], &vars), Err(EchoError::Sort));
        let t = [DagNode::Var(1), DagNode::Var(1), DagNode::BoolAnd(0, 1)];
        assert_eq!(term(&t, &[], &[2], &vars), Err(EchoError::Sort));
        let t = [DagNode::Var(1), DagNode::Not(0)];
        assert_eq!(term(&t, &[], &[1], &vars[..1]), Err(EchoError::Sort));
        let t = [
            DagNode::Var(1),
            DagNode::Var(1),
            DagNode::Ite(0, 0, 1),
            DagNode::Eq(2, 1),
        ];
        assert_eq!(term(&t, &[], &[3], &vars), Err(EchoError::Sort));
    }

    #[test]
    fn refuses_an_unnamed_variable_and_a_malformed_list() {
        let t = [DagNode::Var(8), DagNode::Var(8), DagNode::Ult(0, 1)];
        // Node 1 has no table entry; node 1 at another width; a table variable of width 0.
        assert_eq!(term(&t, &[], &[2], &[("x", 0, 8)]), Err(EchoError::Var));
        assert_eq!(
            term(&t, &[], &[2], &[("x", 0, 8), ("y", 1, 16)]),
            Err(EchoError::Var)
        );
        assert_eq!(
            term(&t, &[], &[2], &[("x", 0, 8), ("y", 1, 8), ("z", 7, 0)]),
            Err(EchoError::Var)
        );
        // An entry naming no node is declared and unused.
        assert_eq!(
            term(&t, &[], &[2], &[("x", 0, 8), ("y", 1, 8), ("z", 9, 4)]).unwrap(),
            "(set-logic QF_BV)\n\
             (declare-const |x| (_ BitVec 8))\n\
             (declare-const |y| (_ BitVec 8))\n\
             (declare-const |z| (_ BitVec 4))\n\
             (assert (bvult |x| |y|))\n\
             (check-sat)\n"
        );
        // Not well formed: a forward operand, disagreeing widths, a root past the list,
        // a constant outside the bit table.
        let vars = [("x", 0, 8), ("y", 1, 8)];
        let fwd = [DagNode::Var(8), DagNode::Ult(0, 2), DagNode::Var(8)];
        assert_eq!(term(&fwd, &[], &[1], &vars), Err(EchoError::Malformed));
        let wid = [DagNode::Var(8), DagNode::Var(9), DagNode::Ult(0, 1)];
        assert_eq!(term(&wid, &[], &[2], &vars), Err(EchoError::Malformed));
        assert_eq!(term(&t, &[], &[3], &vars), Err(EchoError::Malformed));
        let cst = [DagNode::Var(8), DagNode::Const(0, 8), DagNode::Ult(0, 1)];
        assert_eq!(
            term(&cst, &[true; 7], &[2], &vars[..1]),
            Err(EchoError::Malformed)
        );
        // Table columns of different lengths.
        assert_eq!(
            echo_term(&t, &[], &[2], b"xy", &[0, 1], &[1, 1], &[0, 1], &[8]),
            Err(EchoError::Malformed)
        );
        // A name range outside the arena is not a name.
        assert_eq!(
            echo_term(&t, &[], &[2], b"xy", &[0, 1], &[1, 2], &[0, 1], &[8, 8]),
            Err(EchoError::Name)
        );
    }

    #[test]
    fn refuses_a_shared_operator_node() {
        let vars = [("x", 0, 8), ("y", 1, 8)];
        // (x + y) used by two parents: a hash-consed list.
        let t = [
            DagNode::Var(8),
            DagNode::Var(8),
            DagNode::Add(0, 1),
            DagNode::Mul(2, 2),
            DagNode::Eq(3, 0),
        ];
        assert_eq!(term(&t, &[], &[4], &vars), Err(EchoError::Shared));
        let t = [
            DagNode::Var(8),
            DagNode::Var(8),
            DagNode::Add(0, 1),
            DagNode::Ult(2, 0),
            DagNode::Ult(2, 1),
        ];
        assert_eq!(term(&t, &[], &[3, 4], &vars), Err(EchoError::Shared));
        // One node asserted twice.
        let t = [DagNode::Var(8), DagNode::Var(8), DagNode::Ult(0, 1)];
        assert_eq!(term(&t, &[], &[2, 2], &vars), Err(EchoError::Shared));
        // Leaves are shared freely.
        let t = [
            DagNode::Var(8),
            DagNode::Const(0, 8),
            DagNode::Add(0, 1),
            DagNode::Add(1, 0),
            DagNode::Eq(2, 3),
        ];
        assert!(term(&t, &[false; 8], &[4], &vars[..1]).is_ok());
        // A 40-level doubling chain is refused instead of echoed at 2^40 leaves.
        let mut t = vec![DagNode::Var(8)];
        for i in 0..40 {
            t.push(DagNode::Add(i, i));
        }
        t.push(DagNode::Eq(40, 0));
        assert_eq!(term(&t, &[], &[41], &vars[..1]), Err(EchoError::Shared));
    }

    #[test]
    fn refuses_an_inconsistent_function_signature() {
        let call = |args: TArgs, w: usize| Box::new(TBv::Call(b"f".to_vec(), w, Box::new(args)));
        let one = |a: Box<TBv>| TArgs::Cons(a, Box::new(TArgs::Nil));
        let two = |a: Box<TBv>, b: Box<TBv>| TArgs::Cons(a, Box::new(one(b)));
        // Two arities, then two argument widths: the flattener checks only the result width.
        let t = TBool::Eq(
            call(one(var("x", 8)), 8),
            call(two(var("x", 8), var("x", 8)), 8),
        );
        assert_eq!(refusal(&[t]), Some(EchoError::Signature));
        let t = TBool::Eq(call(one(var("x", 8)), 8), call(one(var("y", 16)), 8));
        assert_eq!(refusal(&[t]), Some(EchoError::Signature));
        let t = TBool::Eq(call(one(var("x", 8)), 8), call(one(var("z", 8)), 8));
        assert_eq!(refusal(&[t]), None);
        let run = |nodes: &[ExtNode], fw: &[usize], fs: &[usize], fl: &[usize]| {
            echo_ext(
                nodes,
                &[],
                &[1],
                &[3],
                b"x",
                &[0],
                &[1],
                &[0],
                &[1],
                b"",
                &[],
                &[],
                b"fg",
                fs,
                fl,
                fw,
            )
        };
        // A formula as an argument is a sort error.
        let nodes = [
            ExtNode::Core(DagNode::Var(1)),
            ExtNode::Core(DagNode::Eq(0, 0)),
            ExtNode::Call(0, 1, 0, 1),
            ExtNode::Core(DagNode::Eq(2, 0)),
        ];
        assert_eq!(run(&nodes, &[1], &[0], &[1]), Err(EchoError::Sort));
        // The table's result width disagrees with the call; a function no node calls.
        let nodes = [
            ExtNode::Core(DagNode::Var(1)),
            ExtNode::Core(DagNode::Var(1)),
            ExtNode::Call(0, 1, 0, 1),
            ExtNode::Core(DagNode::Eq(2, 0)),
        ];
        assert_eq!(run(&nodes, &[2], &[0], &[1]), Err(EchoError::Signature));
        assert_eq!(
            run(&nodes, &[1, 1], &[0, 1], &[1, 1]),
            Err(EchoError::Signature)
        );
        // A call outside the function table.
        assert_eq!(run(&nodes, &[], &[], &[]), Err(EchoError::Malformed));
    }

    #[test]
    fn the_term_echo_is_the_extended_echo_of_a_closed_list() {
        let t = TBool::Ule(
            Box::new(TBv::Mul(var("x", 32), konst(3, 32))),
            Box::new(TBv::Lshr(var("y", 32), konst(1, 32))),
        );
        let f = flatten_tree(&[t]).unwrap();
        let core = project_core(&f.nodes).unwrap();
        let a = echo_term(
            &core,
            &f.bits,
            &f.roots,
            &f.names,
            &f.name_start,
            &f.name_len,
            &f.var_node,
            &f.var_width,
        )
        .unwrap();
        assert_eq!(a, echo_flat(&f).unwrap());
        assert!(a.starts_with(b"(set-logic QF_BV)\n"));
    }

    #[test]
    fn decimal_numerals_have_no_leading_zeros() {
        for (n, want) in [
            (0usize, "0"),
            (7, "7"),
            (9, "9"),
            (10, "10"),
            (32, "32"),
            (99, "99"),
            (100, "100"),
            (128, "128"),
            (65536, "65536"),
            (1234567890, "1234567890"),
            (usize::MAX, "18446744073709551615"),
        ] {
            let mut out = Vec::new();
            push_dec(&mut out, n);
            assert_eq!(String::from_utf8(out).unwrap(), want);
        }
    }

    #[test]
    fn the_echo_is_linear_in_a_deep_unshared_chain() {
        // x + 1 + 1 + … (200 levels): every operator its own node.
        let mut t = var("x", 8);
        for _ in 0..200 {
            t = Box::new(TBv::Add(t, konst(1, 8)));
        }
        let s = text(&[TBool::Eq(t, var("x", 8))]);
        assert_eq!(s.matches("(bvadd ").count(), 200);
        assert_eq!(s.matches("#b00000001").count(), 200);
    }
}
