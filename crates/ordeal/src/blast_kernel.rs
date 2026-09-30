//! Aeneas-friendly model of the bit-blaster (issue #68, v0.15.0 — the
//! assurance capstone).
//!
//! This mirrors what `crates/ordeal-lrat/src/kernel.rs` does for the checker:
//! a self-contained Rust model, written in the translatable subset Charon +
//! Aeneas accept (no `HashMap`, no interior mutability, no trait objects), that
//! captures the **correctness content** of the real bit-blaster. `lean/regen.sh`
//! Aeneas-translates it into `lean/Blaster.lean`, and `lean/Blaster.lean`'s
//! proofs establish that each rule equals the formal `BitVec` semantics for
//! ALL widths — the unbounded evidence that replaces the Kani-bounded harnesses.
//!
//! Fidelity note: the real `aig.rs` adds structural hashing (a `HashMap`) as a
//! *performance* optimization — it changes which gates are shared, never what a
//! gate computes. This model omits it: a functional append-only AIG evaluated
//! by a forward fold has the same input→output function, which is all the
//! correctness proof needs. The blast rules themselves (`blast/bitwise.rs`) are
//! already in the translatable subset and are mirrored here verbatim in spirit.

/// A literal: an AIG node index plus a negation flag. Mirrors `aig::Lit`.
#[derive(Clone, Copy)]
pub struct Lit {
    pub node: usize,
    pub neg: bool,
}

/// An AIG node. `Input` is a primary input (the k-th); `And` is a two-input
/// AND gate over earlier literals. Constants are modelled as node 0 = FALSE.
#[derive(Clone, Copy)]
pub enum Node {
    False,
    Input(usize),
    And(Lit, Lit),
}

/// An and-inverter graph: an append-only vector of nodes. Node 0 is always
/// `False` (so `Lit { node: 0, neg: true }` is TRUE), matching `aig.rs`.
pub struct Aig {
    pub nodes: Vec<Node>,
}

/// The constant-false literal.
pub fn lit_false() -> Lit {
    Lit {
        node: 0,
        neg: false,
    }
}

/// The constant-true literal.
pub fn lit_true() -> Lit {
    Lit { node: 0, neg: true }
}

/// Negate a literal.
pub fn lit_not(l: Lit) -> Lit {
    Lit {
        node: l.node,
        neg: !l.neg,
    }
}

/// A fresh AIG with just the constant node.
///
/// The `Vec::new` + `push` form is deliberate: Charon/Aeneas translate this
/// subset cleanly, but the `vec![]` macro clippy suggests is not in it — the
/// whole file must stay in the translatable fragment (see the module docs).
#[allow(clippy::vec_init_then_push)]
pub fn aig_new() -> Aig {
    let mut nodes: Vec<Node> = Vec::new();
    nodes.push(Node::False);
    Aig { nodes }
}

/// Add a primary input, returning its literal.
pub fn push_input(aig: &mut Aig, k: usize) -> Lit {
    let idx = aig.nodes.len();
    aig.nodes.push(Node::Input(k));
    Lit {
        node: idx,
        neg: false,
    }
}

/// Add an AND gate over `x` and `y`, returning its literal. No strashing:
/// correctness does not depend on gate sharing.
pub fn push_and(aig: &mut Aig, x: Lit, y: Lit) -> Lit {
    let idx = aig.nodes.len();
    aig.nodes.push(Node::And(x, y));
    Lit {
        node: idx,
        neg: false,
    }
}

/// OR via De Morgan: `x | y = !(!x & !y)`. Matches `aig::or`.
pub fn push_or(aig: &mut Aig, x: Lit, y: Lit) -> Lit {
    let na = push_and(aig, lit_not(x), lit_not(y));
    lit_not(na)
}

/// XOR: `(x | y) & !(x & y)`. Matches `aig::xor`.
pub fn push_xor(aig: &mut Aig, x: Lit, y: Lit) -> Lit {
    let o = push_or(aig, x, y);
    let a = push_and(aig, x, y);
    push_and(aig, o, lit_not(a))
}

/// Evaluate a literal under a primary-input assignment, given the values
/// already computed for every earlier node. `vals[i]` is node `i`'s value.
pub fn eval_lit(vals: &[bool], l: Lit) -> bool {
    let v = vals[l.node];
    if l.neg { !v } else { v }
}

/// Simulate the whole AIG under a primary-input assignment, returning each
/// node's value. A forward fold: node `i`'s value depends only on earlier
/// nodes (append-only construction guarantees this), so one pass suffices.
pub fn simulate(aig: &Aig, inputs: &[bool]) -> Vec<bool> {
    let mut vals: Vec<bool> = Vec::new();
    let n = aig.nodes.len();
    let mut i = 0usize;
    while i < n {
        let node = aig.nodes[i];
        let v = match node {
            Node::False => false,
            Node::Input(k) => inputs[k],
            Node::And(x, y) => {
                let vx = eval_lit(&vals, x);
                let vy = eval_lit(&vals, y);
                vx && vy
            }
        };
        vals.push(v);
        i += 1;
    }
    vals
}

/// `bvand` — per-bit AND over two equal-width words. Mirrors
/// `blast/bitwise.rs::blast_and`.
pub fn blast_and(aig: &mut Aig, a: &[Lit], b: &[Lit]) -> Vec<Lit> {
    let mut out: Vec<Lit> = Vec::new();
    let w = a.len();
    let mut i = 0usize;
    while i < w {
        let g = push_and(aig, a[i], b[i]);
        out.push(g);
        i += 1;
    }
    out
}

/// `bvor` — per-bit OR.
pub fn blast_or(aig: &mut Aig, a: &[Lit], b: &[Lit]) -> Vec<Lit> {
    let mut out: Vec<Lit> = Vec::new();
    let w = a.len();
    let mut i = 0usize;
    while i < w {
        let g = push_or(aig, a[i], b[i]);
        out.push(g);
        i += 1;
    }
    out
}

/// `bvxor` — per-bit XOR.
pub fn blast_xor(aig: &mut Aig, a: &[Lit], b: &[Lit]) -> Vec<Lit> {
    let mut out: Vec<Lit> = Vec::new();
    let w = a.len();
    let mut i = 0usize;
    while i < w {
        let g = push_xor(aig, a[i], b[i]);
        out.push(g);
        i += 1;
    }
    out
}

/// Ripple-carry chain over equal-width words: returns the truncated sum and
/// the final carry-out. Mirrors `blast/arith.rs::ripple_carry`. Per bit:
/// `sum_i = a_i ^ b_i ^ carry`, `carry' = (a_i & b_i) | (carry & (a_i ^ b_i))`.
pub fn ripple_carry(aig: &mut Aig, a: &[Lit], b: &[Lit], carry_in: Lit) -> (Vec<Lit>, Lit) {
    let mut carry = carry_in;
    let mut sum: Vec<Lit> = Vec::new();
    let w = a.len();
    let mut i = 0usize;
    while i < w {
        let p = push_xor(aig, a[i], b[i]);
        let s = push_xor(aig, p, carry);
        sum.push(s);
        let g = push_and(aig, a[i], b[i]);
        let t = push_and(aig, p, carry);
        carry = push_or(aig, g, t);
        i += 1;
    }
    (sum, carry)
}

/// `bvadd` — ripple-carry adder, carry-in 0. Mirrors `blast/arith.rs::blast_add`.
pub fn blast_add(aig: &mut Aig, a: &[Lit], b: &[Lit]) -> Vec<Lit> {
    let (sum, _carry) = ripple_carry(aig, a, b, lit_false());
    sum
}

/// The word with every literal complemented (for two's-complement subtract).
pub fn word_not(a: &[Lit]) -> Vec<Lit> {
    let mut out: Vec<Lit> = Vec::new();
    let w = a.len();
    let mut i = 0usize;
    while i < w {
        out.push(lit_not(a[i]));
        i += 1;
    }
    out
}

/// `bvsub` — two's complement: `a + !b + 1`. Mirrors `blast/arith.rs::blast_sub`.
pub fn blast_sub(aig: &mut Aig, a: &[Lit], b: &[Lit]) -> Vec<Lit> {
    let not_b = word_not(b);
    let (sum, _carry) = ripple_carry(aig, a, &not_b, lit_true());
    sum
}

/// `bvult` — unsigned less-than: the borrow of `a - b`, i.e. the complement
/// of the carry-out of `a + !b + 1`. Mirrors `blast/arith.rs::blast_ult`.
pub fn blast_ult(aig: &mut Aig, a: &[Lit], b: &[Lit]) -> Lit {
    let not_b = word_not(b);
    let (_sum, carry) = ripple_carry(aig, a, &not_b, lit_true());
    lit_not(carry)
}

/// `bvule` — `a <= b` iff not `b < a`. Mirrors `blast/arith.rs::blast_ule`.
pub fn blast_ule(aig: &mut Aig, a: &[Lit], b: &[Lit]) -> Lit {
    let lt = blast_ult(aig, b, a);
    lit_not(lt)
}

/// `bvugt` — `a > b` iff `b < a`.
pub fn blast_ugt(aig: &mut Aig, a: &[Lit], b: &[Lit]) -> Lit {
    blast_ult(aig, b, a)
}

/// `bvuge` — `a >= b` iff not `a < b`.
pub fn blast_uge(aig: &mut Aig, a: &[Lit], b: &[Lit]) -> Lit {
    let lt = blast_ult(aig, a, b);
    lit_not(lt)
}

/// The word with its most significant (sign) bit complemented. Mirrors
/// `blast/arith.rs::flip_sign`.
pub fn flip_sign(a: &[Lit]) -> Vec<Lit> {
    let mut out: Vec<Lit> = Vec::new();
    let w = a.len();
    let mut i = 0usize;
    while i < w {
        if i + 1 == w {
            out.push(lit_not(a[i]));
        } else {
            out.push(a[i]);
        }
        i += 1;
    }
    out
}

/// `bvslt` — signed: unsigned compare with both sign bits flipped (the
/// order-embedding of two's complement into unsigned).
pub fn blast_slt(aig: &mut Aig, a: &[Lit], b: &[Lit]) -> Lit {
    let fa = flip_sign(a);
    let fb = flip_sign(b);
    blast_ult(aig, &fa, &fb)
}

/// `bvsle` — `a <=s b` iff not `b <s a`.
pub fn blast_sle(aig: &mut Aig, a: &[Lit], b: &[Lit]) -> Lit {
    let lt = blast_slt(aig, b, a);
    lit_not(lt)
}

/// `bvsgt` — `a >s b` iff `b <s a`.
pub fn blast_sgt(aig: &mut Aig, a: &[Lit], b: &[Lit]) -> Lit {
    blast_slt(aig, b, a)
}

/// `bvsge` — `a >=s b` iff not `a <s b`.
pub fn blast_sge(aig: &mut Aig, a: &[Lit], b: &[Lit]) -> Lit {
    let lt = blast_slt(aig, a, b);
    lit_not(lt)
}

/// `=` — conjunction of per-bit XNORs. Mirrors `blast/bitwise.rs::blast_eq`.
pub fn blast_eq(aig: &mut Aig, a: &[Lit], b: &[Lit]) -> Lit {
    let mut acc = lit_true();
    let w = a.len();
    let mut i = 0usize;
    while i < w {
        let x = push_xor(aig, a[i], b[i]);
        let bit_eq = lit_not(x);
        acc = push_and(aig, acc, bit_eq);
        i += 1;
    }
    acc
}

/// `distinct` — negation of equality.
pub fn blast_ne(aig: &mut Aig, a: &[Lit], b: &[Lit]) -> Lit {
    let eq = blast_eq(aig, a, b);
    lit_not(eq)
}

/// Per-bit mux: `sel ? t : e = (sel & t) | (!sel & e)`. Mirrors `aig::mux`.
pub fn push_mux(aig: &mut Aig, sel: Lit, t: Lit, e: Lit) -> Lit {
    let then_b = push_and(aig, sel, t);
    let else_b = push_and(aig, lit_not(sel), e);
    push_or(aig, then_b, else_b)
}

/// `ite` (bool -> BV bridge) — per-bit mux on the condition literal.
pub fn blast_ite(aig: &mut Aig, cond: Lit, then_: &[Lit], else_: &[Lit]) -> Vec<Lit> {
    let mut out: Vec<Lit> = Vec::new();
    let w = then_.len();
    let mut i = 0usize;
    while i < w {
        let m = push_mux(aig, cond, then_[i], else_[i]);
        out.push(m);
        i += 1;
    }
    out
}

/// `extract[hi:lo]` (inclusive) — slice of the LSB-first word. No gates.
pub fn blast_extract(a: &[Lit], hi: usize, lo: usize) -> Vec<Lit> {
    let mut out: Vec<Lit> = Vec::new();
    let mut i = lo;
    while i <= hi {
        out.push(a[i]);
        i += 1;
    }
    out
}

/// `concat` — SMT-LIB: the FIRST operand becomes the high bits; LSB-first
/// words, so the low part comes first. No gates.
pub fn blast_concat(hi_part: &[Lit], lo_part: &[Lit]) -> Vec<Lit> {
    let mut out: Vec<Lit> = Vec::new();
    let wl = lo_part.len();
    let mut i = 0usize;
    while i < wl {
        out.push(lo_part[i]);
        i += 1;
    }
    let wh = hi_part.len();
    let mut j = 0usize;
    while j < wh {
        out.push(hi_part[j]);
        j += 1;
    }
    out
}

/// `zero_ext` — append `by` FALSE literals above the MSB. No gates.
pub fn blast_zero_ext(a: &[Lit], by: usize) -> Vec<Lit> {
    let mut out: Vec<Lit> = Vec::new();
    let w = a.len();
    let mut i = 0usize;
    while i < w {
        out.push(a[i]);
        i += 1;
    }
    let mut j = 0usize;
    while j < by {
        out.push(lit_false());
        j += 1;
    }
    out
}

/// `sign_ext` — replicate the sign (MSB) literal `by` times. No gates.
pub fn blast_sign_ext(a: &[Lit], by: usize) -> Vec<Lit> {
    let mut out: Vec<Lit> = Vec::new();
    let w = a.len();
    let mut i = 0usize;
    while i < w {
        out.push(a[i]);
        i += 1;
    }
    let sign = a[w - 1];
    let mut j = 0usize;
    while j < by {
        out.push(sign);
        j += 1;
    }
    out
}

/// Barrel stages for a width `w >= 1`, and whether `w` is a power of two.
/// Mirrors `blast/shift.rs::stage_count` — `ceil(log2 w)`, the bit length
/// of `w - 1`, which the real blaster spells `usize::BITS - (w - 1)
/// .leading_zeros()`; `leading_zeros` has no Aeneas model, so the mirror
/// halves `w - 1` to zero and counts the rounds. `w` is a power of two
/// exactly when every bit of `w - 1` below that length is set (`w - 1 =
/// 2^stages - 1`), which the same loop records — the real `blast_rotr`
/// tests `w.is_power_of_two()`. Stage `k` shifts by `2^k`, `2^(stages-1)
/// < w <= 2^stages`, so `stages <= w` and no stage exceeds the width
/// (issue #201; the Lean spec `stage_count_spec` proves all of this).
pub fn stage_count(w: usize) -> (usize, bool) {
    let mut t = w - 1;
    let mut stages = 0usize;
    let mut pow2 = true;
    while t > 0 {
        // `% 2 == 1`, not `is_multiple_of`: that std call has no Aeneas
        // model (it would extract as an opaque `axiom`, which CI rejects).
        pow2 = pow2 && t % 2 == 1;
        t /= 2;
        stages += 1;
    }
    (stages, pow2)
}

/// The `w`-bit constant word for `value` (bit `k` is `value`'s bit `k`,
/// LSB first, as TRUE / FALSE literals). Mirrors `aig::word_const`; the
/// bits are peeled off with `% 2` / `/ 2` (no shifts, so no width limit
/// and nothing outside the Aeneas fragment). No gates.
pub fn word_const(value: usize, w: usize) -> Vec<Lit> {
    let mut out: Vec<Lit> = Vec::new();
    let mut v = value;
    let mut k = 0usize;
    while k < w {
        if v % 2 == 1 {
            out.push(lit_true());
        } else {
            out.push(lit_false());
        }
        v /= 2;
        k += 1;
    }
    out
}

/// `amount >= 2^stages`: OR of the amount bits above the barrel stages.
/// Together with the barrel itself (which shifts everything out for any
/// combined amount in `w..2^stages`) this realises `amount >= w`. Mirrors
/// `blast/shift.rs::out_of_range`.
pub fn out_of_range(aig: &mut Aig, b: &[Lit], stages: usize) -> Lit {
    let mut acc = lit_false();
    let w = b.len();
    let mut i = stages;
    while i < w {
        acc = push_or(aig, acc, b[i]);
        i += 1;
    }
    acc
}

/// One barrel stage of a RIGHT shift by `2^k` gated on `sel`: bit i becomes
/// `mux(sel, cur[i + 2^k] (or fill), cur[i])`.
pub fn barrel_right_stage(aig: &mut Aig, cur: &[Lit], sel: Lit, s: usize, fill: Lit) -> Vec<Lit> {
    let w = cur.len();
    let mut next: Vec<Lit> = Vec::new();
    let mut i = 0usize;
    while i < w {
        let shifted = if i + s < w { cur[i + s] } else { fill };
        let m = push_mux(aig, sel, shifted, cur[i]);
        next.push(m);
        i += 1;
    }
    next
}

/// Barrel right-shifter with SMT-LIB out-of-range semantics:
/// `ceil(log2 w)` mux-stages then an all-`fill` mux on out-of-range.
/// Mirrors `blast/shift.rs::barrel_right` at every width `w >= 1`.
pub fn barrel_right(aig: &mut Aig, a: &[Lit], b: &[Lit], fill: Lit) -> Vec<Lit> {
    let mut cur: Vec<Lit> = Vec::new();
    let w = a.len();
    let (stages, _pow2) = stage_count(w);
    let mut i = 0usize;
    while i < w {
        cur.push(a[i]);
        i += 1;
    }
    let mut k = 0usize;
    while k < stages {
        let s = 1usize << k;
        cur = barrel_right_stage(aig, &cur, b[k], s, fill);
        k += 1;
    }
    let oor = out_of_range(aig, b, stages);
    let mut out: Vec<Lit> = Vec::new();
    let mut j = 0usize;
    while j < w {
        let m = push_mux(aig, oor, fill, cur[j]);
        out.push(m);
        j += 1;
    }
    out
}

/// One barrel stage of a LEFT shift by `2^k` gated on `sel`: bit i becomes
/// `mux(sel, cur[i - 2^k] (or FALSE), cur[i])`.
pub fn barrel_left_stage(aig: &mut Aig, cur: &[Lit], sel: Lit, s: usize) -> Vec<Lit> {
    let w = cur.len();
    let mut next: Vec<Lit> = Vec::new();
    let mut i = 0usize;
    while i < w {
        let shifted = if i >= s { cur[i - s] } else { lit_false() };
        let m = push_mux(aig, sel, shifted, cur[i]);
        next.push(m);
        i += 1;
    }
    next
}

/// `bvshl` — barrel left-shifter; zero when the amount is >= width.
/// Mirrors `blast/shift.rs::blast_shl` at every width `w >= 1`.
pub fn blast_shl(aig: &mut Aig, a: &[Lit], b: &[Lit]) -> Vec<Lit> {
    let mut cur: Vec<Lit> = Vec::new();
    let w = a.len();
    let (stages, _pow2) = stage_count(w);
    let mut i = 0usize;
    while i < w {
        cur.push(a[i]);
        i += 1;
    }
    let mut k = 0usize;
    while k < stages {
        let s = 1usize << k;
        cur = barrel_left_stage(aig, &cur, b[k], s);
        k += 1;
    }
    let oor = out_of_range(aig, b, stages);
    let f = lit_false();
    let mut out: Vec<Lit> = Vec::new();
    let mut j = 0usize;
    while j < w {
        let m = push_mux(aig, oor, f, cur[j]);
        out.push(m);
        j += 1;
    }
    out
}

/// `bvlshr` — zero-fill right shift.
pub fn blast_lshr(aig: &mut Aig, a: &[Lit], b: &[Lit]) -> Vec<Lit> {
    barrel_right(aig, a, b, lit_false())
}

/// `bvashr` — sign-fill right shift; all sign when the amount is >= width.
pub fn blast_ashr(aig: &mut Aig, a: &[Lit], b: &[Lit]) -> Vec<Lit> {
    let sign = a[a.len() - 1];
    barrel_right(aig, a, b, sign)
}

/// One rotate-right stage by `2^k` gated on `sel`: bit i becomes
/// `mux(sel, cur[(i + 2^k) mod w], cur[i])`.
pub fn rotr_stage(aig: &mut Aig, cur: &[Lit], sel: Lit, s: usize) -> Vec<Lit> {
    let w = cur.len();
    let mut next: Vec<Lit> = Vec::new();
    let mut i = 0usize;
    while i < w {
        let src = (i + s) % w;
        let m = push_mux(aig, sel, cur[src], cur[i]);
        next.push(m);
        i += 1;
    }
    next
}

/// The rotate-right barrel: `stages` rounds, round `k` rotating by `2^k`
/// gated on `amount[k]`. Rotates by the value of the low `stages` amount
/// bits (mod `w`).
pub fn rotr_stages(aig: &mut Aig, a: &[Lit], amount: &[Lit], stages: usize) -> Vec<Lit> {
    let mut cur: Vec<Lit> = Vec::new();
    let w = a.len();
    let mut i = 0usize;
    while i < w {
        cur.push(a[i]);
        i += 1;
    }
    let mut k = 0usize;
    while k < stages {
        let s = 1usize << k;
        cur = rotr_stage(aig, &cur, amount[k], s);
        k += 1;
    }
    cur
}

/// `bvrotr` — rotate right by amount mod width, at every width `w >= 1`.
/// Mirrors `blast/shift.rs::blast_rotr`: for a power-of-two width only the
/// low `log2 w` amount bits matter (higher bits vanish mod `w`); for any
/// other width the amount is first reduced mod `w` with `blast_urem`
/// against the constant word `w`, and the reduced amount `< w <=
/// 2^stages` drives the barrel (issue #201).
pub fn blast_rotr(aig: &mut Aig, a: &[Lit], b: &[Lit]) -> Vec<Lit> {
    let w = a.len();
    let (stages, pow2) = stage_count(w);
    if pow2 {
        rotr_stages(aig, a, b, stages)
    } else {
        let modulus = word_const(w, w);
        let reduced = blast_urem(aig, b, &modulus);
        rotr_stages(aig, a, &reduced, stages)
    }
}

/// Full adder: `(sum, carry_out)` for one bit column. Mirrors
/// `blast/muldiv.rs::full_adder`.
pub fn full_adder(aig: &mut Aig, a: Lit, b: Lit, cin: Lit) -> (Lit, Lit) {
    let a_xor_b = push_xor(aig, a, b);
    let sum = push_xor(aig, a_xor_b, cin);
    let and_ab = push_and(aig, a, b);
    let and_prop = push_and(aig, a_xor_b, cin);
    let cout = push_or(aig, and_ab, and_prop);
    (sum, cout)
}

/// Ripple subtraction `a - b` as `a + !b + 1`: returns the w-bit difference
/// and the final carry, which is 1 iff `a >= b` (no borrow). Mirrors
/// `blast/muldiv.rs::sub_with_uge`.
pub fn sub_with_uge(aig: &mut Aig, a: &[Lit], b: &[Lit]) -> (Vec<Lit>, Lit) {
    let mut carry = lit_true();
    let mut diff: Vec<Lit> = Vec::new();
    let w = a.len();
    let mut i = 0usize;
    while i < w {
        let nb = lit_not(b[i]);
        let (s, c) = full_adder(aig, a[i], nb, carry);
        diff.push(s);
        carry = c;
        i += 1;
    }
    (diff, carry)
}

/// `bvmul` — truncated shift-add partial-product sum. Row `i` adds
/// `(a << i) & b[i]` into the accumulator; only bits `i..w` are touched and
/// the carry out of bit `w-1` is dropped (modular semantics). Mirrors
/// `blast/muldiv.rs::blast_mul`.
pub fn blast_mul(aig: &mut Aig, a: &[Lit], b: &[Lit]) -> Vec<Lit> {
    let w = a.len();
    let mut acc: Vec<Lit> = Vec::new();
    let mut k = 0usize;
    while k < w {
        acc.push(lit_false());
        k += 1;
    }
    let mut i = 0usize;
    while i < w {
        let mut carry = lit_false();
        let mut j = i;
        while j < w {
            let pp = push_and(aig, a[j - i], b[i]);
            let (sum, cout) = full_adder(aig, acc[j], pp, carry);
            acc[j] = sum;
            carry = cout;
            j += 1;
        }
        i += 1;
    }
    acc
}

/// `bvudiv`/`bvurem` — restoring long division, both results, each with its
/// SMT-LIB divide-by-zero case (quotient all-ones, remainder = dividend).
/// Mirrors `blast/muldiv.rs::blast_udivrem`, including the w-bit trick: the
/// shifted-out top bit alone decides the (w+1)-bit compare, and the w-bit
/// modular difference is correct because the loop invariant `rem < divisor`
/// bounds the true difference below 2^w.
pub fn blast_udivrem(aig: &mut Aig, a: &[Lit], b: &[Lit]) -> (Vec<Lit>, Vec<Lit>) {
    let w = a.len();
    let mut rem: Vec<Lit> = Vec::new();
    let mut quo: Vec<Lit> = Vec::new();
    let mut k = 0usize;
    while k < w {
        rem.push(lit_false());
        quo.push(lit_false());
        k += 1;
    }
    let mut step = 0usize;
    while step < w {
        let i = w - 1 - step;
        // Shift the remainder left, bringing in dividend bit i; `top` is the
        // bit shifted into the conceptual (w+1)-th position.
        let top = rem[w - 1];
        let mut j = w - 1;
        while j > 0 {
            rem[j] = rem[j - 1];
            j -= 1;
        }
        rem[0] = a[i];
        let (diff, low_ge) = sub_with_uge(aig, &rem, b);
        let ge = push_or(aig, top, low_ge);
        quo[i] = ge;
        // Restoring step: keep the difference only when it did not borrow.
        let mut m = 0usize;
        while m < w {
            let sel = push_mux(aig, ge, diff[m], rem[m]);
            rem[m] = sel;
            m += 1;
        }
        step += 1;
    }
    // SMT-LIB divide-by-zero: quotient all-ones, remainder = dividend.
    let mut nz = lit_false();
    let mut n = 0usize;
    while n < w {
        nz = push_or(aig, nz, b[n]);
        n += 1;
    }
    let b_zero = lit_not(nz);
    let t = lit_true();
    let mut quo_out: Vec<Lit> = Vec::new();
    let mut q = 0usize;
    while q < w {
        let sel = push_mux(aig, b_zero, t, quo[q]);
        quo_out.push(sel);
        q += 1;
    }
    let mut rem_out: Vec<Lit> = Vec::new();
    let mut r = 0usize;
    while r < w {
        let sel = push_mux(aig, b_zero, a[r], rem[r]);
        rem_out.push(sel);
        r += 1;
    }
    (quo_out, rem_out)
}

/// `bvudiv` — the quotient half.
pub fn blast_udiv(aig: &mut Aig, a: &[Lit], b: &[Lit]) -> Vec<Lit> {
    let (quo, _rem) = blast_udivrem(aig, a, b);
    quo
}

/// `bvurem` — MULTIPLICATIVE: `a - (a udiv b) * b` (issue #101), mirroring
/// the production rule. Exact including /0 (all-ones * 0 = 0, so a - 0 = a).
pub fn blast_urem(aig: &mut Aig, a: &[Lit], b: &[Lit]) -> Vec<Lit> {
    let q = blast_udiv(aig, a, b);
    let prod = blast_mul(aig, &q, b);
    blast_sub(aig, a, &prod)
}

#[cfg(test)]
mod tests {
    //! Fidelity differential (the blast_kernel <-> aig.rs link, issue #68).
    //!
    //! The Lean proof (`lean/Blaster*.lean`) establishes: MODEL = BitVec
    //! semantics, unbounded. These tests establish: REAL BLASTER = MODEL, by
    //! differential simulation — the same operand values through the real
    //! `blast::*` rules (with structural hashing) and through this model
    //! (without), asserting equal outputs. Every mirrored rule, exhaustive at
    //! every width 1..=8, seeded-sampled at every width 9..=16 and at a
    //! spread of wide widths up to 128 (issue #185(b); this supersedes the
    //! original width-8-only differential). The chain
    //!   real blaster =(this differential)= model =(Lean, all widths)= BitVec
    //! is what replaces "trust the mirroring was faithful". This link is
    //! test evidence (bounded), stated as such — not smuggled into the
    //! unbounded claim. Every pair — `rotr` included — is compared on the
    //! FULL operand domain at every width (issue #201 closed the last
    //! restriction, `rotr` on amounts `< w` at non-power-of-two widths).

    use super::*;

    /// The mirror's `stage_count` IS the real `blast::shift::stage_count`
    /// (`ceil(log2 w)` as `usize::BITS - (w - 1).leading_zeros()`) and its
    /// power-of-two flag IS `usize::is_power_of_two`, at every width the
    /// solver accepts and well beyond — the two functions the mirror can
    /// not call (no Aeneas model) pinned against their std spellings.
    #[test]
    fn stage_count_matches_real_formula_and_is_power_of_two() {
        for w in 1usize..=4096 {
            let real = (usize::BITS - (w - 1).leading_zeros()) as usize;
            assert_eq!(stage_count(w), (real, w.is_power_of_two()), "w={w}");
        }
        for w in [
            usize::MAX / 2,
            usize::MAX / 2 + 1,
            usize::MAX / 2 + 2,
            usize::MAX,
        ] {
            let real = (usize::BITS - (w - 1).leading_zeros()) as usize;
            assert_eq!(stage_count(w), (real, w.is_power_of_two()), "w={w}");
        }
    }

    /// Build two w-bit input words in the model, mirroring `word_input`.
    fn model_inputs(aig: &mut Aig, w: usize) -> (Vec<Lit>, Vec<Lit>) {
        let mut a: Vec<Lit> = Vec::new();
        let mut b: Vec<Lit> = Vec::new();
        let mut i = 0usize;
        while i < w {
            a.push(push_input(aig, i));
            i += 1;
        }
        let mut j = 0usize;
        while j < w {
            b.push(push_input(aig, w + j));
            j += 1;
        }
        (a, b)
    }

    /// One mirrored rule instantiated on both sides: the real output word
    /// (predicates are 1-literal words) and the model output word.
    struct DiffPair {
        name: String,
        real: Vec<crate::aig::Lit>,
        model: Vec<Lit>,
    }

    /// Both AIGs with every mirrored rule blasted once over shared inputs:
    /// `a` = inputs `0..w`, `b` = inputs `w..2w`, `cond` = input `2w`.
    struct DiffHarness {
        w: usize,
        raig: crate::aig::Aig,
        maig: Aig,
        pairs: Vec<DiffPair>,
    }

    /// `(hi, lo)` extract ranges for width `w`: every range for `w <= 8`,
    /// a representative set (full, top/bottom bit, middle, halves) above.
    fn extract_ranges(w: usize) -> Vec<(usize, usize)> {
        let mut out = Vec::new();
        if w <= 8 {
            for hi in 0..w {
                for lo in 0..=hi {
                    out.push((hi, lo));
                }
            }
        } else {
            for (hi, lo) in [
                (w - 1, 0),
                (w - 1, w - 1),
                (0, 0),
                (w / 2, w / 4),
                (w - 1, w / 2),
                (w / 2 - 1, 0),
                (w - 2, 1),
            ] {
                if !out.contains(&(hi, lo)) {
                    out.push((hi, lo));
                }
            }
        }
        out
    }

    /// Build the harness at width `w`. Every pair, `rotr` included, is
    /// compared on its full operand domain.
    fn build_harness(w: usize) -> DiffHarness {
        use crate::aig as real;
        use crate::blast::{arith, bitwise, muldiv, shift, structural};

        type RealWordOp = fn(&mut real::Aig, &real::Word, &real::Word) -> real::Word;
        type ModelWordOp = fn(&mut Aig, &[Lit], &[Lit]) -> Vec<Lit>;
        type RealPredOp = fn(&mut real::Aig, &real::Word, &real::Word) -> real::Lit;
        type ModelPredOp = fn(&mut Aig, &[Lit], &[Lit]) -> Lit;

        let wu = w as u32;
        let mut raig = real::Aig::new();
        let ra = real::word_input(&mut raig, wu);
        let rb = real::word_input(&mut raig, wu);
        let rc = raig.input();

        let mut maig = aig_new();
        let (ma, mb) = model_inputs(&mut maig, w);
        let mc = push_input(&mut maig, 2 * w);

        let mut pairs: Vec<DiffPair> = Vec::new();
        let mut push = |name: String, real: Vec<real::Lit>, model: Vec<Lit>| {
            assert_eq!(real.len(), model.len(), "{name} w={w}: width mismatch");
            pairs.push(DiffPair { name, real, model });
        };

        let word_ops: [(&str, RealWordOp, ModelWordOp); 9] = [
            ("and", bitwise::blast_and, blast_and),
            ("or", bitwise::blast_or, blast_or),
            ("xor", bitwise::blast_xor, blast_xor),
            ("add", arith::blast_add, blast_add),
            ("sub", arith::blast_sub, blast_sub),
            ("mul", muldiv::blast_mul, blast_mul),
            ("udiv", muldiv::blast_udiv, blast_udiv),
            ("urem", muldiv::blast_urem, blast_urem),
            // Commuted operands exercise the rule asymmetrically.
            (
                "sub(b,a)",
                |g, a, b| arith::blast_sub(g, b, a),
                |g, a, b| blast_sub(g, b, a),
            ),
        ];
        for (name, rf, mf) in word_ops {
            let r = rf(&mut raig, &ra, &rb);
            let m = mf(&mut maig, &ma, &mb);
            push(name.to_string(), r, m);
        }

        let pred_ops: [(&str, RealPredOp, ModelPredOp); 10] = [
            ("ult", arith::blast_ult, blast_ult),
            ("ule", arith::blast_ule, blast_ule),
            ("ugt", arith::blast_ugt, blast_ugt),
            ("uge", arith::blast_uge, blast_uge),
            ("slt", arith::blast_slt, blast_slt),
            ("sle", arith::blast_sle, blast_sle),
            ("sgt", arith::blast_sgt, blast_sgt),
            ("sge", arith::blast_sge, blast_sge),
            ("eq", bitwise::blast_eq, blast_eq),
            ("ne", bitwise::blast_ne, blast_ne),
        ];
        for (name, rf, mf) in pred_ops {
            let r = rf(&mut raig, &ra, &rb);
            let m = mf(&mut maig, &ma, &mb);
            push(name.to_string(), vec![r], vec![m]);
        }

        // udivrem returns both halves; compare each.
        let (rq, rr) = muldiv::blast_udivrem(&mut raig, &ra, &rb);
        let (mq, mr) = blast_udivrem(&mut maig, &ma, &mb);
        push("udivrem.quo".to_string(), rq, mq);
        push("udivrem.rem".to_string(), rr, mr);

        let r = bitwise::blast_ite(&mut raig, rc, &ra, &rb);
        let m = blast_ite(&mut maig, mc, &ma, &mb);
        push("ite".to_string(), r, m);

        // Shifts and rotate: both sides derive the stage count (and the
        // rotr mod-w reduction) from the width themselves.
        let r = shift::blast_shl(&mut raig, &ra, &rb);
        let m = blast_shl(&mut maig, &ma, &mb);
        push("shl".to_string(), r, m);
        let r = shift::blast_lshr(&mut raig, &ra, &rb);
        let m = blast_lshr(&mut maig, &ma, &mb);
        push("lshr".to_string(), r, m);
        let r = shift::blast_ashr(&mut raig, &ra, &rb);
        let m = blast_ashr(&mut maig, &ma, &mb);
        push("ashr".to_string(), r, m);
        let r = shift::blast_rotr(&mut raig, &ra, &rb);
        let m = blast_rotr(&mut maig, &ma, &mb);
        push("rotr".to_string(), r, m);

        // Structural plumbing (gate-free).
        for (hi, lo) in extract_ranges(w) {
            let r = structural::blast_extract(&ra, hi as u32, lo as u32);
            let m = blast_extract(&ma, hi, lo);
            push(format!("extract[{hi}:{lo}]"), r, m);
        }
        push(
            "concat(a,b)".to_string(),
            structural::blast_concat(&ra, &rb),
            blast_concat(&ma, &mb),
        );
        push(
            "concat(b,a)".to_string(),
            structural::blast_concat(&rb, &ra),
            blast_concat(&mb, &ma),
        );
        for by in [0usize, 1, 4, w] {
            push(
                format!("zero_ext({by})"),
                structural::blast_zero_ext(&ra, by as u32),
                blast_zero_ext(&ma, by),
            );
            push(
                format!("sign_ext({by})"),
                structural::blast_sign_ext(&ra, by as u32),
                blast_sign_ext(&ma, by),
            );
        }

        DiffHarness {
            w,
            raig,
            maig,
            pairs,
        }
    }

    /// Simulate one `(a, b, cond)` assignment on both sides and assert
    /// every pair agrees bit-for-bit.
    fn check_diff(h: &DiffHarness, a: u128, b: u128, cond: bool) {
        let w = h.w;
        let mut inputs = vec![false; 2 * w + 1];
        for k in 0..w {
            inputs[k] = (a >> k) & 1 == 1;
            inputs[w + k] = (b >> k) & 1 == 1;
        }
        inputs[2 * w] = cond;
        let rvals = h.raig.simulate(&inputs);
        let mvals = simulate(&h.maig, &inputs);
        for p in &h.pairs {
            let agree = p.real.len() == p.model.len()
                && p.real
                    .iter()
                    .zip(&p.model)
                    .all(|(&r, &m)| h.raig.lit_value(&rvals, r) == eval_lit(&mvals, m));
            if !agree {
                let rbits: String = p
                    .real
                    .iter()
                    .rev()
                    .map(|&l| {
                        if h.raig.lit_value(&rvals, l) {
                            '1'
                        } else {
                            '0'
                        }
                    })
                    .collect();
                let mbits: String = p
                    .model
                    .iter()
                    .rev()
                    .map(|&l| if eval_lit(&mvals, l) { '1' } else { '0' })
                    .collect();
                panic!(
                    "mirror/real disagree: op={} w={w} a={a:#x} b={b:#x} cond={cond} \
                     mirror=#b{mbits} real=#b{rbits}",
                    p.name
                );
            }
        }
    }

    fn width_mask(w: usize) -> u128 {
        if w == 128 {
            u128::MAX
        } else {
            (1u128 << w) - 1
        }
    }

    /// xorshift64 — a fixed, dependency-free PRNG for reproducible sampling.
    struct DiffRng(u64);

    impl DiffRng {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }

        fn next_u128(&mut self) -> u128 {
            (u128::from(self.next()) << 64) | u128::from(self.next())
        }
    }

    /// `n` seeded cases at width `w`, mixing uniform operands with the edge
    /// amounts shifts and division care about: in-range `b < w`, exactly
    /// `w`, zero, all-ones, and a set sign bit.
    fn sampled_diff(w: usize, n: u32, seed: u64) {
        let h = build_harness(w);
        let mask = width_mask(w);
        let mut rng = DiffRng(seed | 1);
        for case in 0..n {
            let a = rng.next_u128() & mask;
            let raw = rng.next_u128() & mask;
            let b = match case % 8 {
                0 | 1 => raw,
                2 | 3 => raw % w as u128,
                4 => (w as u128) & mask,
                5 => 0,
                6 => mask,
                _ => (1u128 << (w - 1)) | (raw >> 1),
            };
            let cond = rng.next() & 1 == 1;
            check_diff(&h, a, b, cond);
        }
    }

    // rivet: verifies VER-051
    /// Issue #185(b): EXHAUSTIVE at every width 1..=8 — every `(a, b)` pair
    /// through every mirrored rule on both sides (and/or/xor, add, sub,
    /// ult/ule/ugt/uge, slt/sle/sgt/sge, eq/ne, ite, extract, concat,
    /// zero_ext, sign_ext, shl/lshr/ashr, mul, udiv/urem/udivrem, rotr —
    /// rotr on its FULL amount domain at every width, #201). `ite`'s
    /// condition is exhaustive too: every pair runs under both values.
    #[test]
    fn model_matches_real_blaster_every_op_exhaustive_widths_1_to_8() {
        for w in 1usize..=8 {
            let h = build_harness(w);
            for a in 0u128..(1 << w) {
                for b in 0u128..(1 << w) {
                    check_diff(&h, a, b, false);
                    check_diff(&h, a, b, true);
                }
            }
        }
    }

    // rivet: verifies VER-051
    /// Issue #185(b): seeded sampling at every width 9..=16 (exhaustive is
    /// 2^18..2^32 pairs there — infeasible in a debug `cargo test`).
    #[test]
    fn model_matches_real_blaster_every_op_sampled_widths_9_to_16() {
        for w in 9usize..=16 {
            sampled_diff(w, 4096, 0x185B_0900 ^ w as u64);
        }
    }

    // rivet: verifies VER-051
    /// Issue #185(b): seeded sampling at wide widths up to 128, power-of-two
    /// and not (the #182 bug class lives at the non-power-of-two ones).
    #[test]
    fn model_matches_real_blaster_every_op_sampled_wide_widths() {
        for w in [17usize, 24, 31, 32, 33, 48, 63, 64, 65, 96, 127, 128] {
            sampled_diff(w, 128, 0x185B_1700 ^ w as u64);
        }
    }
}
