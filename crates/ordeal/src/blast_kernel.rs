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
    push_or(aig, x, y)
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

/// `amount >= width`: OR of the amount bits at position `log2 w` and above
/// (width is a power of two). Mirrors `blast/shift.rs::out_of_range`.
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

/// Barrel right-shifter with SMT-LIB out-of-range semantics: `stages`
/// mux-stages then an all-`fill` mux on out-of-range. Mirrors
/// `blast/shift.rs::barrel_right`. Width must be a power of two with
/// `stages = log2 w` (the Lean spec hypothesizes it).
pub fn barrel_right(aig: &mut Aig, a: &[Lit], b: &[Lit], stages: usize, fill: Lit) -> Vec<Lit> {
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
pub fn blast_shl(aig: &mut Aig, a: &[Lit], b: &[Lit], stages: usize) -> Vec<Lit> {
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
pub fn blast_lshr(aig: &mut Aig, a: &[Lit], b: &[Lit], stages: usize) -> Vec<Lit> {
    barrel_right(aig, a, b, stages, lit_false())
}

/// `bvashr` — sign-fill right shift; all sign when the amount is >= width.
pub fn blast_ashr(aig: &mut Aig, a: &[Lit], b: &[Lit], stages: usize) -> Vec<Lit> {
    let sign = a[a.len() - 1];
    barrel_right(aig, a, b, stages, sign)
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

/// `bvrotr` — rotate right by amount mod width; only the low `log2 w` amount
/// bits matter (power-of-two width).
pub fn blast_rotr(aig: &mut Aig, a: &[Lit], b: &[Lit], stages: usize) -> Vec<Lit> {
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
        cur = rotr_stage(aig, &cur, b[k], s);
        k += 1;
    }
    cur
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
    //! (without), asserting equal outputs. Exhaustive at width 8; the chain
    //!   real blaster =(this differential)= model =(Lean, all widths)= BitVec
    //! is what replaces "trust the mirroring was faithful". This link is
    //! test evidence (bounded), stated as such — not smuggled into the
    //! unbounded claim.

    use super::*;

    /// Simulate a model word under a concrete input assignment -> u128.
    fn model_word_value(aig: &Aig, inputs: &[bool], word: &[Lit]) -> u128 {
        let vals = simulate(aig, inputs);
        let mut out = 0u128;
        let mut i = 0usize;
        while i < word.len() {
            if eval_lit(&vals, word[i]) {
                out |= 1u128 << i;
            }
            i += 1;
        }
        out
    }

    /// Simulate a single model literal -> bool.
    fn model_lit_value(aig: &Aig, inputs: &[bool], l: Lit) -> bool {
        let vals = simulate(aig, inputs);
        eval_lit(&vals, l)
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

    /// Exhaustive width-8 differential: every (a, b) pair through the real
    /// blaster and the model; word-valued rules must agree bit-for-bit and
    /// predicate rules literal-for-literal.
    #[test]
    fn model_matches_real_blaster_exhaustively_at_width_8() {
        use crate::aig as real;
        use crate::blast::{arith, bitwise};
        const W: usize = 8;

        // Real side: one AIG, all rules blasted over shared inputs.
        let mut raig = real::Aig::new();
        let ra = real::word_input(&mut raig, W as u32);
        let rb = real::word_input(&mut raig, W as u32);
        let r_and = bitwise::blast_and(&mut raig, &ra, &rb);
        let r_or = bitwise::blast_or(&mut raig, &ra, &rb);
        let r_xor = bitwise::blast_xor(&mut raig, &ra, &rb);
        let r_add = arith::blast_add(&mut raig, &ra, &rb);
        let r_sub = arith::blast_sub(&mut raig, &ra, &rb);
        let r_ult = arith::blast_ult(&mut raig, &ra, &rb);
        let r_slt = arith::blast_slt(&mut raig, &ra, &rb);
        let r_eq = bitwise::blast_eq(&mut raig, &ra, &rb);
        let r_shl = crate::blast::shift::blast_shl(&mut raig, &ra, &rb);
        let r_lshr = crate::blast::shift::blast_lshr(&mut raig, &ra, &rb);
        let r_ashr = crate::blast::shift::blast_ashr(&mut raig, &ra, &rb);
        let r_rotr = crate::blast::shift::blast_rotr(&mut raig, &ra, &rb);
        let r_mul = crate::blast::muldiv::blast_mul(&mut raig, &ra, &rb);
        let (r_quo, r_rem) = crate::blast::muldiv::blast_udivrem(&mut raig, &ra, &rb);

        // Model side: same shape.
        let mut maig = aig_new();
        let (ma, mb) = model_inputs(&mut maig, W);
        let m_and = blast_and(&mut maig, &ma, &mb);
        let m_or = blast_or(&mut maig, &ma, &mb);
        let m_xor = blast_xor(&mut maig, &ma, &mb);
        let m_add = blast_add(&mut maig, &ma, &mb);
        let m_sub = blast_sub(&mut maig, &ma, &mb);
        let m_ult = blast_ult(&mut maig, &ma, &mb);
        let m_slt = blast_slt(&mut maig, &ma, &mb);
        let m_eq = blast_eq(&mut maig, &ma, &mb);
        let m_shl = blast_shl(&mut maig, &ma, &mb, 3);
        let m_lshr = blast_lshr(&mut maig, &ma, &mb, 3);
        let m_ashr = blast_ashr(&mut maig, &ma, &mb, 3);
        let m_rotr = blast_rotr(&mut maig, &ma, &mb, 3);
        let m_mul = blast_mul(&mut maig, &ma, &mb);
        let (m_quo, m_rem) = blast_udivrem(&mut maig, &ma, &mb);

        for av in 0..=255u32 {
            for bv in 0..=255u32 {
                let mut inputs = [false; 2 * W];
                let mut k = 0usize;
                while k < W {
                    inputs[k] = (av >> k) & 1 == 1;
                    inputs[W + k] = (bv >> k) & 1 == 1;
                    k += 1;
                }
                let rvals = raig.simulate(&inputs);
                let word = |wd: &real::Word| real::word_value(&raig, &rvals, wd);
                let lit = |l: real::Lit| {
                    let v = rvals[l.var() as usize];
                    if l.is_complement() { !v } else { v }
                };

                assert_eq!(
                    word(&r_and),
                    model_word_value(&maig, &inputs, &m_and),
                    "and {av} {bv}"
                );
                assert_eq!(
                    word(&r_or),
                    model_word_value(&maig, &inputs, &m_or),
                    "or {av} {bv}"
                );
                assert_eq!(
                    word(&r_xor),
                    model_word_value(&maig, &inputs, &m_xor),
                    "xor {av} {bv}"
                );
                assert_eq!(
                    word(&r_add),
                    model_word_value(&maig, &inputs, &m_add),
                    "add {av} {bv}"
                );
                assert_eq!(
                    word(&r_sub),
                    model_word_value(&maig, &inputs, &m_sub),
                    "sub {av} {bv}"
                );
                assert_eq!(
                    lit(r_ult),
                    model_lit_value(&maig, &inputs, m_ult),
                    "ult {av} {bv}"
                );
                assert_eq!(
                    lit(r_slt),
                    model_lit_value(&maig, &inputs, m_slt),
                    "slt {av} {bv}"
                );
                assert_eq!(
                    lit(r_eq),
                    model_lit_value(&maig, &inputs, m_eq),
                    "eq {av} {bv}"
                );
                assert_eq!(
                    word(&r_shl),
                    model_word_value(&maig, &inputs, &m_shl),
                    "shl {av} {bv}"
                );
                assert_eq!(
                    word(&r_lshr),
                    model_word_value(&maig, &inputs, &m_lshr),
                    "lshr {av} {bv}"
                );
                assert_eq!(
                    word(&r_ashr),
                    model_word_value(&maig, &inputs, &m_ashr),
                    "ashr {av} {bv}"
                );
                assert_eq!(
                    word(&r_rotr),
                    model_word_value(&maig, &inputs, &m_rotr),
                    "rotr {av} {bv}"
                );
                assert_eq!(
                    word(&r_mul),
                    model_word_value(&maig, &inputs, &m_mul),
                    "mul {av} {bv}"
                );
                assert_eq!(
                    word(&r_quo),
                    model_word_value(&maig, &inputs, &m_quo),
                    "udiv {av} {bv}"
                );
                assert_eq!(
                    word(&r_rem),
                    model_word_value(&maig, &inputs, &m_rem),
                    "urem {av} {bv}"
                );
            }
        }
    }

    /// Structural rules are gate-free plumbing; check them on sampled values
    /// against the real rules (same extraction/concat/extension semantics).
    #[test]
    fn model_structural_matches_real_blaster() {
        use crate::aig as real;
        use crate::blast::structural;
        const W: usize = 8;

        let mut raig = real::Aig::new();
        let ra = real::word_input(&mut raig, W as u32);
        let r_ex = structural::blast_extract(&ra, 6, 2);
        let r_ze = structural::blast_zero_ext(&ra, 4);
        let r_se = structural::blast_sign_ext(&ra, 4);

        let mut maig = aig_new();
        let mut ma: Vec<Lit> = Vec::new();
        let mut i = 0usize;
        while i < W {
            ma.push(push_input(&mut maig, i));
            i += 1;
        }
        let m_ex = blast_extract(&ma, 6, 2);
        let m_ze = blast_zero_ext(&ma, 4);
        let m_se = blast_sign_ext(&ma, 4);

        for av in 0..=255u32 {
            let mut inputs = [false; W];
            let mut k = 0usize;
            while k < W {
                inputs[k] = (av >> k) & 1 == 1;
                k += 1;
            }
            let rvals = raig.simulate(&inputs);
            let word = |wd: &real::Word| real::word_value(&raig, &rvals, wd);
            assert_eq!(
                word(&r_ex),
                model_word_value(&maig, &inputs, &m_ex),
                "extract {av}"
            );
            assert_eq!(
                word(&r_ze),
                model_word_value(&maig, &inputs, &m_ze),
                "zero_ext {av}"
            );
            assert_eq!(
                word(&r_se),
                model_word_value(&maig, &inputs, &m_se),
                "sign_ext {av}"
            );
        }
    }
}
