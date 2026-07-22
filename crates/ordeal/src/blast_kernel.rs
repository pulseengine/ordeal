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
