//! THE bit-blasting rules, the term-DAG encoder, the folding + hashing pass
//! and the Tseitin encoder — Aeneas-translatable and Lean-proven (issue
//! #68, v0.15.0 — the assurance capstone; issue #192 phases 2 and 3 — the
//! code the solver runs; phase 4 — the code the trusted re-check runs).
//!
//! This module is part of the TRUSTED crate since #192 phase 4: it is a
//! submodule of [`super`] (`kernel.rs`, the crate root of the single
//! Aeneas translation unit, `#[path]`-included so `lean/regen.sh` sees one
//! crate), written in the translatable subset Charon + Aeneas accept (no
//! `HashMap`, no interior mutability, no trait objects, no std beyond
//! `Vec::{new, push, len}` and indexing). `lean/regen.sh` translates the
//! unit into `lean/Kernel.lean` (namespace `kernel.blast_kernel`), and the
//! `lean/Blaster*.lean` proofs establish that each rule equals the formal
//! `BitVec` semantics for ALL widths — the unbounded evidence that replaces
//! the Kani-bounded harnesses.
//!
//! The solver's lowering (`ordeal`'s `solver.rs::lower_with`, through its
//! `blast_kernel` re-export) runs three functions of this file end to end,
//! and so does the trusted [`super::check_query`] over a certificate's
//! term DAG: [`encode`] walks the DAG ([`DagNode`]) calling the proven rule
//! for every node (`encode_sound`, `lean/BlasterDag.lean`), [`compact`]
//! applies the constant folding and structural hashing (`compact_sound`,
//! `lean/BlasterCompact.lean`; the sharing is driven by untrusted hints it
//! checks), and [`tseitin`] emits the CNF (`tseitin_sat_preserving`,
//! `lean/BlasterTseitin.lean`). The three compose with the checker's
//! `lrat_check_sound` into `dag_refuted` (`lean/BlasterCapstone.lean`) and,
//! through `check_query`, into `check_query_sound` (`lean/QueryCheck.lean`):
//! a certificate the checker accepts refutes the DAG. The rules build on an
//! append-only arena — the proofs count nodes exactly (`push_and` appends
//! one node) — which is why folding and hashing are a separate, separately
//! proven pass. The `aig.rs` names in the docs below (`aig::or`,
//! `aig::xor`, `aig::mux`, `word_const`) are the solver's one-gate helpers
//! whose shape each gadget reproduces; `aig.rs`, `cnf.rs` and
//! `blast/mod.rs` (the phase-2 replay bridge) serve the solver-side
//! differentials and the gate-identity tests only (they live in `ordeal`'s
//! `blast_kernel.rs`, next to the re-export, because this crate depends on
//! nothing).

/// A literal: an AIG node index plus a negation flag. Mirrors `aig::Lit`.
#[derive(Clone, Copy)]
pub struct Lit {
    /// The AIG node this literal reads.
    pub node: usize,
    /// Whether the node's value is complemented.
    pub neg: bool,
}

/// An AIG node. `Input` is a primary input (the k-th); `And` is a two-input
/// AND gate over earlier literals. Constants are modelled as node 0 = FALSE.
#[derive(Clone, Copy)]
pub enum Node {
    /// The constant FALSE (always node 0).
    False,
    /// The k-th primary input.
    Input(usize),
    /// A two-input AND gate over earlier literals.
    And(Lit, Lit),
}

/// An and-inverter graph: an append-only vector of nodes. Node 0 is always
/// `False` (so `Lit { node: 0, neg: true }` is TRUE), matching `aig.rs`.
pub struct Aig {
    /// The nodes, in creation order (every gate's operands are earlier).
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

/// XOR: `(x & !y) | (!x & y)` — three AND gates, in exactly the order
/// `aig::xor` pushes them (issue #192 phase 1: the model was `(x | y) &
/// !(x & y)` before, the same function as a different circuit, so the
/// model's CNF was not the shipped CNF). Gate-identical to `aig::xor`:
/// `gate_identity_*` in the tests below rebuilds this gadget through
/// `aig::Aig::and` and demands the same arena.
pub fn push_xor(aig: &mut Aig, x: Lit, y: Lit) -> Lit {
    let l = push_and(aig, x, lit_not(y));
    let r = push_and(aig, lit_not(x), y);
    push_or(aig, l, r)
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

/// `bvand` — per-bit AND over two equal-width words.
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
/// the final carry-out. Per bit:
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

/// `bvadd` — ripple-carry adder, carry-in 0.
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

/// `bvsub` — two's complement: `a + !b + 1`.
pub fn blast_sub(aig: &mut Aig, a: &[Lit], b: &[Lit]) -> Vec<Lit> {
    let not_b = word_not(b);
    let (sum, _carry) = ripple_carry(aig, a, &not_b, lit_true());
    sum
}

/// `bvult` — unsigned less-than: the borrow of `a - b`, i.e. the complement
/// of the carry-out of `a + !b + 1`.
pub fn blast_ult(aig: &mut Aig, a: &[Lit], b: &[Lit]) -> Lit {
    let not_b = word_not(b);
    let (_sum, carry) = ripple_carry(aig, a, &not_b, lit_true());
    lit_not(carry)
}

/// `bvule` — `a <= b` iff not `b < a`.
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

/// The word with its most significant (sign) bit complemented.
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

/// `=` — conjunction of per-bit XNORs.
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

/// Barrel stages for a width `w >= 1`, and whether `w` is a power of two:
/// `ceil(log2 w)`, the bit length of `w - 1` (std would spell it
/// `usize::BITS - (w - 1).leading_zeros()`; `leading_zeros` has no Aeneas
/// model, so this halves `w - 1` to zero and counts the rounds — the
/// `stage_count_matches_real_formula_*` test pins the two spellings against
/// each other). `w` is a power of two exactly when every bit of `w - 1`
/// below that length is set (`w - 1 = 2^stages - 1`), which the same loop
/// records (std: `w.is_power_of_two()`). Stage `k` shifts by `2^k`,
/// `2^(stages-1) < w <= 2^stages`, so `stages <= w` and no stage exceeds the
/// width (issue #201; the Lean spec `stage_count_spec` proves all of this).
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
/// combined amount in `w..2^stages`) this realises `amount >= w`.
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
/// `ceil(log2 w)` mux-stages then an all-`fill` mux on out-of-range, at
/// every width `w >= 1`.
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

/// `bvshl` — barrel left-shifter; zero when the amount is >= width, at
/// every width `w >= 1`.
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
/// For a power-of-two width only the
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

/// Full adder: `(sum, carry_out)` for one bit column.
pub fn full_adder(aig: &mut Aig, a: Lit, b: Lit, cin: Lit) -> (Lit, Lit) {
    let a_xor_b = push_xor(aig, a, b);
    let sum = push_xor(aig, a_xor_b, cin);
    let and_ab = push_and(aig, a, b);
    let and_prop = push_and(aig, a_xor_b, cin);
    let cout = push_or(aig, and_ab, and_prop);
    (sum, cout)
}

/// Ripple subtraction `a - b` as `a + !b + 1`: returns the w-bit difference
/// and the final carry, which is 1 iff `a >= b` (no borrow).
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
/// the carry out of bit `w-1` is dropped (modular semantics).
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
/// The w-bit trick: the
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

/// `bvurem` — MULTIPLICATIVE: `a - (a udiv b) * b` (issue #101; the shape
/// consumer VCs strash against, see `blast/muldiv.rs`). Exact including /0
/// (all-ones * 0 = 0, so a - 0 = a).
pub fn blast_urem(aig: &mut Aig, a: &[Lit], b: &[Lit]) -> Vec<Lit> {
    let q = blast_udiv(aig, a, b);
    let prod = blast_mul(aig, &q, b);
    blast_sub(aig, a, &prod)
}

/// The DIMACS literal of an AIG literal, mirroring `cnf::TseitinMap::cnf_lit`:
/// CNF variable `node + 1` (DIMACS has no variable 0), negative when the
/// literal is complemented. The `as i32` cast is modelled by Aeneas
/// (`UScalar.hcast`); the Lean spec carries the in-bounds precondition.
pub fn cnf_lit(l: Lit) -> i32 {
    let var = (l.node + 1) as i32;
    if l.neg { -var } else { var }
}

/// Model Tseitin encoder (issue #192 phase 1), mirroring `cnf::tseitin`
/// clause for clause and in the same order: the constant node pinned false
/// (`[-1]`), then for every AND gate `o = a & b`, in node order, the three
/// clauses `(¬o ∨ a) (¬o ∨ b) (o ∨ ¬a ∨ ¬b)`, then one unit clause per
/// asserted output literal. `lean/BlasterTseitin.lean` proves
/// `tseitin_sat_preserving`: when every output literal is true under some
/// input assignment, the simulation values satisfy this CNF — the direction
/// an UNSAT verdict needs (a refuted CNF refutes the query). The
/// `tseitin_matches_cnf_rs_*` tests below pin the model to `cnf::tseitin`
/// clause for clause.
///
/// `Vec::new` + `push` (not `vec![]`): the Aeneas fragment, as in `aig_new`.
#[allow(clippy::vec_init_then_push)]
pub fn tseitin(aig: &Aig, outputs: &[Lit]) -> Vec<Vec<i32>> {
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    let mut c0: Vec<i32> = Vec::new();
    c0.push(-1);
    clauses.push(c0);
    let n = aig.nodes.len();
    let mut i = 0usize;
    while i < n {
        let node = aig.nodes[i];
        match node {
            Node::False => {}
            Node::Input(_) => {}
            Node::And(x, y) => {
                let o = (i + 1) as i32;
                let la = cnf_lit(x);
                let lb = cnf_lit(y);
                let mut c1: Vec<i32> = Vec::new();
                c1.push(-o);
                c1.push(la);
                clauses.push(c1);
                let mut c2: Vec<i32> = Vec::new();
                c2.push(-o);
                c2.push(lb);
                clauses.push(c2);
                let mut c3: Vec<i32> = Vec::new();
                c3.push(o);
                c3.push(-la);
                c3.push(-lb);
                clauses.push(c3);
            }
        }
        i += 1;
    }
    let m = outputs.len();
    let mut j = 0usize;
    while j < m {
        let mut c: Vec<i32> = Vec::new();
        c.push(cnf_lit(outputs[j]));
        clauses.push(c);
        j += 1;
    }
    clauses
}

// ───────────────── The term-DAG encoder (issue #192 phase 3) ─────────────────

/// A node of a term DAG (issue #192 phase 3): the closed QF_BV fragment of
/// `term.rs`, with every operand an index of an EARLIER node (topological
/// order). Bitvector nodes denote words; the comparison and boolean nodes
/// denote one-literal words. Leaves: `Var(w)` is a fresh `w`-bit variable
/// (its bits become the next `w` primary inputs, in order), `Const(s, w)`
/// is the `w`-bit constant whose LSB-first bits are `bits[s..s + w]` of the
/// constant table `encode` is given (a table, not a payload, so the node
/// stays `Copy` — the Aeneas fragment, as `Node`). `Extract(hi, lo, a)`,
/// `ZeroExt(a, by)` / `SignExt(a, by)` carry their parameters; `Ite(c, t,
/// e)` takes a boolean node `c`. `lean/BlasterDag.lean` defines the
/// semantics directly over Lean `BitVec` (`dagSim`) and proves
/// `encode_sound`: every node's word denotes its value.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum DagNode {
    /// A fresh `w`-bit variable (the next `w` primary inputs).
    Var(usize),
    /// The `w`-bit constant whose bits are `bits[s..s + w]`: `Const(s, w)`.
    Const(usize, usize),
    /// `bvadd`.
    Add(usize, usize),
    /// `bvsub`.
    Sub(usize, usize),
    /// `bvmul`.
    Mul(usize, usize),
    /// `bvudiv`.
    Udiv(usize, usize),
    /// `bvurem`.
    Urem(usize, usize),
    /// `bvand`.
    And(usize, usize),
    /// `bvor`.
    Or(usize, usize),
    /// `bvxor`.
    Xor(usize, usize),
    /// `bvshl`.
    Shl(usize, usize),
    /// `bvlshr`.
    Lshr(usize, usize),
    /// `bvashr`.
    Ashr(usize, usize),
    /// `rotate_right` (amount as a word).
    Rotr(usize, usize),
    /// `extract[hi:lo]` of a node: `Extract(hi, lo, a)`.
    Extract(usize, usize, usize),
    /// `concat` — the first operand becomes the high bits.
    Concat(usize, usize),
    /// `zero_extend` by `by` bits: `ZeroExt(a, by)`.
    ZeroExt(usize, usize),
    /// `sign_extend` by `by` bits: `SignExt(a, by)`.
    SignExt(usize, usize),
    /// `ite` over a boolean node: `Ite(c, t, e)`.
    Ite(usize, usize, usize),
    /// `=` (boolean result).
    Eq(usize, usize),
    /// `distinct` (boolean result).
    Ne(usize, usize),
    /// `bvult`.
    Ult(usize, usize),
    /// `bvule`.
    Ule(usize, usize),
    /// `bvugt`.
    Ugt(usize, usize),
    /// `bvuge`.
    Uge(usize, usize),
    /// `bvslt`.
    Slt(usize, usize),
    /// `bvsle`.
    Sle(usize, usize),
    /// `bvsgt`.
    Sgt(usize, usize),
    /// `bvsge`.
    Sge(usize, usize),
    /// Boolean `not`.
    Not(usize),
    /// Boolean `and`.
    BoolAnd(usize, usize),
    /// Boolean `or`.
    BoolOr(usize, usize),
}

/// `w` fresh primary inputs numbered `first .. first + w`, as a word.
pub fn word_inputs(aig: &mut Aig, first: usize, w: usize) -> Vec<Lit> {
    let mut out: Vec<Lit> = Vec::new();
    let mut j = 0usize;
    while j < w {
        let l = push_input(aig, first + j);
        out.push(l);
        j += 1;
    }
    out
}

/// The constant word whose bit `j` is `bits[s + j]` (TRUE / FALSE
/// literals, no gates): the `Const(s, w)` leaf.
pub fn word_bits(bits: &[bool], s: usize, w: usize) -> Vec<Lit> {
    let mut out: Vec<Lit> = Vec::new();
    let mut j = 0usize;
    while j < w {
        if bits[s + j] {
            out.push(lit_true());
        } else {
            out.push(lit_false());
        }
        j += 1;
    }
    out
}

/// A one-literal word (the boolean nodes' denotation).
#[allow(clippy::vec_init_then_push)]
pub fn lit_word(l: Lit) -> Vec<Lit> {
    let mut out: Vec<Lit> = Vec::new();
    out.push(l);
    out
}

/// Encode ONE DAG node, given the words of every earlier node (`words[i]`
/// is node `i`'s) and the next free primary-input number `nin`; returns
/// the node's word and the updated input counter. Every arm is a call to
/// the proven rule for that operator — this function adds no gate of its
/// own beyond `push_and` / `push_or` for the boolean connectives.
pub fn encode_node(
    aig: &mut Aig,
    words: &[Vec<Lit>],
    bits: &[bool],
    nin: usize,
    node: DagNode,
) -> (Vec<Lit>, usize) {
    match node {
        DagNode::Var(w) => {
            let out = word_inputs(aig, nin, w);
            (out, nin + w)
        }
        DagNode::Const(s, w) => (word_bits(bits, s, w), nin),
        DagNode::Add(a, b) => (blast_add(aig, &words[a], &words[b]), nin),
        DagNode::Sub(a, b) => (blast_sub(aig, &words[a], &words[b]), nin),
        DagNode::Mul(a, b) => (blast_mul(aig, &words[a], &words[b]), nin),
        DagNode::Udiv(a, b) => (blast_udiv(aig, &words[a], &words[b]), nin),
        DagNode::Urem(a, b) => (blast_urem(aig, &words[a], &words[b]), nin),
        DagNode::And(a, b) => (blast_and(aig, &words[a], &words[b]), nin),
        DagNode::Or(a, b) => (blast_or(aig, &words[a], &words[b]), nin),
        DagNode::Xor(a, b) => (blast_xor(aig, &words[a], &words[b]), nin),
        DagNode::Shl(a, b) => (blast_shl(aig, &words[a], &words[b]), nin),
        DagNode::Lshr(a, b) => (blast_lshr(aig, &words[a], &words[b]), nin),
        DagNode::Ashr(a, b) => (blast_ashr(aig, &words[a], &words[b]), nin),
        DagNode::Rotr(a, b) => (blast_rotr(aig, &words[a], &words[b]), nin),
        DagNode::Extract(hi, lo, a) => (blast_extract(&words[a], hi, lo), nin),
        DagNode::Concat(a, b) => (blast_concat(&words[a], &words[b]), nin),
        DagNode::ZeroExt(a, by) => (blast_zero_ext(&words[a], by), nin),
        DagNode::SignExt(a, by) => (blast_sign_ext(&words[a], by), nin),
        DagNode::Ite(c, t, e) => (blast_ite(aig, words[c][0], &words[t], &words[e]), nin),
        DagNode::Eq(a, b) => (lit_word(blast_eq(aig, &words[a], &words[b])), nin),
        DagNode::Ne(a, b) => (lit_word(blast_ne(aig, &words[a], &words[b])), nin),
        DagNode::Ult(a, b) => (lit_word(blast_ult(aig, &words[a], &words[b])), nin),
        DagNode::Ule(a, b) => (lit_word(blast_ule(aig, &words[a], &words[b])), nin),
        DagNode::Ugt(a, b) => (lit_word(blast_ugt(aig, &words[a], &words[b])), nin),
        DagNode::Uge(a, b) => (lit_word(blast_uge(aig, &words[a], &words[b])), nin),
        DagNode::Slt(a, b) => (lit_word(blast_slt(aig, &words[a], &words[b])), nin),
        DagNode::Sle(a, b) => (lit_word(blast_sle(aig, &words[a], &words[b])), nin),
        DagNode::Sgt(a, b) => (lit_word(blast_sgt(aig, &words[a], &words[b])), nin),
        DagNode::Sge(a, b) => (lit_word(blast_sge(aig, &words[a], &words[b])), nin),
        DagNode::Not(a) => (lit_word(lit_not(words[a][0])), nin),
        DagNode::BoolAnd(a, b) => (lit_word(push_and(aig, words[a][0], words[b][0])), nin),
        DagNode::BoolOr(a, b) => (lit_word(push_or(aig, words[a][0], words[b][0])), nin),
    }
}

/// The proven term-DAG encoder (issue #192 phase 3): encodes every node of
/// a topologically ordered DAG in order, returning every node's word and
/// the asserted output literals — the first (only) literal of each root
/// node's word. The arena is append-only (`push_and`, one node per gate):
/// `compact` applies the folding and hashing afterwards. Semantics and
/// proof: `lean/BlasterDag.lean` (`encode_sound`).
pub fn encode(
    aig: &mut Aig,
    ns: &[DagNode],
    bits: &[bool],
    roots: &[usize],
) -> (Vec<Vec<Lit>>, Vec<Lit>) {
    let mut words: Vec<Vec<Lit>> = Vec::new();
    let mut nin = 0usize;
    let n = ns.len();
    let mut i = 0usize;
    while i < n {
        let node = ns[i];
        let (w, nin1) = encode_node(aig, &words, bits, nin, node);
        words.push(w);
        nin = nin1;
        i += 1;
    }
    let mut outs: Vec<Lit> = Vec::new();
    let m = roots.len();
    let mut r = 0usize;
    while r < m {
        outs.push(words[roots[r]][0]);
        r += 1;
    }
    (words, outs)
}

// ───────────── The folding + hashing pass (issue #192 phase 3) ─────────────

/// Structural literal equality (`Lit` carries no derive, the fragment
/// compares fields).
pub fn lit_eq(a: Lit, b: Lit) -> bool {
    a.node == b.node && a.neg == b.neg
}

/// `a.raw() <= b.raw()` in the shipped arena's AIGER encoding (`node * 2 +
/// neg`), spelled without the multiplication: the operand order the
/// shipped `Aig::and` stores.
pub fn lit_le(a: Lit, b: Lit) -> bool {
    a.node < b.node || (a.node == b.node && (!a.neg || b.neg))
}

/// The literal of the compacted arena that a literal of the source arena
/// maps to (`map[node]`, negated if the literal is).
pub fn map_lit(map: &[Lit], l: Lit) -> Lit {
    let m = map[l.node];
    if l.neg { lit_not(m) } else { m }
}

/// A word of the source arena carried over to the compacted arena, literal
/// by literal (`map_lit`): the asserted outputs after `compact`.
pub fn map_word(map: &[Lit], word: &[Lit]) -> Vec<Lit> {
    let mut out: Vec<Lit> = Vec::new();
    let w = word.len();
    let mut i = 0usize;
    while i < w {
        out.push(map_lit(map, word[i]));
        i += 1;
    }
    out
}

/// Whether `cand` is a positive literal of an existing gate of `out` whose
/// stored operands are exactly `(p, q)` — the check that makes a hashing
/// hint safe: a wrong hint is rejected and a fresh gate is pushed instead.
pub fn hint_matches(out: &Aig, cand: Lit, p: Lit, q: Lit) -> bool {
    if cand.neg || cand.node >= out.nodes.len() {
        false
    } else {
        match out.nodes[cand.node] {
            Node::False => false,
            Node::Input(_) => false,
            Node::And(cx, cy) => lit_eq(cx, p) && lit_eq(cy, q),
        }
    }
}

/// One AND of the compaction pass over already-mapped operands: the
/// shipped `Aig::and`'s constant folds (`x&0 = 0`, `x&!x = 0`, `1&x = x`,
/// `x&1 = x`, `x&x = x`) in its order, then its operand-order
/// normalisation, then the hashing hint — `hint` names a SOURCE node whose
/// mapped gate is claimed to have the same operands; it is checked, never
/// trusted — and otherwise one fresh gate.
pub fn compact_and(out: &mut Aig, map: &[Lit], rx: Lit, ry: Lit, hint: usize) -> Lit {
    if lit_eq(rx, lit_false()) || lit_eq(ry, lit_false()) || lit_eq(rx, lit_not(ry)) {
        lit_false()
    } else if lit_eq(rx, lit_true()) {
        ry
    } else if lit_eq(ry, lit_true()) || lit_eq(rx, ry) {
        rx
    } else {
        let p = if lit_le(rx, ry) { rx } else { ry };
        let q = if lit_le(rx, ry) { ry } else { rx };
        if hint < map.len() && hint_matches(out, map[hint], p, q) {
            map[hint]
        } else {
            push_and(out, p, q)
        }
    }
}

/// The proven folding + structural-hashing pass (issue #192 phase 3):
/// rebuilds `aig` node by node into a fresh arena, keeping the inputs'
/// numbering, folding every AND gate's constants and sharing gates through
/// checked `hints` (`hints[i]` = an earlier source node whose compacted
/// gate node `i` may reuse; `i` itself, or anything wrong, means "no
/// sharing"). Returns the new arena and, for every source node, the
/// literal of the new arena that carries its value. `lean/BlasterDag.lean`
/// proves `compact_sound`: every source literal and its image simulate to
/// the same value under every input assignment, whatever the hints say.
pub fn compact(aig: &Aig, hints: &[usize]) -> (Aig, Vec<Lit>) {
    let mut out = aig_new();
    let mut map: Vec<Lit> = Vec::new();
    let n = aig.nodes.len();
    let mut i = 0usize;
    while i < n {
        let node = aig.nodes[i];
        let hint = if i < hints.len() { hints[i] } else { i };
        let l = match node {
            Node::False => lit_false(),
            Node::Input(k) => push_input(&mut out, k),
            Node::And(x, y) => {
                let rx = map_lit(&map, x);
                let ry = map_lit(&map, y);
                compact_and(&mut out, &map, rx, ry, hint)
            }
        };
        map.push(l);
        i += 1;
    }
    (out, map)
}
