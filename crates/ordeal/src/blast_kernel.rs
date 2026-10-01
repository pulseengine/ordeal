//! THE bit-blasting rules, Aeneas-translatable and Lean-proven (issue #68,
//! v0.15.0 — the assurance capstone; issue #192 phases 2 and 3 — the code
//! the solver runs).
//!
//! This is what `crates/ordeal-lrat/src/kernel.rs` is for the checker: a
//! self-contained Rust core, written in the translatable subset Charon +
//! Aeneas accept (no `HashMap`, no interior mutability, no trait objects).
//! `lean/regen.sh` Aeneas-translates it into `lean/BlastKernel.lean`, and the
//! `lean/Blaster*.lean` proofs establish that each rule equals the formal
//! `BitVec` semantics for ALL widths — the unbounded evidence that replaces
//! the Kani-bounded harnesses.
//!
//! Since #192 phase 3 the solver's lowering (`solver.rs::lower_with`) runs
//! three functions of this file end to end: [`encode`] walks a term DAG
//! ([`DagNode`]) calling the proven rule for every node (`encode_sound`,
//! `lean/BlasterDag.lean`), [`compact`] applies the constant folding and
//! structural hashing the shipped `aig::Aig::and` used to apply gate by
//! gate (`compact_sound`, `lean/BlasterCompact.lean`; the sharing is driven
//! by untrusted hints it checks), and [`tseitin`] emits the CNF
//! (`tseitin_sat_preserving`, `lean/BlasterTseitin.lean`). The three
//! compose with the checker's `lrat_check_sound` into `dag_refuted`
//! (`lean/BlasterCapstone.lean`): a certificate the checker accepts
//! refutes the DAG. The rules build on an append-only arena — the proofs
//! count nodes exactly (`push_and` appends one node) — which is why
//! folding and hashing are a separate, separately proven pass. The
//! `aig.rs` names in the docs below (`aig::or`, `aig::xor`, `aig::mux`,
//! `word_const`) are the shipped one-gate helpers whose shape each gadget
//! reproduces; `aig.rs` and `blast/mod.rs` (the phase-2 replay bridge)
//! now serve the per-family differentials and the gate-identity tests
//! only.

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
#[derive(Clone, Copy)]
pub enum DagNode {
    Var(usize),
    Const(usize, usize),
    Add(usize, usize),
    Sub(usize, usize),
    Mul(usize, usize),
    Udiv(usize, usize),
    Urem(usize, usize),
    And(usize, usize),
    Or(usize, usize),
    Xor(usize, usize),
    Shl(usize, usize),
    Lshr(usize, usize),
    Ashr(usize, usize),
    Rotr(usize, usize),
    Extract(usize, usize, usize),
    Concat(usize, usize),
    ZeroExt(usize, usize),
    SignExt(usize, usize),
    Ite(usize, usize, usize),
    Eq(usize, usize),
    Ne(usize, usize),
    Ult(usize, usize),
    Ule(usize, usize),
    Ugt(usize, usize),
    Uge(usize, usize),
    Slt(usize, usize),
    Sle(usize, usize),
    Sgt(usize, usize),
    Sge(usize, usize),
    Not(usize),
    BoolAnd(usize, usize),
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

#[cfg(test)]
mod tests {
    //! Fidelity differential (the blast_kernel <-> aig.rs link, issue #68;
    //! re-targeted by #192 phase 2).
    //!
    //! The Lean proof (`lean/Blaster*.lean`) establishes: these rules =
    //! BitVec semantics, unbounded, on the append-only reference arena.
    //! Since #192 phase 2 the solver runs these very rules, so there is no
    //! second implementation to compare against. Since phase 3 the solver
    //! lowers through the proven `encode` / `compact` / `tseitin` instead
    //! of the per-rule bridge (`blast/mod.rs`), and the folding + hashing
    //! is proven (`compact_sound`); the bridge is a test harness. These
    //! tests establish, by differential simulation, that BRIDGED
    //! (`blast::*`, replayed with the shipped `Aig::and`'s folding +
    //! hashing) = REFERENCE (this arena, raw): the same operand values
    //! through both, asserting equal outputs. Every rule, exhaustive at
    //! every width 1..=8, seeded-sampled at every width 9..=16 and at a
    //! spread of wide widths up to 128 (issue #185(b)). The chain
    //!   shipped Aig::and (bridge + fold + hash) =(this differential)= rules =(Lean)= BitVec
    //! is bounded test evidence that the shipped `aig::Aig` — the
    //! gate-identity reference `dag::tests` compare `compact` against —
    //! agrees with the rules, stated as such — not smuggled into the
    //! unbounded claim. Every pair — `rotr` included — is compared on the
    //! FULL operand domain at every width (issue #201).

    use super::*;

    /// `stage_count` IS `ceil(log2 w)` as std spells it (`usize::BITS - (w -
    /// 1).leading_zeros()`) and its power-of-two flag IS
    /// `usize::is_power_of_two`, at every width the solver accepts and well
    /// beyond — the two std functions the kernel cannot call (no Aeneas
    /// model) pinned against their std spellings.
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

    /// Build two w-bit input words on the reference arena (`word_input`'s shape).
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

    /// One rule instantiated on both sides: the bridged output word
    /// (predicates are 1-literal words) and the reference output word.
    struct DiffPair {
        name: String,
        real: Vec<crate::aig::Lit>,
        model: Vec<Lit>,
    }

    /// Both AIGs with every rule blasted once over shared inputs:
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
                    "reference/bridged disagree: op={} w={w} a={a:#x} b={b:#x} cond={cond} \
                     reference=#b{mbits} bridged=#b{rbits}",
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
    // rivet: verifies VER-056
    /// Issue #185(b): EXHAUSTIVE at every width 1..=8 — every `(a, b)` pair
    /// through every rule on both sides (and/or/xor, add, sub,
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
    // rivet: verifies VER-056
    /// Issue #185(b): seeded sampling at every width 9..=16 (exhaustive is
    /// 2^18..2^32 pairs there — infeasible in a debug `cargo test`).
    #[test]
    fn model_matches_real_blaster_every_op_sampled_widths_9_to_16() {
        for w in 9usize..=16 {
            sampled_diff(w, 4096, 0x185B_0900 ^ w as u64);
        }
    }

    // rivet: verifies VER-051
    // rivet: verifies VER-056
    /// Issue #185(b): seeded sampling at wide widths up to 128, power-of-two
    /// and not (the #182 bug class lives at the non-power-of-two ones).
    #[test]
    fn model_matches_real_blaster_every_op_sampled_wide_widths() {
        for w in [17usize, 24, 31, 32, 33, 48, 63, 64, 65, 96, 127, 128] {
            sampled_diff(w, 128, 0x185B_1700 ^ w as u64);
        }
    }

    // ───────────── Gate identity (issue #192 phase 1, F1; phase 2) ─────────────
    //
    // The simulation differential above shows bridged and reference compute
    // the same FUNCTION. Phase 1 of #192 needed more: the same CIRCUIT, so
    // that the reference Tseitin CNF (proven in lean/BlasterTseitin.lean) is
    // the CNF the solver ships. In phase 1 the shipped rules were a second
    // hand-written copy and these tests showed the copy was gate-identical;
    // since phase 2 the shipped rules ARE a replay of this arena through
    // `blast/mod.rs`, and the same two notions now pin the bridge against
    // an independent, test-local replay (`replay` below) — every op, every
    // width 1..=16, each op in its own fresh AIG pair:
    //
    //  * RAW identity — the bridged rule on an `AigOptions::RAW` arena (no
    //    folding, no hashing: one gate per `and` call, like `push_and`)
    //    against the reference rule: the same number of nodes, the same
    //    inputs, gate `i` has the same operand PAIR on both sides, and the
    //    same output literals — the bridge adds and drops nothing. The one
    //    asymmetry: the shipped `Aig::and` stores its two operands
    //    order-normalized (`a.raw() <= b.raw()`, the strash key, applied in
    //    every mode) while the reference stores them as given — so gate
    //    operands are compared as unordered pairs. Everything else is exact.
    //  * REPLAY identity — the reference arena replayed node by node through
    //    a DEFAULT `aig::Aig` (folding + hashing) by the test's own `replay`
    //    is node-identical to the bridged rule on a default arena: the same
    //    `and_gates()` sequence, the same output literals. This is the
    //    statement "shipped = fold_and_hash(reference)" that phase 3's
    //    proven pass `compact` realises (`compact_sound` for the value,
    //    `dag::tests::compact_matches_replay_on_a_shared_query` for the
    //    node-for-node identity with this replay).
    //
    // Result: every op is identical under both notions (`push_xor` was the
    // one phase-1 mismatch — `(x|y)&!(x&y)` vs the shipped `(x&!y)|(!x&y)`
    // — and has the shipped shape since).

    /// Every op, by name: the word ops, the predicates, `udivrem`
    /// (both halves), `ite`, the shifts/rotate, the gate-free plumbing and
    /// the one-bit mux gadget.
    const GATE_IDENTITY_OPS: [&str; 30] = [
        "and", "or", "xor", "add", "sub", "sub(b,a)", "mul", "udiv", "urem", "udivrem", "ult",
        "ule", "ugt", "uge", "slt", "sle", "sgt", "sge", "eq", "ne", "ite", "shl", "lshr", "ashr",
        "rotr", "extract", "concat", "zero_ext", "sign_ext", "mux1",
    ];

    /// Run one op on BOTH sides over fresh inputs `a = 0..w`, `b = w..2w`,
    /// `cond = 2w` (created in that order on both arenas, so the input
    /// variables coincide), returning the output words.
    fn apply_op(
        name: &str,
        w: usize,
        raig: &mut crate::aig::Aig,
        maig: &mut Aig,
    ) -> (Vec<crate::aig::Lit>, Vec<Lit>) {
        use crate::aig as real;
        use crate::blast::{arith, bitwise, muldiv, shift, structural};
        let wu = w as u32;
        let ra = real::word_input(raig, wu);
        let rb = real::word_input(raig, wu);
        let rc = raig.input();
        let (ma, mb) = model_inputs(maig, w);
        let mc = push_input(maig, 2 * w);
        match name {
            "and" => (
                bitwise::blast_and(raig, &ra, &rb),
                blast_and(maig, &ma, &mb),
            ),
            "or" => (bitwise::blast_or(raig, &ra, &rb), blast_or(maig, &ma, &mb)),
            "xor" => (
                bitwise::blast_xor(raig, &ra, &rb),
                blast_xor(maig, &ma, &mb),
            ),
            "add" => (arith::blast_add(raig, &ra, &rb), blast_add(maig, &ma, &mb)),
            "sub" => (arith::blast_sub(raig, &ra, &rb), blast_sub(maig, &ma, &mb)),
            "sub(b,a)" => (arith::blast_sub(raig, &rb, &ra), blast_sub(maig, &mb, &ma)),
            "mul" => (muldiv::blast_mul(raig, &ra, &rb), blast_mul(maig, &ma, &mb)),
            "udiv" => (
                muldiv::blast_udiv(raig, &ra, &rb),
                blast_udiv(maig, &ma, &mb),
            ),
            "urem" => (
                muldiv::blast_urem(raig, &ra, &rb),
                blast_urem(maig, &ma, &mb),
            ),
            "udivrem" => {
                let (rq, rr) = muldiv::blast_udivrem(raig, &ra, &rb);
                let (mq, mr) = blast_udivrem(maig, &ma, &mb);
                (
                    rq.into_iter().chain(rr).collect(),
                    mq.into_iter().chain(mr).collect(),
                )
            }
            "ult" => (
                vec![arith::blast_ult(raig, &ra, &rb)],
                vec![blast_ult(maig, &ma, &mb)],
            ),
            "ule" => (
                vec![arith::blast_ule(raig, &ra, &rb)],
                vec![blast_ule(maig, &ma, &mb)],
            ),
            "ugt" => (
                vec![arith::blast_ugt(raig, &ra, &rb)],
                vec![blast_ugt(maig, &ma, &mb)],
            ),
            "uge" => (
                vec![arith::blast_uge(raig, &ra, &rb)],
                vec![blast_uge(maig, &ma, &mb)],
            ),
            "slt" => (
                vec![arith::blast_slt(raig, &ra, &rb)],
                vec![blast_slt(maig, &ma, &mb)],
            ),
            "sle" => (
                vec![arith::blast_sle(raig, &ra, &rb)],
                vec![blast_sle(maig, &ma, &mb)],
            ),
            "sgt" => (
                vec![arith::blast_sgt(raig, &ra, &rb)],
                vec![blast_sgt(maig, &ma, &mb)],
            ),
            "sge" => (
                vec![arith::blast_sge(raig, &ra, &rb)],
                vec![blast_sge(maig, &ma, &mb)],
            ),
            "eq" => (
                vec![bitwise::blast_eq(raig, &ra, &rb)],
                vec![blast_eq(maig, &ma, &mb)],
            ),
            "ne" => (
                vec![bitwise::blast_ne(raig, &ra, &rb)],
                vec![blast_ne(maig, &ma, &mb)],
            ),
            "ite" => (
                bitwise::blast_ite(raig, rc, &ra, &rb),
                blast_ite(maig, mc, &ma, &mb),
            ),
            "shl" => (shift::blast_shl(raig, &ra, &rb), blast_shl(maig, &ma, &mb)),
            "lshr" => (
                shift::blast_lshr(raig, &ra, &rb),
                blast_lshr(maig, &ma, &mb),
            ),
            "ashr" => (
                shift::blast_ashr(raig, &ra, &rb),
                blast_ashr(maig, &ma, &mb),
            ),
            "rotr" => (
                shift::blast_rotr(raig, &ra, &rb),
                blast_rotr(maig, &ma, &mb),
            ),
            // Gate-free plumbing: every extract range for the width, both
            // concat orders, the four extension amounts — concatenated into
            // one output word per side.
            "extract" => {
                let mut r = Vec::new();
                let mut m = Vec::new();
                for (hi, lo) in extract_ranges(w) {
                    r.extend(structural::blast_extract(&ra, hi as u32, lo as u32));
                    m.extend(blast_extract(&ma, hi, lo));
                }
                (r, m)
            }
            "concat" => (
                structural::blast_concat(&ra, &rb)
                    .into_iter()
                    .chain(structural::blast_concat(&rb, &ra))
                    .collect(),
                blast_concat(&ma, &mb)
                    .into_iter()
                    .chain(blast_concat(&mb, &ma))
                    .collect(),
            ),
            "zero_ext" => {
                let mut r = Vec::new();
                let mut m = Vec::new();
                for by in [0usize, 1, 4, w] {
                    r.extend(structural::blast_zero_ext(&ra, by as u32));
                    m.extend(blast_zero_ext(&ma, by));
                }
                (r, m)
            }
            "sign_ext" => {
                let mut r = Vec::new();
                let mut m = Vec::new();
                for by in [0usize, 1, 4, w] {
                    r.extend(structural::blast_sign_ext(&ra, by as u32));
                    m.extend(blast_sign_ext(&ma, by));
                }
                (r, m)
            }
            // The one-bit mux gadget itself (`aig::mux` vs `push_mux`).
            "mux1" => (
                vec![raig.mux(rc, ra[0], rb[0])],
                vec![push_mux(maig, mc, ma[0], mb[0])],
            ),
            other => panic!("unknown gate-identity op {other}"),
        }
    }

    /// AIGER raw encoding of a model literal: `node << 1 | neg`, the
    /// shipped `aig::Lit::raw`.
    fn model_raw(l: Lit) -> u32 {
        (l.node as u32) << 1 | l.neg as u32
    }

    /// The model arena as `(gate var, operand raw, operand raw)` triples in
    /// node order, exactly what `aig::Aig::and_gates` yields.
    fn model_gates(maig: &Aig) -> Vec<(u32, u32, u32)> {
        maig.nodes
            .iter()
            .enumerate()
            .filter_map(|(i, n)| match n {
                Node::And(x, y) => Some((i as u32, model_raw(*x), model_raw(*y))),
                _ => None,
            })
            .collect()
    }

    fn real_gates(raig: &crate::aig::Aig) -> Vec<(u32, u32, u32)> {
        raig.and_gates()
            .map(|(v, a, b)| (v, a.raw(), b.raw()))
            .collect()
    }

    /// The shipped literal of a model literal under a replay map.
    fn replay_lit(map: &[crate::aig::Lit], l: Lit) -> crate::aig::Lit {
        if l.neg {
            map[l.node].not()
        } else {
            map[l.node]
        }
    }

    /// Replay a model arena through a shipped `aig::Aig` with the given
    /// options, returning the arena and the shipped literal of every model
    /// node.
    fn replay(maig: &Aig, opts: crate::aig::AigOptions) -> (crate::aig::Aig, Vec<crate::aig::Lit>) {
        use crate::aig as real;
        let mut raig = real::Aig::with_options(opts);
        let mut map: Vec<real::Lit> = Vec::with_capacity(maig.nodes.len());
        for n in &maig.nodes {
            let r = match n {
                Node::False => real::Lit::FALSE,
                Node::Input(_) => raig.input(),
                Node::And(x, y) => {
                    let (rx, ry) = (replay_lit(&map, *x), replay_lit(&map, *y));
                    raig.and(rx, ry)
                }
            };
            map.push(r);
        }
        (raig, map)
    }

    // rivet: verifies VER-051
    // rivet: verifies VER-059
    /// Issue #192 phase 1 (F1), RAW identity: the bridged rule on an
    /// unsimplified arena IS the reference arena — node for node, every op,
    /// every width 1..=16 (gate operands as unordered pairs, see the
    /// section comment; everything else exact).
    #[test]
    fn gate_identity_raw_every_op_widths_1_to_16() {
        for w in 1usize..=16 {
            for name in GATE_IDENTITY_OPS {
                let mut raig = crate::aig::Aig::with_options(crate::aig::AigOptions::RAW);
                let mut maig = aig_new();
                let (rout, mout) = apply_op(name, w, &mut raig, &mut maig);
                assert_eq!(
                    raig.num_vars() as usize,
                    maig.nodes.len(),
                    "{name} w={w}: node count"
                );
                assert_eq!(
                    raig.num_inputs() as usize,
                    2 * w + 1,
                    "{name} w={w}: inputs"
                );
                let rg = real_gates(&raig);
                let mg = model_gates(&maig);
                assert_eq!(rg.len(), mg.len(), "{name} w={w}: gate count");
                for (k, (r, m)) in rg.iter().zip(&mg).enumerate() {
                    let rp = if r.1 <= r.2 { (r.1, r.2) } else { (r.2, r.1) };
                    let mp = if m.1 <= m.2 { (m.1, m.2) } else { (m.2, m.1) };
                    assert!(
                        r.0 == m.0 && rp == mp,
                        "{name} w={w}: gate #{k} differs: real {r:?} model {m:?}"
                    );
                }
                let mraw: Vec<u32> = mout.iter().map(|&l| model_raw(l)).collect();
                let rraw: Vec<u32> = rout.iter().map(|l| l.raw()).collect();
                assert_eq!(rraw, mraw, "{name} w={w}: output literals");
            }
        }
    }

    // rivet: verifies VER-051
    // rivet: verifies VER-059
    /// Issue #192 phase 1 (F1), REPLAY identity: the reference arena
    /// replayed through a default `aig::Aig` (constant folding + structural
    /// hashing) by the test's own `replay` is node-identical to the bridged
    /// rule — the same `and_gates()` sequence and the same output literals
    /// — for every op at every width 1..=16.
    #[test]
    fn gate_identity_replay_every_op_widths_1_to_16() {
        for w in 1usize..=16 {
            for name in GATE_IDENTITY_OPS {
                let mut raig = crate::aig::Aig::new();
                let mut maig = aig_new();
                let (rout, mout) = apply_op(name, w, &mut raig, &mut maig);
                let (replayed, map) = replay(&maig, crate::aig::AigOptions::default());
                assert_eq!(
                    replayed.num_inputs(),
                    raig.num_inputs(),
                    "{name} w={w}: inputs"
                );
                let rg = real_gates(&raig);
                let pg = real_gates(&replayed);
                for (k, (r, p)) in rg.iter().zip(&pg).enumerate() {
                    assert_eq!(
                        r, p,
                        "{name} w={w}: gate #{k} differs (real vs replayed model)"
                    );
                }
                assert_eq!(rg.len(), pg.len(), "{name} w={w}: gate count");
                assert_eq!(
                    replayed.num_vars(),
                    raig.num_vars(),
                    "{name} w={w}: node count"
                );
                let mapped: Vec<u32> = mout.iter().map(|&l| replay_lit(&map, l).raw()).collect();
                let rraw: Vec<u32> = rout.iter().map(|l| l.raw()).collect();
                assert_eq!(rraw, mapped, "{name} w={w}: output literals");
            }
        }
    }

    // ───────────── Tseitin differential (issue #192 phase 1) ─────────────

    /// A shipped arena as a model arena, node for node. The shipped `Node`
    /// is private; inputs and gates interleave in creation order, so walk
    /// the variables and classify each by whether `and_gates` names it.
    fn to_model(raig: &crate::aig::Aig) -> Aig {
        let gates: std::collections::BTreeMap<u32, (u32, u32)> = raig
            .and_gates()
            .map(|(v, a, b)| (v, (a.raw(), b.raw())))
            .collect();
        let lit = |raw: u32| Lit {
            node: (raw >> 1) as usize,
            neg: raw & 1 == 1,
        };
        let mut m = aig_new();
        let mut k = 0usize;
        for v in 1..raig.num_vars() {
            match gates.get(&v) {
                Some(&(a, b)) => m.nodes.push(Node::And(lit(a), lit(b))),
                None => {
                    m.nodes.push(Node::Input(k));
                    k += 1;
                }
            }
        }
        assert_eq!(k as u32, raig.num_inputs());
        m
    }

    /// Model `tseitin` vs `cnf::tseitin` on the SAME arena (the shipped one
    /// converted node for node): clause-for-clause equal, same var count.
    fn assert_tseitin_identical(raig: &crate::aig::Aig, routs: &[crate::aig::Lit], what: &str) {
        let maig = to_model(raig);
        let mouts: Vec<Lit> = routs
            .iter()
            .map(|l| Lit {
                node: l.var() as usize,
                neg: l.is_complement(),
            })
            .collect();
        let (real, _map) = crate::cnf::tseitin(raig, routs);
        let model = tseitin(&maig, &mouts);
        assert_eq!(real.num_vars as usize, maig.nodes.len(), "{what}: num_vars");
        assert_eq!(real.clauses.len(), model.len(), "{what}: clause count");
        for (k, (r, m)) in real.clauses.iter().zip(&model).enumerate() {
            assert_eq!(r, m, "{what}: clause #{k} differs");
        }
    }

    /// Model `tseitin` on a MODEL-built arena vs `cnf::tseitin` on its raw
    /// replay: the same up to the shipped arena's per-gate operand
    /// normalization (which swaps the two binary clauses of a gate and the
    /// two negated literals of its ternary clause); clause count and
    /// `num_vars` exact.
    fn assert_tseitin_identical_mod_operand_order(maig: &Aig, mouts: &[Lit], what: &str) {
        let (raw, map) = replay(maig, crate::aig::AigOptions::RAW);
        let routs: Vec<crate::aig::Lit> = mouts.iter().map(|&l| replay_lit(&map, l)).collect();
        let (real, _) = crate::cnf::tseitin(&raw, &routs);
        let model = tseitin(maig, mouts);
        assert_eq!(real.num_vars as usize, maig.nodes.len(), "{what}: num_vars");
        assert_eq!(real.clauses.len(), model.len(), "{what}: clause count");
        let mut k = 0usize;
        while k < model.len() {
            let (r, m) = (&real.clauses[k], &model[k]);
            if r == m {
                k += 1;
                continue;
            }
            // A gate whose operands the shipped arena swapped: the model's
            // (¬o∨a)(¬o∨b)(o∨¬a∨¬b) is the shipped (¬o∨b)(¬o∨a)(o∨¬b∨¬a).
            assert!(
                k + 2 < model.len(),
                "{what}: clause #{k} differs: real {r:?} model {m:?}"
            );
            let (m1, m2, m3) = (&model[k], &model[k + 1], &model[k + 2]);
            let (r1, r2, r3) = (&real.clauses[k], &real.clauses[k + 1], &real.clauses[k + 2]);
            let swapped = m1.len() == 2
                && m3.len() == 3
                && r1 == m2
                && r2 == m1
                && r3 == &vec![m3[0], m3[2], m3[1]];
            assert!(
                swapped,
                "{what}: clauses #{k}..#{} differ beyond operand order: real {r1:?} {r2:?} {r3:?} model {m1:?} {m2:?} {m3:?}",
                k + 2
            );
            k += 3;
        }
    }

    // rivet: verifies VER-051
    // rivet: verifies VER-059
    /// Issue #192 phase 1: the model Tseitin encoder IS `cnf::tseitin` —
    /// clause for clause, in order — on the shipped arena of every
    /// op at every width 1..=16, in each simplification mode (raw, fold
    /// only, fold + hash), asserting every output literal; and, on the
    /// model-built arenas, the same up to the shipped operand normalization.
    #[test]
    fn tseitin_matches_cnf_rs_every_op_widths_1_to_16() {
        for w in 1usize..=16 {
            for name in GATE_IDENTITY_OPS {
                for opts in [
                    crate::aig::AigOptions::RAW,
                    crate::aig::AigOptions::FOLD_ONLY,
                    crate::aig::AigOptions::default(),
                ] {
                    let mut raig = crate::aig::Aig::with_options(opts);
                    let mut maig = aig_new();
                    let (rout, mout) = apply_op(name, w, &mut raig, &mut maig);
                    assert_tseitin_identical(&raig, &rout, &format!("{name} w={w} {opts:?}"));
                    assert_tseitin_identical_mod_operand_order(
                        &maig,
                        &mout,
                        &format!("{name} w={w} (model arena)"),
                    );
                }
            }
        }
    }

    /// A seeded random model circuit over `n_in` inputs with `n_gates`
    /// gates (operands drawn from earlier nodes, random polarity), and a
    /// random output literal.
    fn random_model_circuit(rng: &mut DiffRng, n_in: usize, n_gates: usize) -> (Aig, Lit) {
        let mut maig = aig_new();
        for k in 0..n_in {
            push_input(&mut maig, k);
        }
        for _ in 0..n_gates {
            let n = maig.nodes.len();
            let pick = |rng: &mut DiffRng| Lit {
                node: (rng.next() % n as u64) as usize,
                neg: rng.next() & 1 == 1,
            };
            let (x, y) = (pick(rng), pick(rng));
            push_and(&mut maig, x, y);
        }
        let out = Lit {
            node: maig.nodes.len() - 1,
            neg: rng.next() & 1 == 1,
        };
        (maig, out)
    }

    // rivet: verifies VER-051
    // rivet: verifies VER-059
    /// Issue #192 phase 1: `tseitin` vs `cnf::tseitin` on seeded random
    /// circuits (any operand mix, including constants and repeated
    /// operands, which the op arenas never produce raw).
    #[test]
    fn tseitin_matches_cnf_rs_random_circuits() {
        let mut rng = DiffRng(0x1920_7531);
        for round in 0..200 {
            let (maig, out) = random_model_circuit(&mut rng, 1 + (round % 6), 1 + (round % 40));
            assert_tseitin_identical_mod_operand_order(&maig, &[out], &format!("round {round}"));
            // And exactly, on the replayed (default) arena's conversion.
            let (raig, map) = replay(&maig, crate::aig::AigOptions::default());
            assert_tseitin_identical(
                &raig,
                &[replay_lit(&map, out)],
                &format!("round {round} (replayed)"),
            );
        }
    }

    /// Evaluate a DIMACS clause list under `vals[v-1]`.
    fn cnf_holds(clauses: &[Vec<i32>], vals: &[bool]) -> bool {
        clauses.iter().all(|c| {
            c.iter().any(|&l| {
                let v = vals[(l.unsigned_abs() - 1) as usize];
                if l > 0 { v } else { !v }
            })
        })
    }

    // rivet: verifies VER-051
    // rivet: verifies VER-059
    /// Issue #192 phase 1: the runtime shadow of `tseitin_sat_preserving`
    /// (lean/BlasterTseitin.lean) — for every input assignment under which
    /// the output literal is TRUE, the simulation values (CNF variable
    /// `v + 1` := node `v`'s value) satisfy the model CNF; and when it is
    /// FALSE they do not (the root unit clause fails). Random small
    /// circuits, exhaustive over the inputs.
    #[test]
    fn tseitin_simulation_values_satisfy_cnf_iff_output_true() {
        let mut rng = DiffRng(0x1920_ACE5);
        for round in 0..100 {
            let n_in = 1 + (round % 5);
            let (maig, out) = random_model_circuit(&mut rng, n_in, 1 + (round % 12));
            let cnf = tseitin(&maig, &[out]);
            for bits in 0u32..(1 << n_in) {
                let inputs: Vec<bool> = (0..n_in).map(|k| bits >> k & 1 == 1).collect();
                let vals = simulate(&maig, &inputs);
                assert_eq!(
                    cnf_holds(&cnf, &vals),
                    eval_lit(&vals, out),
                    "round {round} inputs {bits:#b}"
                );
            }
        }
    }
}
