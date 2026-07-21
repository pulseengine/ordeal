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
