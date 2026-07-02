//! And-Inverter Graph with structural hashing and constant folding (DES-002).
//!
//! AIGER literal convention: a [`Lit`] is `variable << 1 | complement`.
//! Variable 0 is the constant, so `Lit(0)` is FALSE and `Lit(1)` is TRUE.
//! Inputs and AND nodes occupy consecutive variable indices in one arena.
//!
//! The [`Aig::and`] constructor folds constants (`x&0=0`, `x&1=x`, `x&x=x`,
//! `x&!x=0`) and structurally hashes operand-normalized pairs, so common
//! subexpressions collapse before the CNF stage ever sees them.

use std::collections::HashMap;

/// An AIG literal: a variable with a complement flag (AIGER convention).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Lit(u32);

impl Lit {
    /// Constant false (variable 0, uncomplemented).
    pub const FALSE: Lit = Lit(0);
    /// Constant true (variable 0, complemented).
    pub const TRUE: Lit = Lit(1);

    fn new(var: u32, complement: bool) -> Lit {
        Lit(var << 1 | complement as u32)
    }
    /// The complemented literal. Also available as the `!` operator; the
    /// inherent method exists so callers don't need `std::ops::Not` in scope.
    #[allow(clippy::should_implement_trait)]
    #[must_use]
    pub fn not(self) -> Lit {
        Lit(self.0 ^ 1)
    }
    /// The underlying variable index.
    pub fn var(self) -> u32 {
        self.0 >> 1
    }
    /// Whether this literal is complemented.
    pub fn is_complement(self) -> bool {
        self.0 & 1 == 1
    }
    /// Raw AIGER encoding (`var*2 + complement`).
    pub fn raw(self) -> u32 {
        self.0
    }
}

impl std::ops::Not for Lit {
    type Output = Lit;
    fn not(self) -> Lit {
        Lit::not(self)
    }
}

#[derive(Clone, Debug)]
enum Node {
    /// Variable 0: the constant-false node.
    Const,
    /// A primary input.
    Input,
    /// An AND gate over two literals.
    And(Lit, Lit),
}

/// The AIG arena.
#[derive(Clone, Debug, Default)]
pub struct Aig {
    nodes: Vec<Node>,
    strash: HashMap<(u32, u32), Lit>,
    num_inputs: u32,
}

impl Aig {
    /// An empty graph (just the constant node).
    pub fn new() -> Self {
        Aig {
            nodes: vec![Node::Const],
            strash: HashMap::new(),
            num_inputs: 0,
        }
    }

    /// Number of variables (constant + inputs + AND nodes).
    pub fn num_vars(&self) -> u32 {
        self.nodes.len() as u32
    }

    /// Number of primary inputs created so far.
    pub fn num_inputs(&self) -> u32 {
        self.num_inputs
    }

    /// Number of AND gates.
    pub fn num_ands(&self) -> u32 {
        self.num_vars() - self.num_inputs - 1
    }

    /// Create a fresh primary input.
    pub fn input(&mut self) -> Lit {
        let var = self.nodes.len() as u32;
        self.nodes.push(Node::Input);
        self.num_inputs += 1;
        Lit::new(var, false)
    }

    /// AND of two literals, with constant folding and structural hashing.
    pub fn and(&mut self, a: Lit, b: Lit) -> Lit {
        // Constant folding.
        if a == Lit::FALSE || b == Lit::FALSE || a == b.not() {
            return Lit::FALSE;
        }
        if a == Lit::TRUE {
            return b;
        }
        if b == Lit::TRUE || a == b {
            return a;
        }
        // Normalize operand order for the strash key.
        let (x, y) = if a.raw() <= b.raw() { (a, b) } else { (b, a) };
        if let Some(&lit) = self.strash.get(&(x.raw(), y.raw())) {
            return lit;
        }
        let var = self.nodes.len() as u32;
        self.nodes.push(Node::And(x, y));
        let lit = Lit::new(var, false);
        self.strash.insert((x.raw(), y.raw()), lit);
        lit
    }

    /// OR via De Morgan.
    pub fn or(&mut self, a: Lit, b: Lit) -> Lit {
        self.and(a.not(), b.not()).not()
    }

    /// XOR built from two ANDs.
    pub fn xor(&mut self, a: Lit, b: Lit) -> Lit {
        let l = self.and(a, b.not());
        let r = self.and(a.not(), b);
        self.or(l, r)
    }

    /// XNOR (equivalence).
    pub fn xnor(&mut self, a: Lit, b: Lit) -> Lit {
        self.xor(a, b).not()
    }

    /// If-then-else: `sel ? t : e`.
    pub fn mux(&mut self, sel: Lit, t: Lit, e: Lit) -> Lit {
        let then_b = self.and(sel, t);
        let else_b = self.and(sel.not(), e);
        self.or(then_b, else_b)
    }

    /// Evaluate every variable under the given input assignment
    /// (`inputs[i]` is the i-th created input). Returns a value per variable.
    pub fn simulate(&self, inputs: &[bool]) -> Vec<bool> {
        assert_eq!(inputs.len() as u32, self.num_inputs, "input count");
        let mut values = vec![false; self.nodes.len()];
        let mut next_input = 0usize;
        for (i, node) in self.nodes.iter().enumerate() {
            values[i] = match node {
                Node::Const => false,
                Node::Input => {
                    let v = inputs[next_input];
                    next_input += 1;
                    v
                }
                Node::And(a, b) => {
                    Self::lit_value_in(&values, *a) && Self::lit_value_in(&values, *b)
                }
            };
        }
        values
    }

    fn lit_value_in(values: &[bool], lit: Lit) -> bool {
        values[lit.var() as usize] ^ lit.is_complement()
    }

    /// The value of a literal under a `simulate` result.
    pub fn lit_value(&self, values: &[bool], lit: Lit) -> bool {
        Self::lit_value_in(values, lit)
    }

    /// The fanins of each AND node, for the CNF encoder: `(var, a, b)`.
    pub fn and_gates(&self) -> impl Iterator<Item = (u32, Lit, Lit)> + '_ {
        self.nodes.iter().enumerate().filter_map(|(v, n)| match n {
            Node::And(a, b) => Some((v as u32, *a, *b)),
            _ => None,
        })
    }
}

/// A bitvector as AIG literals, **LSB first** (`word[0]` is bit 0).
pub type Word = Vec<Lit>;

/// A constant word of the given width.
pub fn word_const(value: u128, width: u32) -> Word {
    (0..width)
        .map(|i| {
            if (value >> i) & 1 == 1 {
                Lit::TRUE
            } else {
                Lit::FALSE
            }
        })
        .collect()
}

/// A word of fresh inputs.
pub fn word_input(aig: &mut Aig, width: u32) -> Word {
    (0..width).map(|_| aig.input()).collect()
}

/// Decode a simulated word back to a value (LSB first).
pub fn word_value(aig: &Aig, values: &[bool], word: &Word) -> u128 {
    word.iter().enumerate().fold(0u128, |acc, (i, lit)| {
        acc | ((aig.lit_value(values, *lit) as u128) << i)
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constant_folding_identities() {
        let mut g = Aig::new();
        let x = g.input();
        assert_eq!(g.and(x, Lit::FALSE), Lit::FALSE);
        assert_eq!(g.and(Lit::FALSE, x), Lit::FALSE);
        assert_eq!(g.and(x, Lit::TRUE), x);
        assert_eq!(g.and(Lit::TRUE, x), x);
        assert_eq!(g.and(x, x), x);
        assert_eq!(g.and(x, x.not()), Lit::FALSE);
        assert_eq!(g.num_ands(), 0, "all folded, no gate created");
    }

    #[test]
    fn structural_hashing_collapses_duplicates() {
        let mut g = Aig::new();
        let x = g.input();
        let y = g.input();
        let a = g.and(x, y);
        let b = g.and(y, x); // operand order normalized
        let c = g.and(x, y); // literal repeat
        assert_eq!(a, b);
        assert_eq!(a, c);
        assert_eq!(g.num_ands(), 1);
    }

    #[test]
    fn complement_involution_and_constants() {
        let mut g = Aig::new();
        let x = g.input();
        assert_eq!(x.not().not(), x);
        assert_eq!(Lit::FALSE.not(), Lit::TRUE);
        assert!(Lit::TRUE.is_complement());
        assert_eq!(Lit::TRUE.var(), 0);
    }

    #[test]
    fn derived_gates_simulate_correctly() {
        let mut g = Aig::new();
        let x = g.input();
        let y = g.input();
        let s = g.input();
        let and = g.and(x, y);
        let or = g.or(x, y);
        let xor = g.xor(x, y);
        let xnor = g.xnor(x, y);
        let mux = g.mux(s, x, y);
        for bits in 0..8u32 {
            let (xv, yv, sv) = (bits & 1 == 1, bits & 2 == 2, bits & 4 == 4);
            let vals = g.simulate(&[xv, yv, sv]);
            assert_eq!(g.lit_value(&vals, and), xv && yv);
            assert_eq!(g.lit_value(&vals, or), xv || yv);
            assert_eq!(g.lit_value(&vals, xor), xv ^ yv);
            assert_eq!(g.lit_value(&vals, xnor), !(xv ^ yv));
            assert_eq!(g.lit_value(&vals, mux), if sv { xv } else { yv });
            assert!(!g.lit_value(&vals, Lit::FALSE));
            assert!(g.lit_value(&vals, Lit::TRUE));
        }
    }

    #[test]
    fn word_helpers_roundtrip() {
        let mut g = Aig::new();
        let w = word_const(0xAB, 8);
        let vals = g.simulate(&[]);
        assert_eq!(word_value(&g, &vals, &w), 0xAB);
        let inp = word_input(&mut g, 8);
        // inputs LSB-first: value 0x01 sets bit 0
        let vals = g.simulate(&[true, false, false, false, false, false, false, false]);
        assert_eq!(word_value(&g, &vals, &inp), 0x01);
    }
}
