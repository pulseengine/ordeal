//! And-Inverter Graph with structural hashing and constant folding (DES-002).
//!
//! AIGER literal convention: a [`Lit`] is `variable << 1 | complement`.
//! Variable 0 is the constant, so `Lit(0)` is FALSE and `Lit(1)` is TRUE.
//! Inputs and AND nodes occupy consecutive variable indices in one arena.
//!
//! The [`Aig::and`] constructor folds constants (`x&0=0`, `x&1=x`, `x&x=x`,
//! `x&!x=0`) and structurally hashes operand-normalized pairs, so common
//! subexpressions collapse before the CNF stage ever sees them.

#[cfg(not(kani))]
use std::collections::HashMap;

/// Structural-hash map over operand-normalized gate-index pairs — a pure
/// de-duplication cache: on a repeated `(x, y)` it returns the existing,
/// structurally-identical gate instead of a fresh one.
///
/// Production uses `HashMap`. Under Kani the cache is a **no-op** (`get` always
/// misses): `RandomState` seeds from the OS RNG, which Kani cannot model, and
/// modeling any real hash/tree map explodes the SAT problem. Skipping dedup
/// yields a larger but *simulation-identical* AIG (the strash only ever returns
/// a gate with the same fanins), so a correctness proof over the un-deduped AIG
/// establishes the deduped production AIG too. See `blast::proofs`.
#[cfg(not(kani))]
type Strash = HashMap<(u32, u32), Lit>;

#[cfg(kani)]
#[derive(Clone, Debug, Default)]
struct Strash;
#[cfg(kani)]
impl Strash {
    fn get(&self, _key: &(u32, u32)) -> Option<&Lit> {
        None
    }
    fn insert(&mut self, _key: (u32, u32), _lit: Lit) {}
}

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

/// Which simplifications [`Aig::and`] applies (issue #192 phase 1: the
/// CNF-size / time benchmark in `docs/design/query-cnf-gap.md` runs the
/// shipped blast rules under each combination). The production pipeline
/// always uses [`AigOptions::default`] (both on); every other setting is a
/// measurement / test configuration and yields a *simulation-identical*
/// AIG (folding and hashing only change which gates exist, never what a
/// literal computes).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AigOptions {
    /// Constant folding: `x&0=0`, `x&1=x`, `x&x=x`, `x&!x=0`.
    pub fold: bool,
    /// Structural hashing: a repeated operand pair returns the existing gate.
    pub strash: bool,
}

impl Default for AigOptions {
    /// The production setting: folding and hashing both on.
    fn default() -> Self {
        AigOptions {
            fold: true,
            strash: true,
        }
    }
}

impl AigOptions {
    /// No simplification at all: one gate per `and` call — the shape of the
    /// Lean-modelled `blast_kernel` arena.
    pub const RAW: AigOptions = AigOptions {
        fold: false,
        strash: false,
    };
    /// Constant folding only, no gate sharing.
    pub const FOLD_ONLY: AigOptions = AigOptions {
        fold: true,
        strash: false,
    };
}

/// The AIG arena.
#[derive(Clone, Debug, Default)]
pub struct Aig {
    nodes: Vec<Node>,
    strash: Strash,
    num_inputs: u32,
    options: AigOptions,
}

impl Aig {
    /// An empty graph (just the constant node), with folding and hashing on.
    pub fn new() -> Self {
        Self::with_options(AigOptions::default())
    }

    /// An empty graph with the given simplification settings.
    pub fn with_options(options: AigOptions) -> Self {
        Aig {
            nodes: vec![Node::Const],
            strash: Strash::default(),
            num_inputs: 0,
            options,
        }
    }

    /// The simplification settings this arena was created with.
    pub fn options(&self) -> AigOptions {
        self.options
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

    /// AND of two literals, with constant folding and structural hashing
    /// (each as enabled by the arena's [`AigOptions`]).
    pub fn and(&mut self, a: Lit, b: Lit) -> Lit {
        // Constant folding.
        if self.options.fold {
            if a == Lit::FALSE || b == Lit::FALSE || a == b.not() {
                return Lit::FALSE;
            }
            if a == Lit::TRUE {
                return b;
            }
            if b == Lit::TRUE || a == b {
                return a;
            }
        }
        // Normalize operand order (the strash key; applied in every mode so
        // the stored gate never depends on the hashing setting).
        let (x, y) = if a.raw() <= b.raw() { (a, b) } else { (b, a) };
        if self.options.strash
            && let Some(&lit) = self.strash.get(&(x.raw(), y.raw()))
        {
            return lit;
        }
        let var = self.nodes.len() as u32;
        self.nodes.push(Node::And(x, y));
        let lit = Lit::new(var, false);
        if self.options.strash {
            self.strash.insert((x.raw(), y.raw()), lit);
        }
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
    fn options_control_folding_and_hashing() {
        // RAW: every `and` call is a gate, even a foldable or repeated one.
        let mut raw = Aig::with_options(AigOptions::RAW);
        let x = raw.input();
        let y = raw.input();
        let g1 = raw.and(x, Lit::TRUE);
        assert_ne!(g1, x, "no folding: and(x, TRUE) is a fresh gate");
        let g2 = raw.and(x, y);
        let g3 = raw.and(y, x);
        assert_ne!(g2, g3, "no hashing: a repeated pair is a fresh gate");
        assert_eq!(raw.num_ands(), 3);
        // FOLD_ONLY: folds, but still no sharing.
        let mut fold = Aig::with_options(AigOptions::FOLD_ONLY);
        let x = fold.input();
        let y = fold.input();
        assert_eq!(fold.and(x, Lit::TRUE), x);
        let g2 = fold.and(x, y);
        let g3 = fold.and(y, x);
        assert_ne!(g2, g3);
        assert_eq!(fold.num_ands(), 2);
        // Default: both, and `new()` is the default.
        let mut def = Aig::new();
        assert_eq!(def.options(), AigOptions::default());
        let x = def.input();
        let y = def.input();
        assert_eq!(def.and(x, Lit::TRUE), x);
        assert_eq!(def.and(x, y), def.and(y, x));
        assert_eq!(def.num_ands(), 1);
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
