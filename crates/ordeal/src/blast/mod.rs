//! Bit-blasting (DES-005..DES-009): the per-rule bridge to the Lean-proven
//! rules — since issue #192 phase 3 a TEST harness, not the production path.
//!
//! Since issue #192 phase 2 there is ONE implementation of every rule: the
//! Aeneas-translated, Lean-proven `crate::blast_kernel`. The five op-family
//! modules below hold no rule bodies any more — each `blast_*` there is a
//! one-line bridge that runs the proven rule through [`word2`] / [`pred2`]
//! / friends. Phase 2 ran the solver's term walk through this bridge; since
//! phase 3 the solver lowers the whole query through the proven
//! `blast_kernel::encode` / `compact` / `tseitin` instead (`crate::dag`,
//! `solver.rs::lower_with`), so the replay below no longer runs in
//! production. The modules stay so the per-family evaluator differentials
//! (UV-005..UV-009, VER-049) and the gate-identity tests in
//! `blast_kernel.rs` keep their homes and keep exercising the rules one at
//! a time on the shipped `aig::Aig`. The Kani harnesses (`proofs.rs`)
//! target the `blast_kernel` rules on the reference arena directly:
//! through this bridge they do not terminate under CBMC (the reason and
//! the measurements are in `proofs.rs`).
//!
//! # How the bridge keeps the shipped CNF byte-identical
//!
//! The proven rules build on the reference arena (`blast_kernel::Aig`),
//! whose `push_and` appends exactly one node per call: the Lean proofs
//! count nodes (`push_and_spec`: length = old + 1), so constant folding and
//! structural hashing cannot live there. The shipped arena ([`Aig`]) folds
//! and hashes in [`Aig::and`]. The bridge therefore runs a rule in two
//! steps:
//!
//! 1. a reference arena whose primary inputs stand, in order, for the
//!    shipped operand literals (constants, complements and repeats
//!    included — an input is just a placeholder); the proven rule runs on
//!    it unchanged;
//! 2. the reference arena is replayed node by node into the shipped arena:
//!    input `j` becomes the shipped literal it stood for, and every AND
//!    node becomes one `Aig::and` call over the replayed operands.
//!
//! A shipped rule used to be the same sequence of `Aig::and` calls spelled
//! directly (phase 1 proved it, test `gate_identity_replay_*`, and the
//! `cnf_gap_digest` / `cli_baseline` fingerprints pin it), so the arena,
//! the CNF and the certificate are unchanged. What the replay adds — the
//! folding and hashing inside `Aig::and` — is the part phase 3 of
//! `docs/design/query-cnf-gap.md` turns into a proven pass; it is *not*
//! covered by the rule proofs.
//!
//! The reference arena, the placeholder table and the replay map live in a
//! [`Scratch`] the caller keeps across rule calls (the walk holds one per
//! `Blaster`), so the bridge's own allocations are amortised; the rules'
//! output words are fresh `Vec`s either way.

pub mod arith;
pub mod bitwise;
pub mod muldiv;
pub mod shift;
pub mod structural;

/// Kani proofs of blaster ⇄ evaluator equivalence (FEAT-004 / P4).
#[cfg(kani)]
mod proofs;

use crate::aig::{Aig, Lit, Word};
use crate::blast_kernel as k;

/// A proven word rule: `(arena, a, b) -> word`.
pub type WordRule = fn(&mut k::Aig, &[k::Lit], &[k::Lit]) -> Vec<k::Lit>;
/// A proven predicate rule: `(arena, a, b) -> literal`.
pub type PredRule = fn(&mut k::Aig, &[k::Lit], &[k::Lit]) -> k::Lit;
/// A proven gate-free word rule: `(a, n) -> word` (extensions).
pub type ExtendRule = fn(&[k::Lit], usize) -> Vec<k::Lit>;

/// The bridge's working memory: the reference arena a rule runs on, the
/// shipped literal each of its primary inputs stands for, and the replay
/// map (the shipped literal of every reference node). Reused across calls.
pub struct Scratch {
    maig: k::Aig,
    inputs: Vec<Lit>,
    map: Vec<Lit>,
}

impl Default for Scratch {
    fn default() -> Self {
        Scratch {
            maig: k::aig_new(),
            inputs: Vec::new(),
            map: Vec::new(),
        }
    }
}

impl Scratch {
    /// A fresh reference arena (just the constant node), nothing stood for.
    fn reset(&mut self) {
        self.maig.nodes.clear();
        self.maig.nodes.push(k::Node::False);
        self.inputs.clear();
        self.map.clear();
    }

    /// A reference input standing for the shipped literal `l`.
    fn lit(&mut self, l: Lit) -> k::Lit {
        let j = self.inputs.len();
        self.inputs.push(l);
        k::push_input(&mut self.maig, j)
    }

    /// A reference word standing for the shipped word `w`, bit for bit.
    fn word(&mut self, w: &[Lit]) -> Vec<k::Lit> {
        w.iter().map(|&l| self.lit(l)).collect()
    }

    /// Replay the reference arena into `aig` through [`Aig::and`], filling
    /// `self.map` with the shipped literal of every reference node.
    fn replay(&mut self, aig: &mut Aig) {
        for n in &self.maig.nodes {
            let l = match *n {
                k::Node::False => Lit::FALSE,
                k::Node::Input(j) => self.inputs[j],
                k::Node::And(x, y) => {
                    let (rx, ry) = (lift(&self.map, x), lift(&self.map, y));
                    aig.and(rx, ry)
                }
            };
            self.map.push(l);
        }
    }

    /// Replay and translate an output word.
    fn finish_word(&mut self, aig: &mut Aig, out: &[k::Lit]) -> Word {
        self.replay(aig);
        out.iter().map(|&l| lift(&self.map, l)).collect()
    }

    /// Replay and translate an output literal.
    fn finish_lit(&mut self, aig: &mut Aig, out: k::Lit) -> Lit {
        self.replay(aig);
        lift(&self.map, out)
    }

    /// Translate the output word of a gate-free rule (pure plumbing: the
    /// reference arena holds only the placeholder inputs, so there is
    /// nothing to replay and no shipped arena is involved).
    fn finish_gate_free(&mut self, out: &[k::Lit]) -> Word {
        for n in &self.maig.nodes {
            self.map.push(match *n {
                k::Node::False => Lit::FALSE,
                k::Node::Input(j) => self.inputs[j],
                k::Node::And(..) => unreachable!("gate-free rule pushed a gate"),
            });
        }
        out.iter().map(|&l| lift(&self.map, l)).collect()
    }
}

/// The shipped literal of a reference literal under a replay map.
fn lift(map: &[Lit], l: k::Lit) -> Lit {
    if l.neg {
        map[l.node].not()
    } else {
        map[l.node]
    }
}

/// The malformed operands no rule may see: the walk sort-checks every term
/// before blasting it (`eval::bv_sort`), so this is a guard, not a rule.
fn check_binary(a: &[Lit], b: &[Lit]) {
    assert!(!a.is_empty(), "blast: empty word");
    assert_eq!(a.len(), b.len(), "blast: operand width mismatch");
}

/// Run a proven `Word × Word → Word` rule on shipped words.
pub fn word2(aig: &mut Aig, s: &mut Scratch, a: &Word, b: &Word, rule: WordRule) -> Word {
    check_binary(a, b);
    s.reset();
    let (ma, mb) = (s.word(a), s.word(b));
    let out = rule(&mut s.maig, &ma, &mb);
    s.finish_word(aig, &out)
}

/// Run a proven `Word × Word → Lit` rule (a comparison) on shipped words.
pub fn pred2(aig: &mut Aig, s: &mut Scratch, a: &Word, b: &Word, rule: PredRule) -> Lit {
    check_binary(a, b);
    s.reset();
    let (ma, mb) = (s.word(a), s.word(b));
    let out = rule(&mut s.maig, &ma, &mb);
    s.finish_lit(aig, out)
}

/// Run the proven divider, which yields both halves (`bvudiv`, `bvurem`).
pub fn udivrem(aig: &mut Aig, s: &mut Scratch, a: &Word, b: &Word) -> (Word, Word) {
    check_binary(a, b);
    s.reset();
    let (ma, mb) = (s.word(a), s.word(b));
    let (q, r) = k::blast_udivrem(&mut s.maig, &ma, &mb);
    s.replay(aig);
    let lift_word = |w: &[k::Lit]| -> Word { w.iter().map(|&l| lift(&s.map, l)).collect() };
    (lift_word(&q), lift_word(&r))
}

/// Run the proven `ite` (per-bit mux on a condition literal).
pub fn ite(aig: &mut Aig, s: &mut Scratch, cond: Lit, then_: &Word, else_: &Word) -> Word {
    check_binary(then_, else_);
    s.reset();
    let mc = s.lit(cond);
    let (mt, me) = (s.word(then_), s.word(else_));
    let out = k::blast_ite(&mut s.maig, mc, &mt, &me);
    s.finish_word(aig, &out)
}

/// Run the proven `extract[hi:lo]` (gate-free: pure word plumbing).
pub fn extract(s: &mut Scratch, a: &Word, hi: u32, lo: u32) -> Word {
    assert!(
        hi >= lo && (hi as usize) < a.len(),
        "blast: bad extract range [{hi}:{lo}] for width {}",
        a.len()
    );
    s.reset();
    let ma = s.word(a);
    let out = k::blast_extract(&ma, hi as usize, lo as usize);
    s.finish_gate_free(&out)
}

/// Run the proven `concat` (gate-free; SMT-LIB: the first operand is the
/// high part).
pub fn concat(s: &mut Scratch, hi_part: &Word, lo_part: &Word) -> Word {
    s.reset();
    let (mh, ml) = (s.word(hi_part), s.word(lo_part));
    let out = k::blast_concat(&mh, &ml);
    s.finish_gate_free(&out)
}

/// Run a proven gate-free extension (`zero_ext` / `sign_ext`) by `by` bits.
pub fn extend(s: &mut Scratch, a: &Word, by: u32, rule: ExtendRule) -> Word {
    assert!(!a.is_empty(), "blast: empty word");
    s.reset();
    let ma = s.word(a);
    let out = rule(&ma, by as usize);
    s.finish_gate_free(&out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aig::{AigOptions, word_input};

    // rivet: verifies VER-060
    /// The bridge adds no gates of its own and drops none: on a RAW arena
    /// (no folding, no hashing) the replay has exactly the reference
    /// arena's gate count, and on a default arena the output of a rule
    /// over constants folds away entirely.
    #[test]
    fn bridge_replays_exactly_the_reference_gates() {
        let mut s = Scratch::default();
        let mut raw = Aig::with_options(AigOptions::RAW);
        let a = word_input(&mut raw, 8);
        let b = word_input(&mut raw, 8);
        let before = raw.num_ands();
        let _ = word2(&mut raw, &mut s, &a, &b, k::blast_add);
        // ripple_carry: 2 xor (3 gates each) + and + and + or = 9 per bit.
        assert_eq!(raw.num_ands() - before, 9 * 8);

        let mut def = Aig::new();
        let c1 = crate::aig::word_const(0x2A, 8);
        let c2 = crate::aig::word_const(0x11, 8);
        let sum = word2(&mut def, &mut s, &c1, &c2, k::blast_add);
        assert_eq!(def.num_ands(), 0, "constant operands fold completely");
        assert_eq!(sum, crate::aig::word_const(0x3B, 8));
    }

    // rivet: verifies VER-060
    /// Placeholder inputs are transparent: a shipped literal that is a
    /// constant, a complement or a repeat is replayed as itself, so the
    /// shipped folds (`x & !x = 0`, `x & x = x`) fire exactly as they would
    /// have on a hand-written `Aig::and` sequence. The scratch is reused
    /// across the calls, so a stale map or arena would show here.
    #[test]
    fn bridge_passes_shipped_literals_through_unchanged() {
        let mut s = Scratch::default();
        let mut g = Aig::new();
        let x = g.input();
        let w: Word = vec![x, x.not(), Lit::TRUE, Lit::FALSE];
        let and = word2(&mut g, &mut s, &w, &w, k::blast_and);
        assert_eq!(and, w, "x&x = x, !x&!x = !x, 1&1 = 1, 0&0 = 0");
        let nw: Word = w.iter().map(|l| l.not()).collect();
        let zero = word2(&mut g, &mut s, &w, &nw, k::blast_and);
        assert!(zero.iter().all(|&l| l == Lit::FALSE), "x & !x = 0");
        assert_eq!(g.num_ands(), 0);
        // A real gate after the folded calls: the scratch starts clean.
        let y = g.input();
        let xy = word2(&mut g, &mut s, &vec![x], &vec![y], k::blast_and);
        assert_eq!(g.num_ands(), 1);
        assert_eq!(xy[0].var(), 3, "the one gate is node 3 (const, x, y, x&y)");
    }

    // rivet: verifies VER-060
    /// The gate-free rules pass placeholders straight through: a complement
    /// or a constant in the operand comes back as itself.
    #[test]
    fn gate_free_bridges_preserve_literals() {
        let mut s = Scratch::default();
        let mut g = Aig::new();
        let x = g.input();
        let w: Word = vec![x, x.not(), Lit::TRUE];
        assert_eq!(extract(&mut s, &w, 2, 1), vec![x.not(), Lit::TRUE]);
        assert_eq!(
            concat(&mut s, &w, &vec![Lit::FALSE]),
            vec![Lit::FALSE, x, x.not(), Lit::TRUE]
        );
        assert_eq!(
            extend(&mut s, &w, 2, k::blast_sign_ext),
            vec![x, x.not(), Lit::TRUE, Lit::TRUE, Lit::TRUE]
        );
        assert_eq!(
            extend(&mut s, &w, 1, k::blast_zero_ext),
            vec![x, x.not(), Lit::TRUE, Lit::FALSE]
        );
        assert_eq!(g.num_ands(), 0);
    }
}
