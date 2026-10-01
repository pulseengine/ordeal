//! Multiplication and unsigned division (DES-008) — bridges to the
//! Lean-proven rules in `crate::blast_kernel` (issue #192 phase 2; the
//! rule bodies that used to live here are gone, see `blast/mod.rs`).
//!
//! `bvmul` is a shift-add partial-product sum; `bvudiv`/`bvurem` come from a
//! restoring long division with the SMT-LIB divide-by-zero case (divisor =
//! 0 ⇒ all-ones quotient, remainder = dividend) merged via a divisor-is-zero
//! mux. Proven in `lean/BlasterMul.lean` / `lean/BlasterDiv.lean`.
//!
//! `bvurem` is MULTIPLICATIVE: `a - (a udiv b) * b` at the circuit level
//! (issue #101; the unsigned twin of the #97 fix). The divider's remainder
//! output computes the same function, but a consumer equivalence VC pits it
//! against a multiplicative model (`a - (a/b)*b` — synth's rem_u, loom's
//! WASM form), and a divider-remainder-vs-multiplier cross-circuit proof is
//! exponential: under 1 s on the 0.9.1 derived form became over 7 m 48 s
//! (killed) on the divider form, per synth's #101 measurements. This shape
//! aligns structurally with those models (the shared `udiv` sub-circuit
//! strashes), restoring propagation-speed VCs. Exact for ALL inputs
//! including division by zero, with no special case: SMT-LIB `a udiv 0` is
//! all-ones, and `all-ones * 0 = 0`, so the result is `a - 0 = a`.
//!
//! The SIGNED forms (`bvsdiv`/`bvsrem`) are deliberately NOT blasted here:
//! they stay derived ops, lowered onto this core at the term level (see
//! `crate::lowering`) — sign corrections over `bvudiv`/`bvurem`.

use crate::aig::{Aig, Word};
use crate::blast::{Scratch, udivrem, word2};
use crate::blast_kernel as k;

/// `bvmul` — truncated shift-add partial-product sum.
pub fn blast_mul(aig: &mut Aig, a: &Word, b: &Word) -> Word {
    word2(aig, &mut Scratch::default(), a, b, k::blast_mul)
}

/// `bvudiv` / `bvurem` — restoring long division returning both quotient
/// and remainder, each with its SMT-LIB divide-by-zero case.
pub fn blast_udivrem(aig: &mut Aig, a: &Word, b: &Word) -> (Word, Word) {
    udivrem(aig, &mut Scratch::default(), a, b)
}

/// `bvudiv` — the quotient half of [`blast_udivrem`].
pub fn blast_udiv(aig: &mut Aig, a: &Word, b: &Word) -> Word {
    word2(aig, &mut Scratch::default(), a, b, k::blast_udiv)
}

/// `bvurem` — multiplicative: `a - (a udiv b) * b` (issue #101).
pub fn blast_urem(aig: &mut Aig, a: &Word, b: &Word) -> Word {
    word2(aig, &mut Scratch::default(), a, b, k::blast_urem)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aig::{word_input, word_value};
    use crate::eval::{Env, eval_bv};
    use crate::term::{BvTerm, Sort};

    fn c(value: u128, w: u32) -> Box<BvTerm> {
        Box::new(BvTerm::Const {
            value,
            sort: Sort::new(w),
        })
    }

    /// Oracle values for every natively-blasted muldiv op via the concrete
    /// evaluator (DES-001): (mul, udiv, urem). The signed forms are derived
    /// (see `crate::lowering`) and are verified there.
    fn oracle(x: u128, y: u128, w: u32) -> (u128, u128, u128) {
        let env = Env::new();
        let e = |t: BvTerm| eval_bv(&t, &env).unwrap();
        (
            e(BvTerm::Mul(c(x, w), c(y, w))),
            e(BvTerm::Udiv(c(x, w), c(y, w))),
            e(BvTerm::Urem(c(x, w), c(y, w))),
        )
    }

    /// Two input words plus every natively-blasted muldiv op over them.
    struct Blasted {
        aig: Aig,
        width: u32,
        mul: Word,
        udiv: Word,
        urem: Word,
    }

    impl Blasted {
        fn new(width: u32) -> Self {
            let mut aig = Aig::new();
            let a = word_input(&mut aig, width);
            let b = word_input(&mut aig, width);
            let mul = blast_mul(&mut aig, &a, &b);
            let udiv = blast_udiv(&mut aig, &a, &b);
            let urem = blast_urem(&mut aig, &a, &b);
            Blasted {
                aig,
                width,
                mul,
                udiv,
                urem,
            }
        }

        /// Simulate with `a`/`b` bit patterns (LSB-first: bit i of `a` is
        /// input i, bit i of `b` is input width+i) and compare every op
        /// against the evaluator oracle.
        fn check(&self, x: u128, y: u128) {
            let w = self.width;
            let inputs: Vec<bool> = (0..w)
                .map(|i| (x >> i) & 1 == 1)
                .chain((0..w).map(|i| (y >> i) & 1 == 1))
                .collect();
            let vals = self.aig.simulate(&inputs);
            let (mul, udiv, urem) = oracle(x, y, w);
            let got = |word: &Word| word_value(&self.aig, &vals, word);
            assert_eq!(got(&self.mul), mul, "bvmul {x:#x} {y:#x} width {w}");
            assert_eq!(got(&self.udiv), udiv, "bvudiv {x:#x} {y:#x} width {w}");
            assert_eq!(got(&self.urem), urem, "bvurem {x:#x} {y:#x} width {w}");
        }
    }

    fn xorshift(s: &mut u64) -> u64 {
        *s ^= *s << 13;
        *s ^= *s >> 7;
        *s ^= *s << 17;
        *s
    }

    #[test]
    fn exhaustive_width8_all_muldiv_ops_match_evaluator() {
        // mul, udiv, urem — all 65536 input pairs, so every divisor-zero and
        // remainder-zero case is covered.
        let blasted = Blasted::new(8);
        for x in 0..=0xFFu128 {
            for y in 0..=0xFFu128 {
                blasted.check(x, y);
            }
        }
    }

    #[test]
    fn randomized_width16_matches_evaluator() {
        let blasted = Blasted::new(16);
        let mut s: u64 = 0xB1A5_7016_0000_0016;
        for _ in 0..2000 {
            let x = (xorshift(&mut s) & 0xFFFF) as u128;
            let y = (xorshift(&mut s) & 0xFFFF) as u128;
            blasted.check(x, y);
            blasted.check(x, 0);
            blasted.check(x, 1);
            blasted.check(x, 0xFFFF); // -1 signed
        }
        // Signed boundaries at width 16.
        for x in [0u128, 1, 0x7FFF, 0x8000, 0xFFFF] {
            for y in [0u128, 1, 0x7FFF, 0x8000, 0xFFFF] {
                blasted.check(x, y);
            }
        }
    }

    #[test]
    fn randomized_width32_matches_evaluator() {
        let blasted = Blasted::new(32);
        let mut s: u64 = 0xDEC0_5008_0000_0032;
        for _ in 0..100 {
            let x = (xorshift(&mut s) & 0xFFFF_FFFF) as u128;
            let y = (xorshift(&mut s) & 0xFFFF_FFFF) as u128;
            blasted.check(x, y);
            // Directed shapes off the same stream: divisor zero and one,
            // equal operands, and dividend strictly below the divisor.
            blasted.check(x, 0);
            blasted.check(x, 1);
            blasted.check(x, x);
            let (lo, hi) = (x.min(y), x.max(y));
            if lo < hi {
                blasted.check(lo, hi);
            }
        }
        // Boundary values.
        for x in [0u128, 1, 2, 0xFFFF_FFFF, 0x8000_0000, 0x7FFF_FFFF] {
            for y in [0u128, 1, 2, 0xFFFF_FFFF, 0x8000_0000, 0x7FFF_FFFF] {
                blasted.check(x, y);
            }
        }
    }

    #[test]
    fn randomized_width64_matches_evaluator() {
        let blasted = Blasted::new(64);
        let mut s: u64 = 0xDEC0_5008_0000_0064;
        for _ in 0..100 {
            let x = xorshift(&mut s) as u128;
            let y = xorshift(&mut s) as u128;
            blasted.check(x, y);
            // Directed shapes: divisor zero and one, equal operands, and
            // dividend strictly below the divisor.
            blasted.check(x, 0);
            blasted.check(x, 1);
            blasted.check(x, x);
            let (lo, hi) = (x.min(y), x.max(y));
            if lo < hi {
                blasted.check(lo, hi);
            }
        }
        // Boundary values.
        for x in [
            0u128,
            1,
            2,
            u64::MAX as u128,
            1u128 << 63,
            (1u128 << 63) - 1,
        ] {
            for y in [
                0u128,
                1,
                2,
                u64::MAX as u128,
                1u128 << 63,
                (1u128 << 63) - 1,
            ] {
                blasted.check(x, y);
            }
        }
    }
}
