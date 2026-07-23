//! Multiplication and unsigned division (DES-008): shift-add partial
//! products; restoring long division with the SMT-LIB divide-by-zero case
//! (divisor = 0 ⇒ all-ones quotient) merged via a divisor-is-zero mux.
//!
//! The adder/comparator primitives are duplicated locally rather than shared
//! with the arith family so this module stands alone; they are a handful of
//! gates and the structural hash collapses any overlap at the AIG level.

use crate::aig::{Aig, Lit, Word};

/// One-bit full adder: returns `(sum, carry_out)`.
fn full_adder(aig: &mut Aig, a: Lit, b: Lit, cin: Lit) -> (Lit, Lit) {
    let a_xor_b = aig.xor(a, b);
    let sum = aig.xor(a_xor_b, cin);
    let and_ab = aig.and(a, b);
    let and_prop = aig.and(a_xor_b, cin);
    let cout = aig.or(and_ab, and_prop);
    (sum, cout)
}

/// Ripple subtraction `a - b` computed as `a + !b + 1`: returns the w-bit
/// difference and the final carry, which is 1 iff `a >= b` (no borrow).
fn sub_with_uge(aig: &mut Aig, a: &Word, b: &Word) -> (Word, Lit) {
    debug_assert_eq!(a.len(), b.len(), "sub_with_uge: operand width mismatch");
    let mut carry = Lit::TRUE;
    let mut diff = Word::with_capacity(a.len());
    for (&x, &y) in a.iter().zip(b) {
        let (s, c) = full_adder(aig, x, y.not(), carry);
        diff.push(s);
        carry = c;
    }
    (diff, carry)
}

/// `bvmul` — truncated shift-add partial-product sum.
///
/// Row `i` adds `(a << i) & b[i]` into an accumulator; only the low `w` bits
/// of each partial sum are computed (row `i` touches bits `i..w`, and the
/// carry out of bit `w-1` is dropped), matching modular semantics.
pub fn blast_mul(aig: &mut Aig, a: &Word, b: &Word) -> Word {
    debug_assert_eq!(a.len(), b.len(), "blast_mul: operand width mismatch");
    let w = a.len();
    let mut acc: Word = vec![Lit::FALSE; w];
    for (i, &bi) in b.iter().enumerate() {
        let mut carry = Lit::FALSE;
        for j in i..w {
            let pp = aig.and(a[j - i], bi);
            let (sum, cout) = full_adder(aig, acc[j], pp, carry);
            acc[j] = sum;
            carry = cout;
        }
    }
    acc
}

/// `bvudiv` / `bvurem` — restoring long division returning both quotient and
/// remainder, each with its SMT-LIB divide-by-zero case (quotient all-ones,
/// remainder = dividend).
///
/// The dividend is consumed MSB-first into a w-bit partial remainder. Each
/// step conceptually widens the remainder to w+1 bits when shifting left;
/// instead of materializing that column, the shifted-out top bit alone
/// decides the comparison — if it is set the (w+1)-bit remainder is at least
/// 2^w > divisor, otherwise a plain w-bit `remainder >= divisor` compare
/// suffices. The w-bit modular difference is correct in both cases because
/// the invariant `remainder < divisor` before the shift bounds the true
/// difference below 2^w. After the last step the partial remainder holds the
/// true remainder.
pub fn blast_udivrem(aig: &mut Aig, a: &Word, b: &Word) -> (Word, Word) {
    debug_assert_eq!(a.len(), b.len(), "blast_udivrem: operand width mismatch");
    let w = a.len();
    let mut rem: Word = vec![Lit::FALSE; w];
    let mut quo: Word = vec![Lit::FALSE; w];
    for i in (0..w).rev() {
        // Shift the remainder left, bringing in dividend bit i; `top` is the
        // bit shifted out into the conceptual (w+1)-th position.
        let top = rem[w - 1];
        for j in (1..w).rev() {
            rem[j] = rem[j - 1];
        }
        rem[0] = a[i];
        // (w+1)-bit remainder >= divisor: the shifted-out bit is set, or the
        // low w bits alone already reach the divisor.
        let (diff, low_ge) = sub_with_uge(aig, &rem, b);
        let ge = aig.or(top, low_ge);
        quo[i] = ge;
        // Restoring step: keep the difference only when it did not borrow.
        for j in 0..w {
            rem[j] = aig.mux(ge, diff[j], rem[j]);
        }
    }
    // SMT-LIB divide-by-zero: quotient all-ones, remainder = dividend.
    let b_zero = b
        .iter()
        .fold(Lit::FALSE, |acc, &bit| aig.or(acc, bit))
        .not();
    let quo = quo.iter().map(|&q| aig.mux(b_zero, Lit::TRUE, q)).collect();
    let rem = rem
        .iter()
        .zip(a)
        .map(|(&r, &ai)| aig.mux(b_zero, ai, r))
        .collect();
    (quo, rem)
}

/// `bvudiv` — the quotient half of [`blast_udivrem`].
pub fn blast_udiv(aig: &mut Aig, a: &Word, b: &Word) -> Word {
    blast_udivrem(aig, a, b).0
}

/// `bvurem` — MULTIPLICATIVE: `a - (a udiv b) * b` at the circuit level
/// (issue #101; the unsigned twin of the #97 fix).
///
/// The divider's remainder output computes the same function, but a consumer
/// equivalence VC pits it against a multiplicative model (`a - (a/b)*b` —
/// synth's rem_u, loom's WASM form), and a divider-remainder-vs-multiplier
/// cross-circuit proof is exponential: under 1 s on the 0.9.1 derived form
/// became over 7 m 48 s (killed) on the divider form, per synth's #101
/// measurements.
/// This shape aligns structurally with those models (the shared `udiv`
/// sub-circuit strashes), restoring propagation-speed VCs.
///
/// Exact for ALL inputs including division by zero, with no special case:
/// SMT-LIB `a udiv 0` is all-ones, and `all-ones * 0 = 0`, so the result is
/// `a - 0 = a` — precisely SMT-LIB `bvurem` by zero.
///
/// The term-level op stays native (`BvTerm::Urem`); only its circuit changed.
/// Kani harnesses (urem_8/32/64) and the exhaustive width-8 evaluator
/// differential re-verify the new circuit against the same reference.
pub fn blast_urem(aig: &mut Aig, a: &Word, b: &Word) -> Word {
    let q = blast_udiv(aig, a, b);
    let prod = blast_mul(aig, &q, b);
    crate::blast::arith::blast_sub(aig, a, &prod)
}

// The SIGNED forms (`bvsdiv`/`bvsrem`) are deliberately NOT blasted here: they
// stay derived ops, lowered onto this core at the term level (see
// `crate::lowering`). Once `bvurem` is native the derived forms cost no
// multiplier either — they are sign corrections over `bvudiv`/`bvurem` — so the
// closed fragment grows by exactly one op rather than three.

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
