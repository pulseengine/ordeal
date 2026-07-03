//! Bitwise ops and (dis)equality (DES-005): bvand, bvor, bvxor, eq, ne.
//!
//! Each rule is a direct per-bit lowering: `bvand`/`bvor`/`bvxor` map bit `i`
//! of the result to the corresponding gate over bit `i` of the operands;
//! `eq` is the conjunction of per-bit XNORs and `ne` its negation. All rules
//! are verified against the concrete evaluator (DES-001) per UV-005.

use crate::aig::{Aig, Lit, Word};

/// `bvand` — per-bit AND.
pub fn blast_and(aig: &mut Aig, a: &Word, b: &Word) -> Word {
    debug_assert_eq!(a.len(), b.len(), "blast_and: operand width mismatch");
    a.iter().zip(b).map(|(&x, &y)| aig.and(x, y)).collect()
}

/// `bvor` — per-bit OR.
pub fn blast_or(aig: &mut Aig, a: &Word, b: &Word) -> Word {
    debug_assert_eq!(a.len(), b.len(), "blast_or: operand width mismatch");
    a.iter().zip(b).map(|(&x, &y)| aig.or(x, y)).collect()
}

/// `bvxor` — per-bit XOR.
pub fn blast_xor(aig: &mut Aig, a: &Word, b: &Word) -> Word {
    debug_assert_eq!(a.len(), b.len(), "blast_xor: operand width mismatch");
    a.iter().zip(b).map(|(&x, &y)| aig.xor(x, y)).collect()
}

/// `=` — conjunction of per-bit XNORs.
pub fn blast_eq(aig: &mut Aig, a: &Word, b: &Word) -> Lit {
    debug_assert_eq!(a.len(), b.len(), "blast_eq: operand width mismatch");
    a.iter().zip(b).fold(Lit::TRUE, |acc, (&x, &y)| {
        let bit_eq = aig.xnor(x, y);
        aig.and(acc, bit_eq)
    })
}

/// `distinct` — negation of equality.
pub fn blast_ne(aig: &mut Aig, a: &Word, b: &Word) -> Lit {
    blast_eq(aig, a, b).not()
}

/// `ite` (bool→BV bridge, DES-017) — per-bit mux on the condition literal:
/// `cond ? then_ : else_`. Both words must share the width.
pub fn blast_ite(aig: &mut Aig, cond: Lit, then_: &Word, else_: &Word) -> Word {
    debug_assert_eq!(then_.len(), else_.len(), "blast_ite: branch width mismatch");
    then_
        .iter()
        .zip(else_)
        .map(|(&t, &e)| aig.mux(cond, t, e))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aig::{word_input, word_value};
    use crate::eval::{Env, eval_bool, eval_bv};
    use crate::term::{BoolTerm, BvTerm, Sort};

    fn c(value: u128, w: u32) -> Box<BvTerm> {
        Box::new(BvTerm::Const {
            value,
            sort: Sort::new(w),
        })
    }

    /// Oracle values for all five ops via the concrete evaluator (DES-001).
    fn oracle(x: u128, y: u128, w: u32) -> (u128, u128, u128, bool, bool) {
        let env = Env::new();
        (
            eval_bv(&BvTerm::And(c(x, w), c(y, w)), &env).unwrap(),
            eval_bv(&BvTerm::Or(c(x, w), c(y, w)), &env).unwrap(),
            eval_bv(&BvTerm::Xor(c(x, w), c(y, w)), &env).unwrap(),
            eval_bool(&BoolTerm::Eq(c(x, w), c(y, w)), &env).unwrap(),
            eval_bool(&BoolTerm::Ne(c(x, w), c(y, w)), &env).unwrap(),
        )
    }

    /// Two input words plus every op blasted once over them.
    struct Blasted {
        aig: Aig,
        width: u32,
        and: Word,
        or: Word,
        xor: Word,
        eq: Lit,
        ne: Lit,
    }

    impl Blasted {
        fn new(width: u32) -> Self {
            let mut aig = Aig::new();
            let a = word_input(&mut aig, width);
            let b = word_input(&mut aig, width);
            let and = blast_and(&mut aig, &a, &b);
            let or = blast_or(&mut aig, &a, &b);
            let xor = blast_xor(&mut aig, &a, &b);
            let eq = blast_eq(&mut aig, &a, &b);
            let ne = blast_ne(&mut aig, &a, &b);
            Blasted {
                aig,
                width,
                and,
                or,
                xor,
                eq,
                ne,
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
            let (and, or, xor, eq, ne) = oracle(x, y, w);
            assert_eq!(
                word_value(&self.aig, &vals, &self.and),
                and,
                "bvand {x:#x} {y:#x} width {w}"
            );
            assert_eq!(
                word_value(&self.aig, &vals, &self.or),
                or,
                "bvor {x:#x} {y:#x} width {w}"
            );
            assert_eq!(
                word_value(&self.aig, &vals, &self.xor),
                xor,
                "bvxor {x:#x} {y:#x} width {w}"
            );
            assert_eq!(
                self.aig.lit_value(&vals, self.eq),
                eq,
                "eq {x:#x} {y:#x} width {w}"
            );
            assert_eq!(
                self.aig.lit_value(&vals, self.ne),
                ne,
                "ne {x:#x} {y:#x} width {w}"
            );
        }
    }

    fn xorshift(s: &mut u64) -> u64 {
        *s ^= *s << 13;
        *s ^= *s >> 7;
        *s ^= *s << 17;
        *s
    }

    #[test]
    fn exhaustive_width8_all_ops_match_evaluator() {
        let blasted = Blasted::new(8);
        for x in 0..=0xFFu128 {
            for y in 0..=0xFFu128 {
                blasted.check(x, y);
            }
        }
    }

    #[test]
    fn randomized_width32_matches_evaluator() {
        let blasted = Blasted::new(32);
        let mut s: u64 = 0xDEC0_5005_0000_0032;
        for _ in 0..200 {
            let x = (xorshift(&mut s) & 0xFFFF_FFFF) as u128;
            let y = (xorshift(&mut s) & 0xFFFF_FFFF) as u128;
            blasted.check(x, y);
        }
        // Boundary values.
        for x in [0u128, 1, 0xFFFF_FFFF, 0x8000_0000] {
            for y in [0u128, 1, 0xFFFF_FFFF, 0x8000_0000] {
                blasted.check(x, y);
            }
        }
    }

    #[test]
    fn randomized_width64_matches_evaluator() {
        let blasted = Blasted::new(64);
        let mut s: u64 = 0xDEC0_5005_0000_0064;
        for _ in 0..200 {
            let x = xorshift(&mut s) as u128;
            let y = xorshift(&mut s) as u128;
            blasted.check(x, y);
        }
        // Boundary values.
        for x in [0u128, 1, u64::MAX as u128, 1u128 << 63] {
            for y in [0u128, 1, u64::MAX as u128, 1u128 << 63] {
                blasted.check(x, y);
            }
        }
    }

    #[test]
    fn eq_reflexive_ne_irreflexive() {
        for width in [8u32, 32, 64] {
            let mut aig = Aig::new();
            let w = word_input(&mut aig, width);
            let eq = blast_eq(&mut aig, &w, &w);
            let ne = blast_ne(&mut aig, &w, &w);
            // eq(w, w) folds to constant true structurally...
            assert_eq!(eq, Lit::TRUE, "width {width}");
            assert_eq!(ne, Lit::FALSE, "width {width}");
            // ...and simulates true/false for random values.
            let mut s: u64 = 0x5EED_0000 + width as u64;
            for _ in 0..20 {
                let v = xorshift(&mut s) as u128;
                let inputs: Vec<bool> = (0..width).map(|i| (v >> i) & 1 == 1).collect();
                let vals = aig.simulate(&inputs);
                assert!(aig.lit_value(&vals, eq), "eq(w,w) at {v:#x} width {width}");
                assert!(!aig.lit_value(&vals, ne), "ne(w,w) at {v:#x} width {width}");
            }
        }
    }

    #[test]
    fn ite_selects_the_right_branch() {
        // One AIG: a condition input + two 8-bit branch words. Exhaustive over
        // (cond, then, else) low bytes at width 8 via simulation.
        let mut aig = Aig::new();
        let cond = aig.input();
        let then_ = word_input(&mut aig, 8);
        let else_ = word_input(&mut aig, 8);
        let out = blast_ite(&mut aig, cond, &then_, &else_);
        for c in [false, true] {
            for t in 0u128..=0xFF {
                for e in [0u128, 1, 0x80, 0xFF, 0x5A] {
                    let inputs: Vec<bool> = std::iter::once(c)
                        .chain((0..8).map(|i| (t >> i) & 1 == 1))
                        .chain((0..8).map(|i| (e >> i) & 1 == 1))
                        .collect();
                    let vals = aig.simulate(&inputs);
                    let want = if c { t } else { e };
                    assert_eq!(word_value(&aig, &vals, &out), want, "ite {c} {t:#x} {e:#x}");
                }
            }
        }
    }
}
