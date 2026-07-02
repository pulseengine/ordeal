//! Add/sub and the eight ordered comparisons (DES-006).
//!
//! `bvadd`/`bvsub` are a ripple-carry adder (truncated, modular); `bvsub` is
//! `a + !b + 1`. `bvult` is the borrow of that subtraction — the complement
//! of the carry-out of `a + !b + 1` — and the remaining unsigned orders are
//! derived from it. Signed orders reduce to unsigned with both sign bits
//! flipped (order-embedding of two's complement into unsigned).
//!
//! Verified against the concrete evaluator (DES-001) exhaustively at width 8
//! and randomized at widths 32/64 (UV-006).

use crate::aig::{Aig, Lit, Word};

/// Panic on the malformed inputs a blasting rule must never see.
fn check_operands(a: &Word, b: &Word) {
    assert!(!a.is_empty(), "arith blasting: empty word");
    assert_eq!(a.len(), b.len(), "arith blasting: width mismatch");
}

/// Ripple-carry chain: returns the truncated sum and the final carry-out.
///
/// Per bit: `sum = a ^ b ^ cin`, `cout = (a & b) | (cin & (a ^ b))`.
fn ripple_carry(aig: &mut Aig, a: &Word, b: &Word, carry_in: Lit) -> (Word, Lit) {
    let mut carry = carry_in;
    let mut sum = Word::with_capacity(a.len());
    for (&x, &y) in a.iter().zip(b) {
        let p = aig.xor(x, y);
        sum.push(aig.xor(p, carry));
        let g = aig.and(x, y);
        let t = aig.and(p, carry);
        carry = aig.or(g, t);
    }
    (sum, carry)
}

/// The word with its most significant (sign) bit complemented.
fn flip_sign(w: &Word) -> Word {
    let mut v = w.clone();
    let msb = v.len() - 1;
    v[msb] = v[msb].not();
    v
}

/// `bvadd` — ripple-carry adder.
pub fn blast_add(aig: &mut Aig, a: &Word, b: &Word) -> Word {
    check_operands(a, b);
    ripple_carry(aig, a, b, Lit::FALSE).0
}

/// `bvsub` — add of two's complement (invert + carry-in 1).
pub fn blast_sub(aig: &mut Aig, a: &Word, b: &Word) -> Word {
    check_operands(a, b);
    let not_b: Word = b.iter().map(|&l| l.not()).collect();
    ripple_carry(aig, a, &not_b, Lit::TRUE).0
}

/// `bvult` — unsigned less-than via the subtraction borrow chain.
///
/// `a < b` iff `a - b` borrows, i.e. the carry-out of `a + !b + 1` is 0.
pub fn blast_ult(aig: &mut Aig, a: &Word, b: &Word) -> Lit {
    check_operands(a, b);
    let not_b: Word = b.iter().map(|&l| l.not()).collect();
    ripple_carry(aig, a, &not_b, Lit::TRUE).1.not()
}

/// `bvule` — `a <= b` iff not `b < a`.
pub fn blast_ule(aig: &mut Aig, a: &Word, b: &Word) -> Lit {
    blast_ult(aig, b, a).not()
}

/// `bvugt` — `a > b` iff `b < a`.
pub fn blast_ugt(aig: &mut Aig, a: &Word, b: &Word) -> Lit {
    blast_ult(aig, b, a)
}

/// `bvuge` — `a >= b` iff not `a < b`.
pub fn blast_uge(aig: &mut Aig, a: &Word, b: &Word) -> Lit {
    blast_ult(aig, a, b).not()
}

/// `bvslt` — signed: unsigned compare with sign bits flipped.
///
/// Adding `2^(w-1)` (= flipping the MSB) maps two's-complement order onto
/// unsigned order, so `slt(a, b) = ult(a ^ MSB, b ^ MSB)`.
pub fn blast_slt(aig: &mut Aig, a: &Word, b: &Word) -> Lit {
    check_operands(a, b);
    blast_ult(aig, &flip_sign(a), &flip_sign(b))
}

/// `bvsle` — `a <=s b` iff not `b <s a`.
pub fn blast_sle(aig: &mut Aig, a: &Word, b: &Word) -> Lit {
    blast_slt(aig, b, a).not()
}

/// `bvsgt` — `a >s b` iff `b <s a`.
pub fn blast_sgt(aig: &mut Aig, a: &Word, b: &Word) -> Lit {
    blast_slt(aig, b, a)
}

/// `bvsge` — `a >=s b` iff not `a <s b`.
pub fn blast_sge(aig: &mut Aig, a: &Word, b: &Word) -> Lit {
    blast_slt(aig, a, b).not()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aig::{word_input, word_value};
    use crate::eval::{Env, eval_bool, eval_bv};
    use crate::term::{BoolTerm, BvTerm, Sort};

    /// Constructor of a binary `BvTerm` / `BoolTerm` op, for table-driven tests.
    type MkBv = fn(Box<BvTerm>, Box<BvTerm>) -> BvTerm;
    type MkBool = fn(Box<BvTerm>, Box<BvTerm>) -> BoolTerm;

    fn c(value: u128, w: u32) -> Box<BvTerm> {
        Box::new(BvTerm::Const {
            value,
            sort: Sort::new(w),
        })
    }

    /// All DES-006 ops blasted once over two shared input words.
    struct Blasted {
        width: u32,
        add: Word,
        sub: Word,
        ult: Lit,
        ule: Lit,
        ugt: Lit,
        uge: Lit,
        slt: Lit,
        sle: Lit,
        sgt: Lit,
        sge: Lit,
    }

    /// One AIG, inputs in word order: bit i of `a` is input i, bit i of `b`
    /// is input `width + i`.
    fn blast_all(width: u32) -> (Aig, Blasted) {
        let mut aig = Aig::new();
        let a = word_input(&mut aig, width);
        let b = word_input(&mut aig, width);
        let blasted = Blasted {
            width,
            add: blast_add(&mut aig, &a, &b),
            sub: blast_sub(&mut aig, &a, &b),
            ult: blast_ult(&mut aig, &a, &b),
            ule: blast_ule(&mut aig, &a, &b),
            ugt: blast_ugt(&mut aig, &a, &b),
            uge: blast_uge(&mut aig, &a, &b),
            slt: blast_slt(&mut aig, &a, &b),
            sle: blast_sle(&mut aig, &a, &b),
            sgt: blast_sgt(&mut aig, &a, &b),
            sge: blast_sge(&mut aig, &a, &b),
        };
        (aig, blasted)
    }

    /// Simulate one `(x, y)` pair and compare every op against the DES-001
    /// evaluator on constant terms.
    fn check_case(aig: &Aig, bl: &Blasted, x: u128, y: u128) {
        let w = bl.width;
        let inputs: Vec<bool> = (0..w)
            .map(|i| (x >> i) & 1 == 1)
            .chain((0..w).map(|i| (y >> i) & 1 == 1))
            .collect();
        let vals = aig.simulate(&inputs);
        let env = Env::new();

        let bv_ops: [(&str, &Word, MkBv); 2] =
            [("add", &bl.add, BvTerm::Add), ("sub", &bl.sub, BvTerm::Sub)];
        for (name, word, mk) in bv_ops {
            let expect = eval_bv(&mk(c(x, w), c(y, w)), &env).unwrap();
            let got = word_value(aig, &vals, word);
            assert_eq!(got, expect, "{name} w={w} x={x:#x} y={y:#x}");
        }

        let bool_ops: [(&str, Lit, MkBool); 8] = [
            ("ult", bl.ult, BoolTerm::Ult),
            ("ule", bl.ule, BoolTerm::Ule),
            ("ugt", bl.ugt, BoolTerm::Ugt),
            ("uge", bl.uge, BoolTerm::Uge),
            ("slt", bl.slt, BoolTerm::Slt),
            ("sle", bl.sle, BoolTerm::Sle),
            ("sgt", bl.sgt, BoolTerm::Sgt),
            ("sge", bl.sge, BoolTerm::Sge),
        ];
        for (name, lit, mk) in bool_ops {
            let expect = eval_bool(&mk(c(x, w), c(y, w)), &env).unwrap();
            let got = aig.lit_value(&vals, lit);
            assert_eq!(got, expect, "{name} w={w} x={x:#x} y={y:#x}");
        }
    }

    /// UV-006 measure 1: exhaustive at width 8 — all 65536 pairs, one AIG.
    #[test]
    fn exhaustive_width8_matches_evaluator() {
        let (aig, bl) = blast_all(8);
        for x in 0..=0xFFu128 {
            for y in 0..=0xFFu128 {
                check_case(&aig, &bl, x, y);
            }
        }
    }

    /// UV-006 measure 2: randomized at widths 32/64 (seeded xorshift), with
    /// the signed boundary values paired against random values.
    #[test]
    fn randomized_width32_64_matches_evaluator() {
        for w in [32u32, 64] {
            let (aig, bl) = blast_all(w);
            let m: u128 = if w == 128 { u128::MAX } else { (1 << w) - 1 };
            let mut s: u64 = 0x9E3779B97F4A7C15 ^ u64::from(w);
            let mut next = move || {
                s ^= s << 13;
                s ^= s >> 7;
                s ^= s << 17;
                s as u128 & m
            };
            for _ in 0..200 {
                check_case(&aig, &bl, next(), next());
            }
            // Signed boundaries: 0, 1, MAX (0x7F..), MIN (0x80..), all-ones.
            let boundaries = [0u128, 1, m >> 1, 1 << (w - 1), m];
            for &edge in &boundaries {
                for _ in 0..10 {
                    check_case(&aig, &bl, edge, next());
                    check_case(&aig, &bl, next(), edge);
                }
                for &other in &boundaries {
                    check_case(&aig, &bl, edge, other);
                }
            }
        }
    }

    #[test]
    #[should_panic(expected = "width mismatch")]
    fn width_mismatch_panics() {
        let mut aig = Aig::new();
        let a = word_input(&mut aig, 8);
        let b = word_input(&mut aig, 4);
        let _ = blast_add(&mut aig, &a, &b);
    }

    #[test]
    #[should_panic(expected = "empty word")]
    fn empty_word_panics() {
        let mut aig = Aig::new();
        let _ = blast_ult(&mut aig, &Word::new(), &Word::new());
    }
}
