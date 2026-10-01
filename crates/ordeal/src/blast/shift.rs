//! Shifts and rotate (DES-007) — bridges to the Lean-proven rules in
//! `crate::blast_kernel` (issue #192 phase 2; the rule bodies that used to
//! live here are gone, see `blast/mod.rs`).
//!
//! Barrel shifter with SMT-LIB out-of-range semantics; `bvrotr` rotates by
//! amount mod width. Correct at EVERY width 1..=128: `stage_count` is
//! `ceil(log2 w)` (`blast_kernel::stage_count`, proved exact in Lean's
//! `stage_count_spec`), the out-of-range test covers the amount bits above
//! the stages, and `rotr` reduces the amount mod `w` with the proven
//! `blast_urem` at non-power-of-two widths. Proven in
//! `lean/BlasterShift.lean` / `lean/BlasterRotr.lean`.
//!
//! SOUNDNESS history (fixed 0.22.1): the stage count used to be
//! `w.trailing_zeros()`, guarded only by a `debug_assert!(w.is_power_of_two())`,
//! so release builds built too few stages at non-power-of-two widths (zero at
//! w = 3) and e.g. `(bvshl #b001 #b001)` at width 3 was encoded as 0 — a
//! satisfiable query came back `unsat` with a VALID certificate, because the
//! checker certifies the CNF it is given. The exhaustive every-width tests
//! below (VER-049) pin the fix.

use crate::aig::{Aig, Word};
use crate::blast::{Scratch, word2};
use crate::blast_kernel as k;

/// `bvshl` — zero when the shift amount is ≥ width.
pub fn blast_shl(aig: &mut Aig, a: &Word, b: &Word) -> Word {
    word2(aig, &mut Scratch::default(), a, b, k::blast_shl)
}

/// `bvlshr` — zero when the shift amount is ≥ width.
pub fn blast_lshr(aig: &mut Aig, a: &Word, b: &Word) -> Word {
    word2(aig, &mut Scratch::default(), a, b, k::blast_lshr)
}

/// `bvashr` — sign-fills; all sign bits when the amount is ≥ width.
pub fn blast_ashr(aig: &mut Aig, a: &Word, b: &Word) -> Word {
    word2(aig, &mut Scratch::default(), a, b, k::blast_ashr)
}

/// `bvrotr` — rotate right by amount mod width.
pub fn blast_rotr(aig: &mut Aig, a: &Word, b: &Word) -> Word {
    word2(aig, &mut Scratch::default(), a, b, k::blast_rotr)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aig::{word_input, word_value};
    use crate::eval::{Env, eval_bv};
    use crate::term::{BvTerm, Sort};

    type Ctor = fn(Box<BvTerm>, Box<BvTerm>) -> BvTerm;

    /// The concrete SMT-LIB oracle: `op` applied to width-`w` constants.
    fn oracle(op: Ctor, a: u128, b: u128, w: u32) -> u128 {
        let c = |value: u128| {
            Box::new(BvTerm::Const {
                value,
                sort: Sort::new(w),
            })
        };
        eval_bv(&op(c(a), c(b)), &Env::new()).expect("oracle eval")
    }

    /// One AIG with two width-`w` input words (bit `i` of `a` is input `i`,
    /// bit `i` of `b` is input `w + i`), each op blasted once.
    fn blast_all(w: u32) -> (Aig, [(&'static str, Ctor, Word); 4]) {
        let mut aig = Aig::new();
        let a = word_input(&mut aig, w);
        let b = word_input(&mut aig, w);
        let ops: [(&'static str, Ctor, Word); 4] = [
            ("shl", BvTerm::Shl, blast_shl(&mut aig, &a, &b)),
            ("lshr", BvTerm::Lshr, blast_lshr(&mut aig, &a, &b)),
            ("ashr", BvTerm::Ashr, blast_ashr(&mut aig, &a, &b)),
            ("rotr", BvTerm::Rotr, blast_rotr(&mut aig, &a, &b)),
        ];
        (aig, ops)
    }

    /// Simulate `(a, b)` and compare every blasted op against the oracle.
    fn check(aig: &Aig, ops: &[(&'static str, Ctor, Word); 4], a: u128, b: u128, w: u32) {
        let inputs: Vec<bool> = (0..w)
            .map(|i| (a >> i) & 1 == 1)
            .chain((0..w).map(|i| (b >> i) & 1 == 1))
            .collect();
        let values = aig.simulate(&inputs);
        for (name, ctor, word) in ops {
            let got = word_value(aig, &values, word);
            let want = oracle(*ctor, a, b, w);
            assert_eq!(got, want, "{name} w={w} a={a:#x} b={b:#x}");
        }
    }

    /// UV-007: exhaustive at width 8 — all 65536 `(a, b)` pairs, which
    /// includes every out-of-range amount `8..=255`.
    #[test]
    fn exhaustive_width_8() {
        let (aig, ops) = blast_all(8);
        for a in 0u128..256 {
            for b in 0u128..256 {
                check(&aig, &ops, a, b, 8);
            }
        }
    }

    struct XorShift64(u64);

    impl XorShift64 {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }

        fn next_u128(&mut self) -> u128 {
            ((self.next() as u128) << 64) | self.next() as u128
        }
    }

    /// UV-007: 200 seeded cases per op at the given width, mixing in-range
    /// amounts, exactly-`w`, and huge (far out-of-range) amounts.
    fn randomized(w: u32, seed: u64) {
        let (aig, ops) = blast_all(w);
        let mask = if w == 128 {
            u128::MAX
        } else {
            (1u128 << w) - 1
        };
        let mut rng = XorShift64(seed);
        for case in 0..200u32 {
            let a = rng.next_u128() & mask;
            let raw = rng.next_u128() & mask;
            let b = match case % 4 {
                // In-range amounts, biased to half the cases.
                0 | 1 => raw % w as u128,
                // Exactly the width: the smallest out-of-range amount.
                2 => w as u128,
                // Huge: OR-ing in `w + 1` forces the amount above `w`.
                _ => (raw | (w as u128 + 1)) & mask,
            };
            check(&aig, &ops, a, b, w);
        }
    }

    #[test]
    fn randomized_width_32() {
        randomized(32, 0xDE50_0701);
    }

    #[test]
    fn randomized_width_64() {
        randomized(64, 0xDE50_0702);
    }

    // rivet: verifies VER-049
    /// Soundness regression (0.22.1): EXHAUSTIVE at every width 1..=7 —
    /// all `(a, b)` pairs, including every out-of-range amount. Before the
    /// fix, release builds encoded non-power-of-two widths wrongly (zero
    /// barrel stages at w = 3); the existing tests only ever tried 8/32/64.
    #[test]
    fn exhaustive_every_width_1_to_7() {
        for w in 1u32..=7 {
            let (aig, ops) = blast_all(w);
            for a in 0u128..(1 << w) {
                for b in 0u128..(1 << w) {
                    check(&aig, &ops, a, b, w);
                }
            }
        }
    }

    /// Soundness regression (0.22.1): 200 seeded cases per op at EVERY
    /// width 9..=128 (power-of-two or not), mixing in-range, exactly-`w`
    /// and far out-of-range amounts.
    #[test]
    fn randomized_every_width_9_to_128() {
        for w in 9u32..=128 {
            randomized(w, 0xDE50_0800 ^ u64::from(w));
        }
    }
}
