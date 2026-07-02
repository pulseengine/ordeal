//! Shifts and rotate (DES-007): barrel shifter with SMT-LIB out-of-range
//! semantics; bvrotr rotates by amount mod width.

use crate::aig::{Aig, Lit, Word};

/// Number of barrel stages (`log2 w`), checking the shared preconditions:
/// both operands have the same width `w`, and `w` is a power of two.
fn stage_count(a: &Word, b: &Word) -> usize {
    let w = a.len();
    debug_assert_eq!(w, b.len(), "shift operands must share a width");
    debug_assert!(w.is_power_of_two(), "shift width must be a power of two");
    w.trailing_zeros() as usize
}

/// `amount >= width`: OR of the amount bits above the barrel stages. Because
/// the width is a power of two, an amount is in range iff every bit at
/// position `log2 w` and above is clear.
fn out_of_range(aig: &mut Aig, b: &Word, stages: usize) -> Lit {
    b[stages..]
        .iter()
        .fold(Lit::FALSE, |acc, &bit| aig.or(acc, bit))
}

/// Barrel right-shifter: stage `k` muxes a shift by `2^k` on amount bit `k`,
/// vacated bits fill with `fill`; an out-of-range amount selects all-`fill`.
fn barrel_right(aig: &mut Aig, a: &Word, b: &Word, fill: Lit) -> Word {
    let w = a.len();
    let stages = stage_count(a, b);
    let mut cur = a.clone();
    for (k, &sel) in b.iter().enumerate().take(stages) {
        let s = 1usize << k;
        cur = (0..w)
            .map(|i| {
                let shifted = if i + s < w { cur[i + s] } else { fill };
                aig.mux(sel, shifted, cur[i])
            })
            .collect();
    }
    let oor = out_of_range(aig, b, stages);
    cur.iter().map(|&bit| aig.mux(oor, fill, bit)).collect()
}

/// `bvshl` — zero when the shift amount is ≥ width.
pub fn blast_shl(aig: &mut Aig, a: &Word, b: &Word) -> Word {
    let w = a.len();
    let stages = stage_count(a, b);
    let mut cur = a.clone();
    for (k, &sel) in b.iter().enumerate().take(stages) {
        let s = 1usize << k;
        cur = (0..w)
            .map(|i| {
                let shifted = if i >= s { cur[i - s] } else { Lit::FALSE };
                aig.mux(sel, shifted, cur[i])
            })
            .collect();
    }
    let oor = out_of_range(aig, b, stages);
    cur.iter()
        .map(|&bit| aig.mux(oor, Lit::FALSE, bit))
        .collect()
}

/// `bvlshr` — zero when the shift amount is ≥ width.
pub fn blast_lshr(aig: &mut Aig, a: &Word, b: &Word) -> Word {
    barrel_right(aig, a, b, Lit::FALSE)
}

/// `bvashr` — sign-fills; all sign bits when the amount is ≥ width.
pub fn blast_ashr(aig: &mut Aig, a: &Word, b: &Word) -> Word {
    let sign = *a.last().expect("ashr operand must be non-empty");
    barrel_right(aig, a, b, sign)
}

/// `bvrotr` — rotate right by amount mod width. Only the low `log2 w` amount
/// bits matter: the width is a power of two, so higher bits vanish mod `w`.
pub fn blast_rotr(aig: &mut Aig, a: &Word, b: &Word) -> Word {
    let w = a.len();
    let stages = stage_count(a, b);
    let mut cur = a.clone();
    for (k, &sel) in b.iter().enumerate().take(stages) {
        let s = 1usize << k;
        cur = (0..w)
            .map(|i| aig.mux(sel, cur[(i + s) % w], cur[i]))
            .collect();
    }
    cur
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
        let mask = (1u128 << w) - 1;
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
}
