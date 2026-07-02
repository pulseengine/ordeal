//! Structural ops (DES-009): extract, concat, zero_ext, sign_ext.
//! Pure word plumbing — no gates.
//!
//! Words are LSB-first, so `extract` is a slice, `concat` puts the SMT-LIB
//! FIRST operand (the high bits) *after* the second in the vector, and the
//! extensions append literals above the MSB. All rules are verified against
//! the concrete evaluator (DES-001) per UV-009.

use crate::aig::{Lit, Word};

/// `extract[hi:lo]` (inclusive) — slice of the LSB-first word.
pub fn blast_extract(a: &Word, hi: u32, lo: u32) -> Word {
    debug_assert!(
        hi >= lo && (hi as usize) < a.len(),
        "blast_extract: bad range [{hi}:{lo}] for width {}",
        a.len()
    );
    a[lo as usize..=hi as usize].to_vec()
}

/// `concat` — SMT-LIB: the FIRST operand becomes the high bits.
pub fn blast_concat(hi_part: &Word, lo_part: &Word) -> Word {
    lo_part.iter().chain(hi_part).copied().collect()
}

/// `zero_ext` — append `by` FALSE literals above the MSB.
pub fn blast_zero_ext(a: &Word, by: u32) -> Word {
    let mut out = a.clone();
    out.resize(a.len() + by as usize, Lit::FALSE);
    out
}

/// `sign_ext` — replicate the sign literal `by` times.
pub fn blast_sign_ext(a: &Word, by: u32) -> Word {
    debug_assert!(!a.is_empty(), "blast_sign_ext: empty word");
    let sign = *a.last().expect("blast_sign_ext: empty word");
    let mut out = a.clone();
    out.resize(a.len() + by as usize, sign);
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aig::{Aig, word_input, word_value};
    use crate::eval::{Env, eval_bv};
    use crate::term::{BvTerm, Sort};

    fn c(value: u128, w: u32) -> Box<BvTerm> {
        Box::new(BvTerm::Const {
            value,
            sort: Sort::new(w),
        })
    }

    fn ev(t: &BvTerm) -> u128 {
        eval_bv(t, &Env::new()).unwrap()
    }

    fn xorshift(s: &mut u64) -> u64 {
        *s ^= *s << 13;
        *s ^= *s >> 7;
        *s ^= *s << 17;
        *s
    }

    /// LSB-first input pattern for a single word of `width` bits.
    fn bits(x: u128, width: u32) -> Vec<bool> {
        (0..width).map(|i| (x >> i) & 1 == 1).collect()
    }

    #[test]
    fn exhaustive_width8_extract_matches_evaluator() {
        let mut aig = Aig::new();
        let a = word_input(&mut aig, 8);
        for x in 0..=0xFFu128 {
            let vals = aig.simulate(&bits(x, 8));
            for lo in 0..8u32 {
                for hi in lo..8u32 {
                    let slice = blast_extract(&a, hi, lo);
                    assert_eq!(slice.len(), (hi - lo + 1) as usize);
                    let want = ev(&BvTerm::Extract {
                        hi,
                        lo,
                        arg: c(x, 8),
                    });
                    assert_eq!(
                        word_value(&aig, &vals, &slice),
                        want,
                        "extract[{hi}:{lo}] of {x:#04x}"
                    );
                }
            }
        }
    }

    #[test]
    fn exhaustive_width8_extensions_match_evaluator() {
        let mut aig = Aig::new();
        let a = word_input(&mut aig, 8);
        // 8 -> 16/32/64 family plus a small odd step.
        for by in [1u32, 8, 24, 56] {
            let zext = blast_zero_ext(&a, by);
            let sext = blast_sign_ext(&a, by);
            assert_eq!(zext.len(), (8 + by) as usize);
            assert_eq!(sext.len(), (8 + by) as usize);
            for x in 0..=0xFFu128 {
                let vals = aig.simulate(&bits(x, 8));
                let want_z = ev(&BvTerm::ZeroExt { by, arg: c(x, 8) });
                let want_s = ev(&BvTerm::SignExt { by, arg: c(x, 8) });
                assert_eq!(
                    word_value(&aig, &vals, &zext),
                    want_z,
                    "zero_ext {by} of {x:#04x}"
                );
                assert_eq!(
                    word_value(&aig, &vals, &sext),
                    want_s,
                    "sign_ext {by} of {x:#04x}"
                );
            }
        }
    }

    #[test]
    fn exhaustive_concat_8x4_matches_evaluator() {
        let mut aig = Aig::new();
        let hi = word_input(&mut aig, 8);
        let lo = word_input(&mut aig, 4);
        let cat = blast_concat(&hi, &lo);
        assert_eq!(cat.len(), 12, "concat width is the sum of operand widths");
        for x in 0..=0xFFu128 {
            for y in 0..=0xFu128 {
                let inputs: Vec<bool> = bits(x, 8).into_iter().chain(bits(y, 4)).collect();
                let vals = aig.simulate(&inputs);
                let want = ev(&BvTerm::Concat(c(x, 8), c(y, 4)));
                assert_eq!(
                    word_value(&aig, &vals, &cat),
                    want,
                    "concat {x:#04x} {y:#03x}"
                );
            }
        }
    }

    #[test]
    fn randomized_width32_64_all_ops_match_evaluator() {
        for width in [32u32, 64] {
            let mut aig = Aig::new();
            let a = word_input(&mut aig, width);
            let b = word_input(&mut aig, width);
            let cat = blast_concat(&a, &b);
            assert_eq!(cat.len(), 2 * width as usize);
            let mask = if width == 64 {
                u64::MAX as u128
            } else {
                (1u128 << width) - 1
            };
            let mut s: u64 = 0xDEC0_5009_0000_0000 + width as u64;
            for _ in 0..200 {
                let x = (xorshift(&mut s) as u128) & mask;
                let y = (xorshift(&mut s) as u128) & mask;
                let r = xorshift(&mut s);
                let lo = (r as u32) % width;
                let hi = lo + ((r >> 32) as u32) % (width - lo);
                let by = 1 + ((r >> 48) as u32) % (128 - width);
                let inputs: Vec<bool> = bits(x, width).into_iter().chain(bits(y, width)).collect();
                let vals = aig.simulate(&inputs);
                assert_eq!(
                    word_value(&aig, &vals, &blast_extract(&a, hi, lo)),
                    ev(&BvTerm::Extract {
                        hi,
                        lo,
                        arg: c(x, width),
                    }),
                    "extract[{hi}:{lo}] of {x:#x} width {width}"
                );
                assert_eq!(
                    word_value(&aig, &vals, &cat),
                    ev(&BvTerm::Concat(c(x, width), c(y, width))),
                    "concat {x:#x} {y:#x} width {width}"
                );
                assert_eq!(
                    word_value(&aig, &vals, &blast_zero_ext(&a, by)),
                    ev(&BvTerm::ZeroExt {
                        by,
                        arg: c(x, width),
                    }),
                    "zero_ext {by} of {x:#x} width {width}"
                );
                assert_eq!(
                    word_value(&aig, &vals, &blast_sign_ext(&a, by)),
                    ev(&BvTerm::SignExt {
                        by,
                        arg: c(x, width),
                    }),
                    "sign_ext {by} of {x:#x} width {width}"
                );
            }
        }
    }
}
