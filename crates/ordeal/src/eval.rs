//! Concrete evaluator for the closed QF_BV fragment — the executable
//! SMT-LIB semantics (DES-001).
//!
//! This is the **test oracle** for every bit-blasting rule (exhaustive at
//! width 8, randomized at 32/64) and the SAT-model self-check: a returned
//! model is re-evaluated here before `check` reports `Sat`.
//!
//! Values are `u128` masked to the term width. Widths are arbitrary in
//! 1..=128 *inside* a term (an `extract` produces narrow intermediates);
//! the 8/32/64 restriction applies to the variables loom/synth declare.

use crate::term::{BoolTerm, BvTerm, Sort};
use std::collections::HashMap;

/// A variable assignment: name → concrete value (masked to the var's width).
pub type Env = HashMap<String, u128>;

/// Why evaluation (or sort-checking) failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EvalError {
    /// A free variable had no binding in the environment.
    UnboundVar(String),
    /// Operand widths disagree where SMT-LIB requires them equal.
    WidthMismatch { left: u32, right: u32 },
    /// `extract` bounds out of range or inverted (`hi < lo` or `hi >= width`).
    BadExtract { hi: u32, lo: u32, width: u32 },
    /// Width outside the supported 1..=128 range.
    UnsupportedWidth(u32),
}

fn mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

fn check_width(w: u32) -> Result<u32, EvalError> {
    if w == 0 || w > 128 {
        Err(EvalError::UnsupportedWidth(w))
    } else {
        Ok(w)
    }
}

fn same_width(a: u32, b: u32) -> Result<u32, EvalError> {
    if a == b {
        Ok(a)
    } else {
        Err(EvalError::WidthMismatch { left: a, right: b })
    }
}

/// Compute the sort (width) of a term, checking well-sortedness.
pub fn bv_sort(term: &BvTerm) -> Result<Sort, EvalError> {
    let w = match term {
        BvTerm::Const { sort, .. } | BvTerm::Var { sort, .. } => check_width(sort.width)?,
        BvTerm::Add(a, b)
        | BvTerm::Sub(a, b)
        | BvTerm::Mul(a, b)
        | BvTerm::Udiv(a, b)
        | BvTerm::And(a, b)
        | BvTerm::Or(a, b)
        | BvTerm::Xor(a, b)
        | BvTerm::Shl(a, b)
        | BvTerm::Lshr(a, b)
        | BvTerm::Ashr(a, b)
        | BvTerm::Rotr(a, b) => same_width(bv_sort(a)?.width, bv_sort(b)?.width)?,
        BvTerm::Extract { hi, lo, arg } => {
            let w = bv_sort(arg)?.width;
            if hi < lo || *hi >= w {
                return Err(EvalError::BadExtract {
                    hi: *hi,
                    lo: *lo,
                    width: w,
                });
            }
            hi - lo + 1
        }
        BvTerm::Concat(a, b) => check_width(bv_sort(a)?.width + bv_sort(b)?.width)?,
        BvTerm::ZeroExt { by, arg } | BvTerm::SignExt { by, arg } => {
            check_width(bv_sort(arg)?.width + by)?
        }
    };
    Ok(Sort::new(w))
}

/// Evaluate a bitvector term to its concrete value (masked to its width).
pub fn eval_bv(term: &BvTerm, env: &Env) -> Result<u128, EvalError> {
    let w = bv_sort(term)?.width;
    let m = mask(w);
    let v = match term {
        BvTerm::Const { value, .. } => value & m,
        BvTerm::Var { name, .. } => {
            *env.get(name)
                .ok_or_else(|| EvalError::UnboundVar(name.clone()))?
                & m
        }
        BvTerm::Add(a, b) => eval_bv(a, env)?.wrapping_add(eval_bv(b, env)?) & m,
        BvTerm::Sub(a, b) => eval_bv(a, env)?.wrapping_sub(eval_bv(b, env)?) & m,
        BvTerm::Mul(a, b) => eval_bv(a, env)?.wrapping_mul(eval_bv(b, env)?) & m,
        BvTerm::Udiv(a, b) => {
            let (x, y) = (eval_bv(a, env)?, eval_bv(b, env)?);
            // SMT-LIB: bvudiv by zero yields all-ones.
            if y == 0 { m } else { x / y }
        }
        BvTerm::And(a, b) => eval_bv(a, env)? & eval_bv(b, env)?,
        BvTerm::Or(a, b) => eval_bv(a, env)? | eval_bv(b, env)?,
        BvTerm::Xor(a, b) => eval_bv(a, env)? ^ eval_bv(b, env)?,
        BvTerm::Shl(a, b) => {
            let (x, sh) = (eval_bv(a, env)?, eval_bv(b, env)?);
            if sh >= w as u128 { 0 } else { (x << sh) & m }
        }
        BvTerm::Lshr(a, b) => {
            let (x, sh) = (eval_bv(a, env)?, eval_bv(b, env)?);
            if sh >= w as u128 { 0 } else { x >> sh }
        }
        BvTerm::Ashr(a, b) => {
            let (x, sh) = (eval_bv(a, env)?, eval_bv(b, env)?);
            let sign = (x >> (w - 1)) & 1 == 1;
            if sh >= w as u128 {
                if sign { m } else { 0 }
            } else if sign {
                // logical shift, then fill the vacated top bits with ones
                ((x >> sh) | (m & !(m >> sh))) & m
            } else {
                x >> sh
            }
        }
        BvTerm::Rotr(a, b) => {
            let (x, sh) = (eval_bv(a, env)?, eval_bv(b, env)?);
            let r = (sh % w as u128) as u32;
            if r == 0 {
                x
            } else {
                ((x >> r) | (x << (w - r))) & m
            }
        }
        BvTerm::Extract { lo, arg, .. } => (eval_bv(arg, env)? >> lo) & m,
        BvTerm::Concat(a, b) => {
            let wb = bv_sort(b)?.width;
            ((eval_bv(a, env)? << wb) | eval_bv(b, env)?) & m
        }
        BvTerm::ZeroExt { arg, .. } => eval_bv(arg, env)?,
        BvTerm::SignExt { arg, .. } => {
            let wa = bv_sort(arg)?.width;
            let x = eval_bv(arg, env)?;
            if (x >> (wa - 1)) & 1 == 1 {
                (x | (m ^ mask(wa))) & m
            } else {
                x
            }
        }
    };
    Ok(v)
}

/// Interpret a value of the given width as a signed integer.
fn to_signed(v: u128, w: u32) -> i128 {
    if w < 128 && (v >> (w - 1)) & 1 == 1 {
        (v | !mask(w)) as i128
    } else {
        v as i128
    }
}

/// Evaluate a boolean term (predicate / connective) to a concrete truth value.
pub fn eval_bool(term: &BoolTerm, env: &Env) -> Result<bool, EvalError> {
    let cmp_w = |a: &BvTerm, b: &BvTerm| -> Result<(u128, u128, u32), EvalError> {
        let w = same_width(bv_sort(a)?.width, bv_sort(b)?.width)?;
        Ok((eval_bv(a, env)?, eval_bv(b, env)?, w))
    };
    Ok(match term {
        BoolTerm::Eq(a, b) => cmp_w(a, b).map(|(x, y, _)| x == y)?,
        BoolTerm::Ne(a, b) => cmp_w(a, b).map(|(x, y, _)| x != y)?,
        BoolTerm::Ult(a, b) => cmp_w(a, b).map(|(x, y, _)| x < y)?,
        BoolTerm::Ule(a, b) => cmp_w(a, b).map(|(x, y, _)| x <= y)?,
        BoolTerm::Ugt(a, b) => cmp_w(a, b).map(|(x, y, _)| x > y)?,
        BoolTerm::Uge(a, b) => cmp_w(a, b).map(|(x, y, _)| x >= y)?,
        BoolTerm::Slt(a, b) => cmp_w(a, b).map(|(x, y, w)| to_signed(x, w) < to_signed(y, w))?,
        BoolTerm::Sle(a, b) => cmp_w(a, b).map(|(x, y, w)| to_signed(x, w) <= to_signed(y, w))?,
        BoolTerm::Sgt(a, b) => cmp_w(a, b).map(|(x, y, w)| to_signed(x, w) > to_signed(y, w))?,
        BoolTerm::Sge(a, b) => cmp_w(a, b).map(|(x, y, w)| to_signed(x, w) >= to_signed(y, w))?,
        BoolTerm::Not(t) => !eval_bool(t, env)?,
        BoolTerm::And(a, b) => eval_bool(a, env)? && eval_bool(b, env)?,
        BoolTerm::Or(a, b) => eval_bool(a, env)? || eval_bool(b, env)?,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn c(value: u128, w: u32) -> BvTerm {
        BvTerm::Const {
            value,
            sort: Sort::new(w),
        }
    }
    fn ev(t: &BvTerm) -> u128 {
        eval_bv(t, &Env::new()).unwrap()
    }
    fn evb(t: &BoolTerm) -> bool {
        eval_bool(t, &Env::new()).unwrap()
    }
    fn b(t: BvTerm) -> Box<BvTerm> {
        Box::new(t)
    }

    #[test]
    fn udiv_by_zero_is_all_ones() {
        for w in [8u32, 32, 64] {
            let q = BvTerm::Udiv(b(c(42, w)), b(c(0, w)));
            assert_eq!(ev(&q), mask(w), "width {w}");
        }
        // and 0/0 too
        assert_eq!(ev(&BvTerm::Udiv(b(c(0, 8)), b(c(0, 8)))), 0xFF);
    }

    #[test]
    fn shifts_out_of_range_saturate() {
        // shl/lshr with amount >= width give zero
        assert_eq!(ev(&BvTerm::Shl(b(c(0xAB, 8)), b(c(8, 8)))), 0);
        assert_eq!(ev(&BvTerm::Shl(b(c(0xAB, 8)), b(c(200, 8)))), 0);
        assert_eq!(ev(&BvTerm::Lshr(b(c(0xAB, 8)), b(c(9, 8)))), 0);
        // ashr fills with the sign bit
        assert_eq!(ev(&BvTerm::Ashr(b(c(0x80, 8)), b(c(8, 8)))), 0xFF);
        assert_eq!(ev(&BvTerm::Ashr(b(c(0x7F, 8)), b(c(8, 8)))), 0x00);
    }

    #[test]
    fn ashr_in_range_sign_fills() {
        assert_eq!(ev(&BvTerm::Ashr(b(c(0x80, 8)), b(c(1, 8)))), 0xC0);
        assert_eq!(ev(&BvTerm::Ashr(b(c(0x80, 8)), b(c(7, 8)))), 0xFF);
        assert_eq!(ev(&BvTerm::Ashr(b(c(0x40, 8)), b(c(1, 8)))), 0x20);
        // width 64 negative value
        let v = 0x8000_0000_0000_0000u128;
        assert_eq!(
            ev(&BvTerm::Ashr(b(c(v, 64)), b(c(4, 64)))),
            0xF800_0000_0000_0000
        );
    }

    #[test]
    fn rotr_wraps_modulo_width() {
        assert_eq!(ev(&BvTerm::Rotr(b(c(0b0000_0001, 8)), b(c(1, 8)))), 0x80);
        assert_eq!(ev(&BvTerm::Rotr(b(c(0xAB, 8)), b(c(8, 8)))), 0xAB);
        assert_eq!(ev(&BvTerm::Rotr(b(c(0xAB, 8)), b(c(0, 8)))), 0xAB);
        // amount 9 ≡ 1 (mod 8)
        assert_eq!(
            ev(&BvTerm::Rotr(b(c(0xAB, 8)), b(c(9, 8)))),
            ev(&BvTerm::Rotr(b(c(0xAB, 8)), b(c(1, 8))))
        );
    }

    #[test]
    fn structural_ops() {
        // extract[7:4] of 0xAB = 0xA
        assert_eq!(
            ev(&BvTerm::Extract {
                hi: 7,
                lo: 4,
                arg: b(c(0xAB, 8))
            }),
            0xA
        );
        // concat(0xA:4, 0xB:4) = 0xAB — first operand is the high part
        let hi4 = BvTerm::Extract {
            hi: 7,
            lo: 4,
            arg: b(c(0xA0, 8)),
        };
        let lo4 = BvTerm::Extract {
            hi: 3,
            lo: 0,
            arg: b(c(0x0B, 8)),
        };
        assert_eq!(ev(&BvTerm::Concat(b(hi4), b(lo4))), 0xAB);
        // zero_ext keeps value; sign_ext replicates the sign bit
        assert_eq!(
            ev(&BvTerm::ZeroExt {
                by: 8,
                arg: b(c(0x80, 8))
            }),
            0x0080
        );
        assert_eq!(
            ev(&BvTerm::SignExt {
                by: 8,
                arg: b(c(0x80, 8))
            }),
            0xFF80
        );
        assert_eq!(
            ev(&BvTerm::SignExt {
                by: 8,
                arg: b(c(0x7F, 8))
            }),
            0x007F
        );
    }

    #[test]
    fn signed_comparisons_on_boundaries() {
        // width 8: -128 < -1 < 0 < 127 in signed order
        let min = c(0x80, 8);
        let neg1 = c(0xFF, 8);
        let zero = c(0, 8);
        let max = c(0x7F, 8);
        assert!(evb(&BoolTerm::Slt(b(min.clone()), b(neg1.clone()))));
        assert!(evb(&BoolTerm::Slt(b(neg1.clone()), b(zero.clone()))));
        assert!(evb(&BoolTerm::Slt(b(zero.clone()), b(max.clone()))));
        // unsigned order differs: 0x80 > 0x7F unsigned
        assert!(evb(&BoolTerm::Ugt(b(min.clone()), b(max.clone()))));
        assert!(evb(&BoolTerm::Sge(b(max), b(min))));
        assert!(evb(&BoolTerm::Sle(b(neg1), b(zero))));
    }

    #[test]
    fn modular_arithmetic_wraps() {
        assert_eq!(ev(&BvTerm::Add(b(c(0xFF, 8)), b(c(1, 8)))), 0);
        assert_eq!(ev(&BvTerm::Sub(b(c(0, 8)), b(c(1, 8)))), 0xFF);
        assert_eq!(ev(&BvTerm::Mul(b(c(0x80, 8)), b(c(2, 8)))), 0);
        assert_eq!(ev(&BvTerm::Add(b(c(u64::MAX as u128, 64)), b(c(1, 64)))), 0);
    }

    #[test]
    fn width64_reference_cross_check() {
        // Deterministic LCG-generated cases cross-checked against u64/i64
        // native arithmetic — the evaluator must agree with the machine.
        let mut s: u64 = 0x2545F4914F6CDD1D;
        let mut next = move || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        };
        for _ in 0..1000 {
            let (x, y) = (next(), next());
            let (tx, ty) = (c(x as u128, 64), c(y as u128, 64));
            assert_eq!(
                ev(&BvTerm::Add(b(tx.clone()), b(ty.clone()))),
                x.wrapping_add(y) as u128
            );
            assert_eq!(
                ev(&BvTerm::Sub(b(tx.clone()), b(ty.clone()))),
                x.wrapping_sub(y) as u128
            );
            assert_eq!(
                ev(&BvTerm::Mul(b(tx.clone()), b(ty.clone()))),
                x.wrapping_mul(y) as u128
            );
            let d = if y == 0 { u64::MAX } else { x / y };
            assert_eq!(ev(&BvTerm::Udiv(b(tx.clone()), b(ty.clone()))), d as u128);
            let sh = y % 67; // exercise out-of-range too
            let shl = if sh >= 64 { 0 } else { x << sh };
            assert_eq!(
                ev(&BvTerm::Shl(b(tx.clone()), b(c(sh as u128, 64)))),
                shl as u128
            );
            let ashr = if sh >= 64 {
                ((x as i64) >> 63) as u64
            } else {
                ((x as i64) >> sh) as u64
            };
            assert_eq!(
                ev(&BvTerm::Ashr(b(tx.clone()), b(c(sh as u128, 64)))),
                ashr as u128
            );
            let rr = x.rotate_right((y % 64) as u32);
            assert_eq!(
                ev(&BvTerm::Rotr(b(tx.clone()), b(c((y % 64) as u128, 64)))),
                rr as u128
            );
            assert_eq!(
                evb(&BoolTerm::Slt(b(tx.clone()), b(ty.clone()))),
                (x as i64) < (y as i64)
            );
            assert_eq!(evb(&BoolTerm::Ult(b(tx), b(ty))), x < y);
        }
    }

    #[test]
    fn unbound_var_and_width_mismatch_error() {
        let x = BvTerm::Var {
            name: "x".into(),
            sort: Sort::new(8),
        };
        assert_eq!(
            eval_bv(&x, &Env::new()),
            Err(EvalError::UnboundVar("x".into()))
        );
        let bad = BvTerm::Add(b(c(1, 8)), b(c(1, 32)));
        assert_eq!(
            eval_bv(&bad, &Env::new()),
            Err(EvalError::WidthMismatch { left: 8, right: 32 })
        );
        let bad_ex = BvTerm::Extract {
            hi: 8,
            lo: 0,
            arg: b(c(0, 8)),
        };
        assert!(matches!(
            eval_bv(&bad_ex, &Env::new()),
            Err(EvalError::BadExtract { .. })
        ));
    }
}
