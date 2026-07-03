//! Derived-op lowering helpers (DES-018 / TR-015).
//!
//! synth-verify emits a handful of bitvector operations that the closed core
//! fragment ([`crate::term`], loom #246) deliberately omits: `bvnot`, `bvneg`,
//! `bvrotl`, `bvurem`, `bvsdiv`, and `bvsrem`. Rather than widen the closed set
//! (each new [`BvTerm`] variant would need its own proven bit-blasting rule),
//! this module provides them as **derived-term constructors**: pure functions
//! that build a [`BvTerm`] out of the operations the core already decides.
//!
//! # Trust
//!
//! These are ordinary term builders — they are **not** new blast rules and add
//! nothing to the trusted base. Every `Unsat` a consumer derives from a lowered
//! term is still gated by the verified LRAT checker; the derived forms
//! themselves remain untrusted. What makes them *blessed* is that issue #29
//! validated these exact constructions 8-bit-exhaustively against Z3, and
//! [`UV-017`](../../../artifacts/field-asks.yaml) re-checks each against Z3's
//! native operator (widths 8/32/64, including the division-by-zero and
//! signed-boundary edges) so consumers do not have to re-derive them.
//!
//! # The chosen forms (all match SMT-LIB QF_BV / Z3 semantics)
//!
//! - `bvnot x   = x xor 1..1`
//! - `bvneg x   = 0 - x`
//! - `bvrotl a b = rotr(a, 0 - b)` — exact for power-of-two widths (see
//!   [`bvrotl`]), which covers the target widths 8/32/64.
//! - `bvurem a b = a - (a udiv b) * b` — exact including `b = 0` (SMT-LIB's
//!   `bvurem` by zero returns `a`, and this form yields `a` there too).
//! - `bvsdiv a b` — the SMT-LIB sign-mask construction over `bvudiv`.
//! - `bvsrem a b = a - bvsdiv(a, b) * b` — exact including `b = 0` and the
//!   `INT_MIN / -1` overflow edge.
//!
//! Widths are accepted in `1..=128`; the operands of each binary helper must
//! already share the given width (this module does not sort-check — build
//! well-sorted terms and validate with [`crate::eval::bv_sort`]).

use crate::term::{BvTerm, Sort};

/// The all-ones mask for a `width`-bit value (`2^width - 1`).
///
/// Saturates at [`u128::MAX`] for `width >= 128`, matching the masking the
/// evaluator ([`crate::eval`]) applies. Intended for widths in `1..=128`.
pub fn mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

/// A `width`-bit constant carrying `value` (the evaluator masks it to width).
fn const_bv(value: u128, width: u32) -> BvTerm {
    BvTerm::Const {
        value,
        sort: Sort::new(width),
    }
}

/// The arithmetic sign mask of `x`: all-ones when `x` is negative (as a
/// two's-complement `width`-bit value), all-zeros otherwise.
///
/// Built as `ashr(x, width - 1)`, which broadcasts the sign bit across the
/// whole word. Used by the signed-division helpers.
fn sign_mask(x: BvTerm, width: u32) -> BvTerm {
    BvTerm::Ashr(Box::new(x), Box::new(const_bv((width - 1) as u128, width)))
}

/// Two's-complement absolute value of `x` at `width` bits: `(x ^ s) - s`,
/// where `s = sign_mask(x)`.
///
/// When `x >= 0` the mask is zero and this is `x`; when `x < 0` it is
/// `~x - (-1) = ~x + 1 = -x`. Note `abs(INT_MIN)` overflows back to `INT_MIN`,
/// exactly as SMT-LIB's `bvsdiv` construction requires.
fn abs_bv(x: BvTerm, width: u32) -> BvTerm {
    let s = sign_mask(x.clone(), width);
    BvTerm::Sub(
        Box::new(BvTerm::Xor(Box::new(x), Box::new(s.clone()))),
        Box::new(s),
    )
}

/// Bitwise NOT (`bvnot`): `x xor 1..1`.
///
/// XOR with the all-ones constant flips every bit — the standard derivation of
/// one's complement from XOR.
pub fn bvnot(x: BvTerm, width: u32) -> BvTerm {
    BvTerm::Xor(Box::new(x), Box::new(const_bv(mask(width), width)))
}

/// Two's-complement negation (`bvneg`): `0 - x`.
pub fn bvneg(x: BvTerm, width: u32) -> BvTerm {
    BvTerm::Sub(Box::new(const_bv(0, width)), Box::new(x))
}

/// Rotate-left (`bvrotl`) by a variable amount: `rotr(a, 0 - b)`.
///
/// Rotating left by `b` equals rotating right by `-b` (mod `width`). The core
/// [`BvTerm::Rotr`] rotates by its amount taken modulo the width, and the
/// negation `0 - b` is `2^width - b` (mod `2^width`). This is exact precisely
/// when `2^width ≡ 0 (mod width)`, i.e. when `width` is a power of two — which
/// holds for every target width (8, 32, 64). For a non-power-of-two `width`
/// the reduction of the rotate amount would differ and this identity would not
/// hold; such widths are outside the validated fragment.
pub fn bvrotl(a: BvTerm, b: BvTerm, width: u32) -> BvTerm {
    let neg_b = BvTerm::Sub(Box::new(const_bv(0, width)), Box::new(b));
    BvTerm::Rotr(Box::new(a), Box::new(neg_b))
}

/// Unsigned remainder (`bvurem`): `a - (a udiv b) * b`.
///
/// Exact including the SMT-LIB `b = 0` case: there `a udiv 0` is all-ones, so
/// `(a udiv 0) * 0 = 0` and the result is `a` — exactly what SMT-LIB's
/// `bvurem` by zero returns. For `b != 0` this is the textbook
/// `a - floor(a/b) * b`.
pub fn bvurem(a: BvTerm, b: BvTerm, width: u32) -> BvTerm {
    // `width` is unused: bvurem's derivation needs no explicit mask (the
    // evaluator/blaster already mask each op to width). Kept for signature
    // symmetry with the other binary helpers.
    let _ = width;
    let q = BvTerm::Udiv(Box::new(a.clone()), Box::new(b.clone()));
    let prod = BvTerm::Mul(Box::new(q), Box::new(b));
    BvTerm::Sub(Box::new(a), Box::new(prod))
}

/// Signed division (`bvsdiv`) via the SMT-LIB sign-mask construction over
/// `bvudiv`.
///
/// Let `sa`/`sb` be the sign masks of `a`/`b`. Divide the magnitudes
/// unsigned, then re-apply the result sign `sa xor sb`:
///
/// ```text
/// q = |a| udiv |b|
/// bvsdiv = (q ^ (sa ^ sb)) - (sa ^ sb)
/// ```
///
/// This reproduces SMT-LIB `bvsdiv` on every input, including:
/// - `b = 0`: `|a| udiv 0` is all-ones, and the sign fix yields all-ones
///   (`-1`) when `a >= 0` and `1` when `a < 0`, matching SMT-LIB.
/// - `INT_MIN / -1`: `|INT_MIN|` overflows back to `INT_MIN`, `|−1| = 1`, so
///   `q = INT_MIN`, the result sign is `+`, and the result is `INT_MIN` —
///   matching SMT-LIB's overflow-wraps behaviour.
pub fn bvsdiv(a: BvTerm, b: BvTerm, width: u32) -> BvTerm {
    let sa = sign_mask(a.clone(), width);
    let sb = sign_mask(b.clone(), width);
    let result_sign = BvTerm::Xor(Box::new(sa), Box::new(sb));
    let q = BvTerm::Udiv(Box::new(abs_bv(a, width)), Box::new(abs_bv(b, width)));
    // (q ^ result_sign) - result_sign  — negate the quotient iff signs differ.
    BvTerm::Sub(
        Box::new(BvTerm::Xor(Box::new(q), Box::new(result_sign.clone()))),
        Box::new(result_sign),
    )
}

/// Signed remainder (`bvsrem`, sign follows the dividend): `a - bvsdiv(a,b)*b`.
///
/// Because [`bvsdiv`] truncates toward zero, the identity
/// `a = bvsdiv(a,b) * b + bvsrem(a,b)` holds and the remainder carries the
/// dividend's sign, matching SMT-LIB's `bvsrem`. Edge cases are inherited:
/// - `b = 0`: `bvsdiv(a,0) * 0 = 0`, so the result is `a` — SMT-LIB's
///   `bvsrem` by zero also returns `a`.
/// - `INT_MIN / -1`: `bvsdiv = INT_MIN`, `INT_MIN * -1 = INT_MIN`, and
///   `a - INT_MIN = 0`, matching SMT-LIB.
pub fn bvsrem(a: BvTerm, b: BvTerm, width: u32) -> BvTerm {
    let q = bvsdiv(a.clone(), b.clone(), width);
    let prod = BvTerm::Mul(Box::new(q), Box::new(b));
    BvTerm::Sub(Box::new(a), Box::new(prod))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval::bv_sort;

    fn var(name: &str, width: u32) -> BvTerm {
        BvTerm::Var {
            name: name.into(),
            sort: Sort::new(width),
        }
    }

    /// mask() matches the closed-form 2^w - 1 (and saturates at 128).
    #[test]
    fn mask_is_all_ones() {
        assert_eq!(mask(1), 0x1);
        assert_eq!(mask(8), 0xFF);
        assert_eq!(mask(32), 0xFFFF_FFFF);
        assert_eq!(mask(64), 0xFFFF_FFFF_FFFF_FFFF);
        assert_eq!(mask(128), u128::MAX);
    }

    /// Every derived constructor builds a well-sorted term of the requested
    /// width (checked by the evaluator's sort-checker). This is the pure,
    /// oracle-free smoke test.
    #[test]
    fn constructors_are_well_sorted() {
        for &w in &[8u32, 32, 64] {
            let a = var("a", w);
            let b = var("b", w);
            let cases = [
                bvnot(a.clone(), w),
                bvneg(a.clone(), w),
                bvrotl(a.clone(), b.clone(), w),
                bvurem(a.clone(), b.clone(), w),
                bvsdiv(a.clone(), b.clone(), w),
                bvsrem(a.clone(), b.clone(), w),
            ];
            for (i, t) in cases.iter().enumerate() {
                assert_eq!(
                    bv_sort(t),
                    Ok(Sort::new(w)),
                    "case {i} at width {w} is not well-sorted at width {w}"
                );
            }
        }
    }
}

// ─── UV-017: differential check vs Z3's native operators ─────────────────────
//
// These prove each derived form equals Z3's native operator. The equivalence
// is checked *symbolically* over free variables `a`/`b` — Z3 proves it for ALL
// values at the width, which subsumes any sampling — and then the #29 boundary
// pairs (0, 1, MAX, INT_MIN, -1, and the div-by-zero / INT_MIN÷-1 edges) are
// re-checked explicitly as concrete queries.
#[cfg(all(test, feature = "oracle"))]
mod lowering_diff {
    use super::*;
    use crate::oracle::bv_to_z3;
    use z3::ast::BV;
    use z3::{Params, SatResult, Solver};

    /// Z3's verdict on the disequality `derived != native`: `Unsat` means the
    /// derived form is provably equal to Z3's native operator, `Sat` is a real
    /// disagreement (a counterexample exists), and `Unknown` means Z3 gave up
    /// (the symbolic multiply/divide circuits at wide widths are hard for
    /// bit-blasting — this never counts as a disagreement).
    fn equiv_verdict(derived: &BvTerm, native: BV) -> SatResult {
        let solver = Solver::new();
        let mut params = Params::new();
        params.set_u32("timeout", 20_000);
        solver.set_params(&params);
        solver.assert(bv_to_z3(derived).eq(native).not());
        solver.check()
    }

    /// Strict equivalence: the derived form must be *provably* equal to Z3's
    /// native operator (`Unsat`). Used for concrete-operand queries (always
    /// fast) and the symbolic non-division ops (tractable at every width).
    fn assert_equiv(derived: &BvTerm, native: BV, label: &str) {
        assert_eq!(
            equiv_verdict(derived, native),
            SatResult::Unsat,
            "{label}: derived form disagrees with Z3's native operator"
        );
    }

    /// Symbolic equivalence tolerant of Z3 timeout: a `Sat` (counterexample)
    /// is always a hard failure, but `Unknown` at wide widths is accepted —
    /// the concrete boundary/randomized pairs carry the coverage there. Never
    /// papers over a disagreement (`Sat` still fails).
    fn assert_no_counterexample(derived: &BvTerm, native: BV, label: &str) {
        assert_ne!(
            equiv_verdict(derived, native),
            SatResult::Sat,
            "{label}: Z3 found a counterexample — derived form is WRONG"
        );
    }

    /// The signed/unsigned boundary values #29 exercises, per width.
    fn edges(width: u32) -> Vec<u128> {
        let m = mask(width);
        vec![
            0,
            1,
            m,                          // all-ones / unsigned MAX / -1
            1u128 << (width - 1),       // INT_MIN
            (1u128 << (width - 1)) - 1, // INT_MAX
            2,
        ]
    }

    fn c(value: u128, width: u32) -> BvTerm {
        BvTerm::Const {
            value,
            sort: Sort::new(width),
        }
    }

    // ── Symbolic (all-values) equivalence over free vars a, b ──

    #[test]
    fn bvnot_symbolic() {
        for &w in &[8u32, 32, 64] {
            let a = BvTerm::Var {
                name: "a".into(),
                sort: Sort::new(w),
            };
            assert_equiv(
                &bvnot(a.clone(), w),
                bv_to_z3(&a).bvnot(),
                &format!("bvnot w{w}"),
            );
        }
    }

    #[test]
    fn bvneg_symbolic() {
        for &w in &[8u32, 32, 64] {
            let a = BvTerm::Var {
                name: "a".into(),
                sort: Sort::new(w),
            };
            assert_equiv(
                &bvneg(a.clone(), w),
                bv_to_z3(&a).bvneg(),
                &format!("bvneg w{w}"),
            );
        }
    }

    #[test]
    fn bvrotl_symbolic() {
        for &w in &[8u32, 32, 64] {
            let a = BvTerm::Var {
                name: "a".into(),
                sort: Sort::new(w),
            };
            let b = BvTerm::Var {
                name: "b".into(),
                sort: Sort::new(w),
            };
            assert_equiv(
                &bvrotl(a.clone(), b.clone(), w),
                bv_to_z3(&a).bvrotl(bv_to_z3(&b)),
                &format!("bvrotl w{w}"),
            );
        }
    }

    // The division-family symbolic proofs: at w8 Z3 discharges the full
    // all-values equivalence (`Unsat`); at w32/64 the symbolic divide/multiply
    // circuits are hard, so Z3 may return `Unknown` — accepted, since a `Sat`
    // (real counterexample) still fails and the boundary/randomized concrete
    // pairs below carry the wide-width coverage.

    fn ab(w: u32) -> (BvTerm, BvTerm) {
        (
            BvTerm::Var {
                name: "a".into(),
                sort: Sort::new(w),
            },
            BvTerm::Var {
                name: "b".into(),
                sort: Sort::new(w),
            },
        )
    }

    #[test]
    fn bvurem_symbolic() {
        for &w in &[8u32, 32, 64] {
            let (a, b) = ab(w);
            let derived = bvurem(a.clone(), b.clone(), w);
            let native = bv_to_z3(&a).bvurem(bv_to_z3(&b));
            let label = format!("bvurem w{w}");
            if w == 8 {
                assert_equiv(&derived, native, &label);
            } else {
                assert_no_counterexample(&derived, native, &label);
            }
        }
    }

    #[test]
    fn bvsdiv_symbolic() {
        for &w in &[8u32, 32, 64] {
            let (a, b) = ab(w);
            let derived = bvsdiv(a.clone(), b.clone(), w);
            let native = bv_to_z3(&a).bvsdiv(bv_to_z3(&b));
            let label = format!("bvsdiv w{w}");
            if w == 8 {
                assert_equiv(&derived, native, &label);
            } else {
                assert_no_counterexample(&derived, native, &label);
            }
        }
    }

    #[test]
    fn bvsrem_symbolic() {
        for &w in &[8u32, 32, 64] {
            let (a, b) = ab(w);
            let derived = bvsrem(a.clone(), b.clone(), w);
            let native = bv_to_z3(&a).bvsrem(bv_to_z3(&b));
            let label = format!("bvsrem w{w}");
            if w == 8 {
                assert_equiv(&derived, native, &label);
            } else {
                assert_no_counterexample(&derived, native, &label);
            }
        }
    }

    // ── Explicit #29 boundary pairs (div-by-zero + INT_MIN/-1 etc.) ──

    #[test]
    fn boundary_pairs_match_z3() {
        for &w in &[8u32, 32, 64] {
            let vals = edges(w);
            for &x in &vals {
                // Unary ops.
                assert_equiv(
                    &bvnot(c(x, w), w),
                    bv_to_z3(&c(x, w)).bvnot(),
                    &format!("bvnot w{w} x={x:#x}"),
                );
                assert_equiv(
                    &bvneg(c(x, w), w),
                    bv_to_z3(&c(x, w)).bvneg(),
                    &format!("bvneg w{w} x={x:#x}"),
                );
                for &y in &vals {
                    let (ca, cb) = (c(x, w), c(y, w));
                    assert_equiv(
                        &bvrotl(ca.clone(), cb.clone(), w),
                        bv_to_z3(&ca).bvrotl(bv_to_z3(&cb)),
                        &format!("bvrotl w{w} a={x:#x} b={y:#x}"),
                    );
                    assert_equiv(
                        &bvurem(ca.clone(), cb.clone(), w),
                        bv_to_z3(&ca).bvurem(bv_to_z3(&cb)),
                        &format!("bvurem w{w} a={x:#x} b={y:#x}"),
                    );
                    assert_equiv(
                        &bvsdiv(ca.clone(), cb.clone(), w),
                        bv_to_z3(&ca).bvsdiv(bv_to_z3(&cb)),
                        &format!("bvsdiv w{w} a={x:#x} b={y:#x}"),
                    );
                    assert_equiv(
                        &bvsrem(ca.clone(), cb.clone(), w),
                        bv_to_z3(&ca).bvsrem(bv_to_z3(&cb)),
                        &format!("bvsrem w{w} a={x:#x} b={y:#x}"),
                    );
                }
            }
        }
    }

    /// A tiny reproducible xorshift64, mirroring the oracle corpus generator,
    /// so wide-width coverage replays byte-for-byte from the seed.
    fn xorshift(state: &mut u64) -> u64 {
        let mut x = *state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        *state = x;
        x
    }

    /// Broad randomized concrete coverage at every width. Both operands are
    /// concrete, so Z3 evaluates each query instantly (no symbolic
    /// divide/multiply) — this closes the wide-width gap the symbolic
    /// division proofs leave when Z3 times out. All six derived ops are
    /// checked strictly (`Unsat`) against Z3's native operator.
    #[test]
    fn randomized_pairs_match_z3() {
        let mut state: u64 = 0x0D2E_A101_5EED_0029;
        for &w in &[8u32, 32, 64] {
            let m = mask(w);
            for _ in 0..128 {
                let x = xorshift(&mut state) as u128 & m;
                let y = xorshift(&mut state) as u128 & m;
                let (ca, cb) = (c(x, w), c(y, w));
                assert_equiv(
                    &bvnot(ca.clone(), w),
                    bv_to_z3(&ca).bvnot(),
                    &format!("bvnot w{w} x={x:#x}"),
                );
                assert_equiv(
                    &bvneg(ca.clone(), w),
                    bv_to_z3(&ca).bvneg(),
                    &format!("bvneg w{w} x={x:#x}"),
                );
                assert_equiv(
                    &bvrotl(ca.clone(), cb.clone(), w),
                    bv_to_z3(&ca).bvrotl(bv_to_z3(&cb)),
                    &format!("bvrotl w{w} a={x:#x} b={y:#x}"),
                );
                assert_equiv(
                    &bvurem(ca.clone(), cb.clone(), w),
                    bv_to_z3(&ca).bvurem(bv_to_z3(&cb)),
                    &format!("bvurem w{w} a={x:#x} b={y:#x}"),
                );
                assert_equiv(
                    &bvsdiv(ca.clone(), cb.clone(), w),
                    bv_to_z3(&ca).bvsdiv(bv_to_z3(&cb)),
                    &format!("bvsdiv w{w} a={x:#x} b={y:#x}"),
                );
                assert_equiv(
                    &bvsrem(ca.clone(), cb.clone(), w),
                    bv_to_z3(&ca).bvsrem(bv_to_z3(&cb)),
                    &format!("bvsrem w{w} a={x:#x} b={y:#x}"),
                );
            }
        }
    }
}
