//! Derived-op lowering helpers (DES-018 / TR-015).
//!
//! synth-verify emits a handful of bitvector operations that the closed core
//! fragment ([`crate::term`], loom #246) deliberately omits: `bvnot`, `bvneg`,
//! `bvrotl`, `bvsdiv`, and `bvsrem`. Rather than widen the closed set (each new
//! [`BvTerm`] variant would need its own proven bit-blasting rule), this module
//! provides them as **derived-term constructors**: pure functions that build a
//! [`BvTerm`] out of the operations the core already decides.
//!
//! `bvurem` is the one exception: as of v0.10.0 it is a NATIVE op
//! ([`BvTerm::Urem`]) because the remainder falls straight out of the
//! restoring-division circuit, whereas the term-level `a - (a/b)*b` identity
//! cannot avoid a multiplier. Promoting that single op made the whole div/rem
//! family multiplier-free (`bvsrem` is now a sign correction over it), for +1
//! trusted op instead of +3. [`bvurem`] remains here as a thin constructor so
//! the SMT-LIB front-end and existing callers keep working.
//!
//! # Trust
//!
//! These are ordinary term builders — they are **not** new blast rules and add
//! nothing to the trusted base (the one native op, `bvurem`, carries its own
//! proven blast rule + Kani harness like every other fragment op). Every `Unsat`
//! a consumer derives from a lowered term is still gated by the verified LRAT
//! checker; the derived forms themselves remain untrusted.
//!
//! What makes them *blessed* is a mechanical oracle, not assertion:
//! `exhaustive_width8_div_rem_family_matches_smtlib_reference` checks `bvurem`,
//! `bvsdiv` and `bvsrem` against an independent SMT-LIB reference over **all
//! 65536 width-8 input pairs** — every sign combination, the `INT_MIN / -1`
//! overflow, and every divide-/remainder-by-zero case — with **no Z3 required**,
//! so it runs in the default build. `UV-017` additionally re-checks each against
//! Z3's native operator (widths 8/32/64) under the `oracle` feature. NOTE: the
//! `bvurem`/`bvsrem` forms CHANGED in v0.10.0 (see above), so the Z3-free
//! exhaustive test — not the older issue-#29 validation of the previous forms —
//! is what backs them now.
//!
//! # The chosen forms (all match SMT-LIB QF_BV / Z3 semantics)
//!
//! - `bvnot x   = x xor 1..1`
//! - `bvneg x   = 0 - x`
//! - `bvrotl a b = rotr(a, 0 - b)` — exact for power-of-two widths (see
//!   [`bvrotl`]), which covers the target widths 8/32/64.
//! - `bvurem a b` — the native [`BvTerm::Urem`] (multiplier-free; see above).
//! - `bvsdiv a b` — the SMT-LIB sign-mask construction over `bvudiv`.
//! - `bvsrem a b = (|a| urem |b| ^ sa) - sa` — the SMT-LIB sign-mask
//!   construction over the native `bvurem`, exact including `b = 0` and the
//!   `INT_MIN / -1` overflow edge, and multiplier-free.
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

/// Unsigned remainder (`bvurem`) — the native fragment op.
///
/// This was previously derived as `a - (a udiv b) * b`, which is exact but
/// costs a **multiplier**. `bvurem` is now native ([`BvTerm::Urem`]) because the
/// restoring-division circuit already produces the remainder, so blasting it
/// directly is multiplier-free. The SMT-LIB `b = 0` case (result `a`) is handled
/// by the blast rule and the evaluator.
///
/// Kept as a helper so the SMT-LIB front-end and existing callers keep working.
pub fn bvurem(a: BvTerm, b: BvTerm, width: u32) -> BvTerm {
    // `width` is unused: the op carries its operands' sort. Kept for signature
    // symmetry with the other binary helpers.
    let _ = width;
    BvTerm::Urem(Box::new(a), Box::new(b))
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

/// Signed remainder (`bvsrem`, sign follows the dividend) via the SMT-LIB
/// sign-mask construction over the native `bvurem`.
///
/// Previously derived as `a - bvsdiv(a,b)*b`, which costs a **multiplier**. Now
/// that [`BvTerm::Urem`] is native (and multiplier-free), the remainder of the
/// magnitudes can be taken directly and the dividend's sign re-applied — so this
/// derivation is multiplier-free too:
///
/// ```text
/// r = |a| urem |b|
/// bvsrem = (r ^ sa) - sa        // negate r iff a < 0
/// ```
///
/// This reproduces SMT-LIB `bvsrem` on every input, including:
/// - `b = 0`: `|a| urem 0` is `|a|`, and the sign fix maps it back to `a` —
///   matching SMT-LIB's `bvsrem` by zero.
/// - `INT_MIN % -1`: `|INT_MIN|` overflows back to `INT_MIN`, `|-1| = 1`, so
///   `r = 0` and the result is `0`, matching SMT-LIB.
pub fn bvsrem(a: BvTerm, b: BvTerm, width: u32) -> BvTerm {
    // MULTIPLICATIVE on purpose — reverted from the v0.10.0 urem-based form
    // (issue #97). Consumers' rem_s value models are multiplicative
    // (`a - (a sdiv b) * b`: synth's Sdiv+Mls, loom's WASM-spec form), and an
    // equivalence VC between THIS lowering and such a model must be
    // structurally similar to solve fast. The urem-based form routed through
    // the restoring divider's remainder, turning every such VC into a
    // divider-vs-multiplier cross-circuit proof: <1 s queries became >240 s
    // hangs in synth's CI (0.9.1 -> 0.12.0). The extra multiplier costs
    // gates; the cross-circuit equivalence costs consumers HOURS. Native
    // `BvTerm::Urem` remains for direct remainder queries.
    let q = bvsdiv(a.clone(), b.clone(), width);
    let prod = BvTerm::Mul(Box::new(q), Box::new(b));
    BvTerm::Sub(Box::new(a), Box::new(prod))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval::{Env, bv_sort, eval_bv};

    /// A Z3-free reference for the SMT-LIB div/rem family, computed directly on
    /// masked values via the spec's own sign-correction definitions. This is the
    /// oracle for the derived lowerings in the DEFAULT build — the `*_symbolic`
    /// tests below are Z3-based and only compile under the `oracle` feature.
    /// Returns `(bvurem, bvsdiv, bvsrem)`.
    fn smtlib_ref(x: u128, y: u128, w: u32) -> (u128, u128, u128) {
        let m = if w >= 128 {
            u128::MAX
        } else {
            (1u128 << w) - 1
        };
        let neg = |v: u128| v.wrapping_neg() & m;
        let msb = |v: u128| (v >> (w - 1)) & 1 == 1;
        let udiv = |p: u128, q: u128| p.checked_div(q).unwrap_or(m);
        let urem = |p: u128, q: u128| if q == 0 { p } else { p % q };
        let sdiv = match (msb(x), msb(y)) {
            (false, false) => udiv(x, y),
            (true, false) => neg(udiv(neg(x), y)),
            (false, true) => neg(udiv(x, neg(y))),
            (true, true) => udiv(neg(x), neg(y)),
        };
        let srem = match (msb(x), msb(y)) {
            (false, false) => urem(x, y),
            (true, false) => neg(urem(neg(x), y)),
            (false, true) => urem(x, neg(y)),
            (true, true) => neg(urem(neg(x), neg(y))),
        };
        (urem(x, y), sdiv, srem)
    }

    #[test]
    fn exhaustive_width8_div_rem_family_matches_smtlib_reference() {
        // Every one of the 65536 width-8 input pairs — so every sign
        // combination, the INT_MIN/-1 overflow, and every divide-/
        // remainder-by-zero case is covered. Guards the multiplier-free
        // derivations (bvurem is now the native op; bvsrem is a sign correction
        // over it) against the SMT-LIB definitions, with no Z3 needed.
        let w = 8u32;
        let env = Env::new();
        for x in 0..=0xFFu128 {
            for y in 0..=0xFFu128 {
                let (a, b) = (const_bv(x, w), const_bv(y, w));
                let (r_urem, r_sdiv, r_srem) = smtlib_ref(x, y, w);
                let got = |t: BvTerm| eval_bv(&t, &env).unwrap();
                assert_eq!(
                    got(bvurem(a.clone(), b.clone(), w)),
                    r_urem,
                    "bvurem {x} {y}"
                );
                assert_eq!(
                    got(bvsdiv(a.clone(), b.clone(), w)),
                    r_sdiv,
                    "bvsdiv {x} {y}"
                );
                assert_eq!(got(bvsrem(a, b, w)), r_srem, "bvsrem {x} {y}");
            }
        }
    }

    #[test]
    fn div_rem_derivation_shapes_are_deliberate() {
        // The shape of each derivation is a DESIGN DECISION, revised by #97:
        //   - bvurem / bvsdiv: multiplier-free (native Urem; sign-corrected
        //     Udiv) — the v0.10.0 gate-count win stands where it is free.
        //   - bvsrem: MULTIPLICATIVE on purpose (a - (a sdiv b) * b).
        //     Consumers' rem_s value models are multiplicative (synth's
        //     Sdiv+Mls, loom's WASM-spec form); the v0.10.0 urem-based form
        //     made every such equivalence VC a divider-vs-multiplier
        //     cross-circuit proof — <1 s queries became >240 s hangs (#97).
        //     This test pins the shape so a future "cleanup" cannot silently
        //     reintroduce the regression in either direction.
        let w = 32u32;
        let (a, b) = (var("a", w), var("b", w));
        let muls = |t: &BvTerm| format!("{t:?}").matches("Mul(").count();
        assert_eq!(
            muls(&bvurem(a.clone(), b.clone(), w)),
            0,
            "bvurem must stay multiplier-free (native Urem)"
        );
        assert_eq!(
            muls(&bvsdiv(a.clone(), b.clone(), w)),
            0,
            "bvsdiv must stay multiplier-free (sign-corrected Udiv)"
        );
        assert_eq!(
            muls(&bvsrem(a.clone(), b.clone(), w)),
            1,
            "bvsrem must stay MULTIPLICATIVE (one Mul) — see #97"
        );
    }

    /// #101 regression guard: the UNSIGNED twin of #97 — native `Urem`
    /// against the multiplicative model `a - (a udiv b) * b`, 32-bit
    /// symbolic. On the divider-remainder blast this exceeded 7 m 48 s
    /// (synth, killed); multiplicative it is ~5 ms. Same 10 s-deadline
    /// headroom logic as the #97 guard.
    #[test]
    fn urem_vc_against_multiplicative_model_decides_fast() {
        use crate::{BoolTerm, CheckResult, Solver};
        let (a, b) = (var("a", 32), var("b", 32));
        let ours = BvTerm::Urem(Box::new(a.clone()), Box::new(b.clone()));
        let q = BvTerm::Udiv(Box::new(a.clone()), Box::new(b.clone()));
        let theirs = BvTerm::Sub(Box::new(a), Box::new(BvTerm::Mul(Box::new(q), Box::new(b))));
        let mut s = Solver::new();
        s.assert(BoolTerm::Ne(Box::new(ours), Box::new(theirs)));
        match s.check_with_deadline(10_000) {
            CheckResult::Unsat(cert) => cert.recheck().expect("cert must re-check"),
            other => panic!(
                "urem VC must decide fast against the multiplicative model; got {other:?} — \
                 the #101 cross-circuit regression is back"
            ),
        }
    }

    /// #97 regression guard: the synth-shaped VC — this crate's srem value
    /// model vs a consumer's multiplicative model (Sdiv + Mls) — must decide
    /// fast at width 32. On the urem-based lowering it exceeded any sane
    /// deadline (>240 s reported, >15 s measured here); multiplicative, it is
    /// milliseconds. The 10 s deadline is three orders of magnitude of head-
    /// room, not a tight timing assertion.
    #[test]
    fn srem_vc_against_multiplicative_model_decides_fast() {
        use crate::{BoolTerm, CheckResult, Solver};
        let (a, b) = (var("a", 32), var("b", 32));
        let ours = bvsrem(a.clone(), b.clone(), 32);
        let q = bvsdiv(a.clone(), b.clone(), 32);
        let theirs = BvTerm::Sub(Box::new(a), Box::new(BvTerm::Mul(Box::new(q), Box::new(b))));
        let mut s = Solver::new();
        s.assert(BoolTerm::Ne(Box::new(ours), Box::new(theirs)));
        match s.check_with_deadline(10_000) {
            CheckResult::Unsat(cert) => cert.recheck().expect("cert must re-check"),
            other => panic!(
                "srem VC must decide (fast) against the multiplicative model; got {other:?} — \
                 the #97 cross-circuit regression is back"
            ),
        }
    }

    #[test]
    fn width16_div_rem_family_matches_smtlib_reference() {
        // Width 16 (relay CCSDS/CRC-16, kiln extend16) across signed
        // boundaries + a sampled sweep.
        let w = 16u32;
        let env = Env::new();
        let mut vals: Vec<u128> = vec![0, 1, 2, 0x7FFF, 0x8000, 0x8001, 0xFFFE, 0xFFFF];
        let mut s: u128 = 0x1234;
        for _ in 0..40 {
            s = (s
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407))
                & 0xFFFF;
            vals.push(s);
        }
        for &x in &vals {
            for &y in &vals {
                let (a, b) = (const_bv(x, w), const_bv(y, w));
                let (r_urem, r_sdiv, r_srem) = smtlib_ref(x, y, w);
                let got = |t: BvTerm| eval_bv(&t, &env).unwrap();
                assert_eq!(
                    got(bvurem(a.clone(), b.clone(), w)),
                    r_urem,
                    "bvurem w16 {x} {y}"
                );
                assert_eq!(
                    got(bvsdiv(a.clone(), b.clone(), w)),
                    r_sdiv,
                    "bvsdiv w16 {x} {y}"
                );
                assert_eq!(got(bvsrem(a, b, w)), r_srem, "bvsrem w16 {x} {y}");
            }
        }
    }

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
