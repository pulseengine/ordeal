//! The formerly derived ops: constructors and the core-fragment REWRITE
//! (DES-018 / TR-015; proven DAG constructs since #192 phase 5, TR-064).
//!
//! synth-verify emits a handful of bitvector operations the closed core
//! fragment ([`crate::term`], loom #246) did not have as constructs of their
//! own until v0.28.0: `bvnot`, `bvneg`, `bvrotl`, `bvsdiv` and `bvsrem`.
//! Until then this module rewrote them into the core (`bvneg x = 0 - x`,
//! the SMT-LIB sign-mask construction for `bvsdiv`, …) *before* the term DAG
//! was built, so a certificate carried the rewrite and the rewrite itself
//! was trusted. Since phase 5 each is a [`BvTerm`] variant ([`BvTerm::Not`],
//! [`BvTerm::Neg`], [`BvTerm::Rotl`], [`BvTerm::Sdiv`], [`BvTerm::Srem`]) with
//! a proven bit-blasting rule (`blast_kernel::blast_bvnot` … `blast_srem`,
//! `lean/BlasterDerived.lean`: `blast_bvnot_bitvec`, `blast_neg_bitvec`,
//! `blast_rotl_bitvec`, `blast_sdiv_bitvec`, `blast_srem_bitvec` — each
//! against the Lean `BitVec` operation SMT-LIB names), and the constructors
//! below ([`bvnot`], [`bvneg`], [`bvrotl`], [`bvsdiv`], [`bvsrem`]) simply
//! build those variants. Callers that used the constructors keep working.
//!
//! The rewrite is kept, as [`expand_bv`] / [`expand_bool`], for one caller:
//! the default path of `Solver::check` / `check_with_witness` (and so
//! `ordeal check` without `--with-query`), which rewrites the derived ops
//! into the core before canonicalization exactly as v0.27.0 did, so that the
//! certificates it emits are byte-identical. `Solver::check_with_query` (and
//! `ordeal check --with-query`) does NOT rewrite: the derived ops reach the
//! DAG as their own nodes, the proven composite rules encode them, and the
//! `ordeal-cert/v2` query block carries the operation. The composite rules
//! are the rewrite spelled gate for gate (the rewrite's term shape over the
//! proven rules, in the rewrite's operand order — `bvnot` compacts to the
//! same literals as its XOR with all-ones), so the two paths produce the
//! same CNF except where canonicalization reorders commutative operands
//! *inside* the rewritten tree (`bvsdiv` / `bvsrem` operands whose `Debug`
//! order differs from the rule's): `docs/design/query-cnf-gap.md`, phase 5,
//! records the exact cases and the digests. Switching the default path to
//! the nodes is the maintainer's call, one line in `Solver::lower`.
//!
//! `bvurem` is a NATIVE op since v0.10.0 ([`BvTerm::Urem`]) because the
//! remainder falls straight out of the restoring-division circuit; [`bvurem`]
//! remains a thin constructor.
//!
//! # Trust
//!
//! The rewrite is on the UNTRUSTED side: every `Unsat` a consumer derives
//! from a rewritten term is still gated by the verified LRAT checker. What
//! backs it: `exhaustive_width8_div_rem_family_matches_smtlib_reference`
//! checks the rewrite AND the evaluator's own definitions of `bvsdiv` /
//! `bvsrem` against an independent SMT-LIB reference over **all 65536
//! width-8 input pairs** — every sign combination, `INT_MIN / -1`, and every
//! divide-/remainder-by-zero case — with no Z3 required; `UV-017` re-checks
//! the rewrite against Z3's native operators (widths 8/32/64) under the
//! `oracle` feature; and, since phase 5, the proven rules:
//! `rewrite_equals_the_proven_rule_with_a_trusted_recheck` asks
//! `check_with_query` to refute `op(a, b) ≠ rewrite(op(a, b))` for every
//! derived op, so the trusted crate re-encodes the DAG that holds BOTH and
//! certifies the refutation.
//!
//! # The rewrite's forms (all match SMT-LIB QF_BV / Z3 semantics)
//!
//! - `bvnot x   = x xor 1..1`
//! - `bvneg x   = 0 - x`
//! - `bvrotl a b = rotr(a, 0 - b)` at a power-of-two width, else
//!   `rotr(a, (w - b mod w) mod w)` — exact at every width (see [`rewrite_rotl`]).
//! - `bvurem a b` — the native [`BvTerm::Urem`] (multiplier-free; see above).
//! - `bvsdiv a b` — the SMT-LIB sign-mask construction over `bvudiv`.
//! - `bvsrem a b = a - (a sdiv b) * b` — MULTIPLICATIVE on purpose (#97).
//!
//! Widths are accepted in `1..=128`; the operands of each binary helper must
//! already share the given width (this module does not sort-check — build
//! well-sorted terms and validate with [`crate::eval::bv_sort`]).

use crate::eval::{self, EvalError};
use crate::term::{BoolTerm, BvTerm, Sort};

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

fn bx(t: BvTerm) -> Box<BvTerm> {
    Box::new(t)
}

// ─── The constructors: the variants of the closed fragment ───────────────────

/// Bitwise NOT (`bvnot`): the [`BvTerm::Not`] node (proven rule
/// `blast_bvnot`). `width` is unused — the node carries its operand's sort —
/// and kept for signature compatibility with v0.27.0.
pub fn bvnot(x: BvTerm, width: u32) -> BvTerm {
    let _ = width;
    BvTerm::Not(bx(x))
}

/// Two's-complement negation (`bvneg`): the [`BvTerm::Neg`] node (proven
/// rule `blast_neg`). `width` as in [`bvnot`].
pub fn bvneg(x: BvTerm, width: u32) -> BvTerm {
    let _ = width;
    BvTerm::Neg(bx(x))
}

/// Rotate-left (`bvrotl`) by a term amount, mod the width, exact at every
/// width: the [`BvTerm::Rotl`] node (proven rule `blast_rotl`). `width` as
/// in [`bvnot`].
pub fn bvrotl(a: BvTerm, b: BvTerm, width: u32) -> BvTerm {
    let _ = width;
    BvTerm::Rotl(bx(a), bx(b))
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
    BvTerm::Urem(bx(a), bx(b))
}

/// Signed division (`bvsdiv`), SMT-LIB semantics: the [`BvTerm::Sdiv`] node
/// (proven rule `blast_sdiv`). `width` as in [`bvnot`].
pub fn bvsdiv(a: BvTerm, b: BvTerm, width: u32) -> BvTerm {
    let _ = width;
    BvTerm::Sdiv(bx(a), bx(b))
}

/// Signed remainder (`bvsrem`, sign of the dividend), SMT-LIB semantics: the
/// [`BvTerm::Srem`] node (proven rule `blast_srem`). `width` as in [`bvnot`].
pub fn bvsrem(a: BvTerm, b: BvTerm, width: u32) -> BvTerm {
    let _ = width;
    BvTerm::Srem(bx(a), bx(b))
}

// ─── The rewrite into the core (the v0.27.0 lowering) ────────────────────────

/// The arithmetic sign mask of `x`: all-ones when `x` is negative (as a
/// two's-complement `width`-bit value), all-zeros otherwise.
///
/// Built as `ashr(x, width - 1)`, which broadcasts the sign bit across the
/// whole word. Used by the signed-division rewrite.
fn sign_mask(x: BvTerm, width: u32) -> BvTerm {
    BvTerm::Ashr(bx(x), bx(const_bv((width - 1) as u128, width)))
}

/// Two's-complement absolute value of `x` at `width` bits: `(x ^ s) - s`,
/// where `s = sign_mask(x)`.
///
/// When `x >= 0` the mask is zero and this is `x`; when `x < 0` it is
/// `~x - (-1) = ~x + 1 = -x`. Note `abs(INT_MIN)` overflows back to `INT_MIN`,
/// exactly as SMT-LIB's `bvsdiv` construction requires.
fn abs_bv(x: BvTerm, width: u32) -> BvTerm {
    let s = sign_mask(x.clone(), width);
    BvTerm::Sub(bx(BvTerm::Xor(bx(x), bx(s.clone()))), bx(s))
}

/// The rewrite of `bvnot`: `x xor 1..1`.
///
/// XOR with the all-ones constant flips every bit — the standard derivation of
/// one's complement from XOR.
pub fn rewrite_not(x: BvTerm, width: u32) -> BvTerm {
    BvTerm::Xor(bx(x), bx(const_bv(mask(width), width)))
}

/// The rewrite of `bvneg`: `0 - x`.
pub fn rewrite_neg(x: BvTerm, width: u32) -> BvTerm {
    BvTerm::Sub(bx(const_bv(0, width)), bx(x))
}

/// The rewrite of `bvrotl` by a variable amount, exact at every width.
///
/// For a power-of-two `width`, rotating left by `b` equals rotating right by
/// `0 - b`: the core [`BvTerm::Rotr`] reduces its amount mod `width`, and
/// `2^width ≡ 0 (mod width)`, so `(0 - b) mod width = (width - b mod width)
/// mod width`. That identity FAILS for any other width (fixed 0.22.1: the
/// SMT-LIB front end applied it at every width), so there the amount is
/// computed explicitly as `(width - b mod width) mod width` — both operands
/// of the subtraction are `<= width`, so it never wraps.
pub fn rewrite_rotl(a: BvTerm, b: BvTerm, width: u32) -> BvTerm {
    let amount = if width.is_power_of_two() {
        BvTerm::Sub(bx(const_bv(0, width)), bx(b))
    } else {
        let w = || bx(const_bv(width as u128, width));
        let b_mod_w = BvTerm::Urem(bx(b), w());
        BvTerm::Urem(bx(BvTerm::Sub(w(), bx(b_mod_w))), w())
    };
    BvTerm::Rotr(bx(a), bx(amount))
}

/// The rewrite of `bvsdiv`: the SMT-LIB sign-mask construction over
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
pub fn rewrite_sdiv(a: BvTerm, b: BvTerm, width: u32) -> BvTerm {
    let sa = sign_mask(a.clone(), width);
    let sb = sign_mask(b.clone(), width);
    let result_sign = BvTerm::Xor(bx(sa), bx(sb));
    let q = BvTerm::Udiv(bx(abs_bv(a, width)), bx(abs_bv(b, width)));
    // (q ^ result_sign) - result_sign  — negate the quotient iff signs differ.
    BvTerm::Sub(
        bx(BvTerm::Xor(bx(q), bx(result_sign.clone()))),
        bx(result_sign),
    )
}

/// The rewrite of `bvsrem` (sign follows the dividend): `a - (a sdiv b) * b`.
///
/// MULTIPLICATIVE on purpose — reverted from the v0.10.0 urem-based form
/// (issue #97). Consumers' rem_s value models are multiplicative
/// (`a - (a sdiv b) * b`: synth's Sdiv+Mls, loom's WASM-spec form), and an
/// equivalence VC between THIS form and such a model must be structurally
/// similar to solve fast. The urem-based form routed through the restoring
/// divider's remainder, turning every such VC into a divider-vs-multiplier
/// cross-circuit proof: <1 s queries became >240 s hangs in synth's CI
/// (0.9.1 -> 0.12.0). The extra multiplier costs gates; the cross-circuit
/// equivalence costs consumers HOURS. Native `BvTerm::Urem` remains for
/// direct remainder queries. Exact including `b = 0` (`(a sdiv 0) * 0 = 0`)
/// and `INT_MIN % -1` (`INT_MIN * -1 = INT_MIN`, so the result is `0`).
pub fn rewrite_srem(a: BvTerm, b: BvTerm, width: u32) -> BvTerm {
    let q = rewrite_sdiv(a.clone(), b.clone(), width);
    let prod = BvTerm::Mul(bx(q), bx(b));
    BvTerm::Sub(bx(a), bx(prod))
}

/// Rewrite every derived op under `t` into the closed core, bottom-up —
/// the v0.27.0 lowering as one pass over the term. `Solver::check`'s
/// default path applies it before canonicalization (see the module docs);
/// `check_with_query` does not. Fails only on an ill-sorted term (the width
/// of a derived op is its operand's width, which [`eval::bv_sort`] supplies).
pub fn expand_bv(t: &BvTerm) -> Result<BvTerm, EvalError> {
    use BvTerm::*;
    let width = |x: &BvTerm| eval::bv_sort(x).map(|s| s.width);
    Ok(match t {
        Const { .. } | Var { .. } => t.clone(),
        Add(a, b) => Add(bx(expand_bv(a)?), bx(expand_bv(b)?)),
        Sub(a, b) => Sub(bx(expand_bv(a)?), bx(expand_bv(b)?)),
        Mul(a, b) => Mul(bx(expand_bv(a)?), bx(expand_bv(b)?)),
        Udiv(a, b) => Udiv(bx(expand_bv(a)?), bx(expand_bv(b)?)),
        Urem(a, b) => Urem(bx(expand_bv(a)?), bx(expand_bv(b)?)),
        And(a, b) => And(bx(expand_bv(a)?), bx(expand_bv(b)?)),
        Or(a, b) => Or(bx(expand_bv(a)?), bx(expand_bv(b)?)),
        Xor(a, b) => Xor(bx(expand_bv(a)?), bx(expand_bv(b)?)),
        Shl(a, b) => Shl(bx(expand_bv(a)?), bx(expand_bv(b)?)),
        Lshr(a, b) => Lshr(bx(expand_bv(a)?), bx(expand_bv(b)?)),
        Ashr(a, b) => Ashr(bx(expand_bv(a)?), bx(expand_bv(b)?)),
        Rotr(a, b) => Rotr(bx(expand_bv(a)?), bx(expand_bv(b)?)),
        Extract { hi, lo, arg } => Extract {
            hi: *hi,
            lo: *lo,
            arg: bx(expand_bv(arg)?),
        },
        Concat(a, b) => Concat(bx(expand_bv(a)?), bx(expand_bv(b)?)),
        ZeroExt { by, arg } => ZeroExt {
            by: *by,
            arg: bx(expand_bv(arg)?),
        },
        SignExt { by, arg } => SignExt {
            by: *by,
            arg: bx(expand_bv(arg)?),
        },
        Ite { cond, then_, else_ } => Ite {
            cond: Box::new(expand_bool(cond)?),
            then_: bx(expand_bv(then_)?),
            else_: bx(expand_bv(else_)?),
        },
        Not(a) => {
            let a = expand_bv(a)?;
            let w = width(&a)?;
            rewrite_not(a, w)
        }
        Neg(a) => {
            let a = expand_bv(a)?;
            let w = width(&a)?;
            rewrite_neg(a, w)
        }
        Rotl(a, b) => {
            let (a, b) = (expand_bv(a)?, expand_bv(b)?);
            let w = width(&a)?;
            rewrite_rotl(a, b, w)
        }
        Sdiv(a, b) => {
            let (a, b) = (expand_bv(a)?, expand_bv(b)?);
            let w = width(&a)?;
            rewrite_sdiv(a, b, w)
        }
        Srem(a, b) => {
            let (a, b) = (expand_bv(a)?, expand_bv(b)?);
            let w = width(&a)?;
            rewrite_srem(a, b, w)
        }
    })
}

/// [`expand_bv`] under a boolean term.
pub fn expand_bool(t: &BoolTerm) -> Result<BoolTerm, EvalError> {
    use BoolTerm::*;
    let eb = |a: &BvTerm, b: &BvTerm| -> Result<(Box<BvTerm>, Box<BvTerm>), EvalError> {
        Ok((bx(expand_bv(a)?), bx(expand_bv(b)?)))
    };
    Ok(match t {
        Eq(a, b) => {
            let (a, b) = eb(a, b)?;
            Eq(a, b)
        }
        Ne(a, b) => {
            let (a, b) = eb(a, b)?;
            Ne(a, b)
        }
        Ult(a, b) => {
            let (a, b) = eb(a, b)?;
            Ult(a, b)
        }
        Ule(a, b) => {
            let (a, b) = eb(a, b)?;
            Ule(a, b)
        }
        Ugt(a, b) => {
            let (a, b) = eb(a, b)?;
            Ugt(a, b)
        }
        Uge(a, b) => {
            let (a, b) = eb(a, b)?;
            Uge(a, b)
        }
        Slt(a, b) => {
            let (a, b) = eb(a, b)?;
            Slt(a, b)
        }
        Sle(a, b) => {
            let (a, b) = eb(a, b)?;
            Sle(a, b)
        }
        Sgt(a, b) => {
            let (a, b) = eb(a, b)?;
            Sgt(a, b)
        }
        Sge(a, b) => {
            let (a, b) = eb(a, b)?;
            Sge(a, b)
        }
        Not(x) => Not(Box::new(expand_bool(x)?)),
        And(a, b) => And(Box::new(expand_bool(a)?), Box::new(expand_bool(b)?)),
        Or(a, b) => Or(Box::new(expand_bool(a)?), Box::new(expand_bool(b)?)),
    })
}

// rivet: verifies VER-045
#[cfg(test)]
mod tests {
    use super::*;

    /// Soundness regression (0.22.1): `bvrotl` equals the SMT-LIB
    /// rotate-left (evaluated directly as a left rotation by `b mod w`) at
    /// EVERY width 1..=10, exhaustively — the evaluator's own `Rotl` AND the
    /// core rewrite `expand_bv` applies on the default path; before the fix
    /// the `rotr(a, 0 - b)` identity was applied at non-power-of-two widths
    /// where it is false.
    #[test]
    fn bvrotl_exact_at_every_width() {
        use crate::eval::{Env, eval_bv};
        for w in 1u32..=10 {
            let m = (1u128 << w) - 1;
            for a in 0u128..(1 << w) {
                for b in 0u128..(1 << w) {
                    let t = bvrotl(const_bv(a, w), const_bv(b, w), w);
                    let got = eval_bv(&t, &Env::new()).expect("eval");
                    let got_rewrite =
                        eval_bv(&expand_bv(&t).expect("sorted"), &Env::new()).expect("eval");
                    let r = (b % w as u128) as u32;
                    let want = if r == 0 {
                        a
                    } else {
                        ((a << r) | (a >> (w - r))) & m
                    };
                    assert_eq!(got, want, "rotl w={w} a={a:#x} b={b:#x}");
                    assert_eq!(got_rewrite, want, "rewritten rotl w={w} a={a:#x} b={b:#x}");
                }
            }
        }
    }
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
        // remainder-by-zero case is covered — through BOTH the evaluator's
        // own `Sdiv` / `Srem` definitions (the SAT model self-check and
        // canon's constant folding) and the core rewrite `expand_bv` (the
        // default path), against an independent SMT-LIB reference, with no
        // Z3 needed.
        let w = 8u32;
        let env = Env::new();
        for x in 0..=0xFFu128 {
            for y in 0..=0xFFu128 {
                let (a, b) = (const_bv(x, w), const_bv(y, w));
                let (r_urem, r_sdiv, r_srem) = smtlib_ref(x, y, w);
                let got = |t: BvTerm| eval_bv(&t, &env).unwrap();
                let got_rw = |t: BvTerm| eval_bv(&expand_bv(&t).unwrap(), &env).unwrap();
                let urem = bvurem(a.clone(), b.clone(), w);
                let sdiv = bvsdiv(a.clone(), b.clone(), w);
                let srem = bvsrem(a, b, w);
                assert_eq!(got(urem.clone()), r_urem, "bvurem {x} {y}");
                assert_eq!(got(sdiv.clone()), r_sdiv, "bvsdiv {x} {y}");
                assert_eq!(got(srem.clone()), r_srem, "bvsrem {x} {y}");
                assert_eq!(got_rw(urem), r_urem, "rewritten bvurem {x} {y}");
                assert_eq!(got_rw(sdiv), r_sdiv, "rewritten bvsdiv {x} {y}");
                assert_eq!(got_rw(srem), r_srem, "rewritten bvsrem {x} {y}");
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
        // Since #192 phase 5 the shape lives in the REWRITE (`expand_bv`,
        // the default path) and, gate for gate, in the proven composite
        // rules `blast_sdiv` / `blast_srem` (`derived_rules_are_the_rewrite`
        // in blast_kernel's tests pins the latter).
        let w = 32u32;
        let (a, b) = (var("a", w), var("b", w));
        let muls = |t: &BvTerm| {
            format!("{:?}", expand_bv(t).unwrap())
                .matches("Mul(")
                .count()
        };
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

    /// #192 phase 5: every derived op's proven rule agrees with the core
    /// rewrite — `op(a, b) ≠ rewrite(op(a, b))` is refuted through
    /// `check_with_query`, i.e. the DAG holding both the node and its
    /// rewritten twin is re-encoded by the trusted crate and the refutation
    /// re-checked before `Unsat` is returned. At widths 8 and 32 (and 64 for
    /// the rules without a divider).
    #[test]
    fn rewrite_equals_the_proven_rule_with_a_trusted_recheck() {
        use crate::{BoolTerm, QueryCheckResult, Solver};
        for &w in &[8u32, 32, 64] {
            let (a, b) = (var("a", w), var("b", w));
            let mut ops: Vec<(&str, BvTerm)> = vec![
                ("bvnot", bvnot(a.clone(), w)),
                ("bvneg", bvneg(a.clone(), w)),
                ("bvrotl", bvrotl(a.clone(), b.clone(), w)),
            ];
            if w <= 32 {
                ops.push(("bvsdiv", bvsdiv(a.clone(), b.clone(), w)));
                ops.push(("bvsrem", bvsrem(a.clone(), b.clone(), w)));
            }
            for (name, t) in ops {
                let twin = expand_bv(&t).expect("sorted");
                let mut s = Solver::new();
                s.assert(BoolTerm::Ne(Box::new(t), Box::new(twin)));
                match s.check_with_query() {
                    QueryCheckResult::Unsat(cert) => {
                        cert.recheck().expect("trusted query recheck");
                        assert!(
                            cert.query.has_derived(),
                            "{name} w{w}: the query block must carry the derived node"
                        );
                    }
                    other => panic!("{name} w{w}: rule ≠ rewrite must be Unsat, got {other:?}"),
                }
            }
        }
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

    /// Z3's verdict on the disequality `rewrite(derived) != native`:
    /// `Unsat` means the core REWRITE of the derived form is provably equal
    /// to Z3's native operator, `Sat` is a real disagreement (a
    /// counterexample exists), and `Unknown` means Z3 gave up (the symbolic
    /// multiply/divide circuits at wide widths are hard for bit-blasting —
    /// this never counts as a disagreement). The variant itself translates
    /// to Z3's native operator (`bv_to_z3`), so it is the rewrite — the
    /// default path's lowering — that this compares; the proven rules are
    /// compared with the rewrite by `rewrite_equals_the_proven_rule_*` and
    /// with Z3 by `oracle::derived_ops_differential_through_check_with_query`.
    fn equiv_verdict(derived: &BvTerm, native: BV) -> SatResult {
        let solver = Solver::new();
        let mut params = Params::new();
        params.set_u32("timeout", 20_000);
        solver.set_params(&params);
        let rewritten = expand_bv(derived).expect("sorted");
        solver.assert(bv_to_z3(&rewritten).eq(native).not());
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
