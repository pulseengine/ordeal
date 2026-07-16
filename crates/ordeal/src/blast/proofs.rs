//! Kani proofs of bit-blaster correctness (FEAT-004 / P4).
//!
//! Each rule is proved equivalent to a concrete reference for ALL inputs at
//! widths 8/32/64 — a machine-checked proof, not a randomized/differential
//! sample. This lets soundness drop the Z3 differential oracle: the blaster is
//! proved correct against a small, auditable `u128` reference.
//!
//! The `r_*` reference functions are the *exact* expressions `eval::eval_bv` /
//! `eval::eval_bool` compute each op with (SMT-LIB QF_BV semantics). They are
//! pure `u128` arithmetic — no `HashMap`/`Env` — so Kani can model them, and the
//! AIG's structural-hash cache is a no-op under `cfg(kani)` (see `crate::aig`).
//!
//! Pattern: build the AIG for `op(a, b)`, make the input bits symbolic, and
//! assert `word_value(blast) == r_op(a, b)` for every assignment.

use crate::aig::{Aig, word_input, word_value};

/// Low `w` bits set (`w ≤ 128`).
fn mask(w: u32) -> u128 {
    if w >= 128 {
        u128::MAX
    } else {
        (1u128 << w) - 1
    }
}

/// `n` fully-symbolic input bits.
fn any_bits(n: usize) -> Vec<bool> {
    (0..n).map(|_| kani::any()).collect()
}

/// Interpret a width-`w` value as a signed two's-complement `i128`.
fn to_signed(x: u128, w: u32) -> i128 {
    if (x >> (w - 1)) & 1 == 1 {
        (x as i128) - (1i128 << w)
    } else {
        x as i128
    }
}

// ── Reference semantics (mirror eval::eval_bv / eval_bool exactly) ─────────
fn r_add(x: u128, y: u128, w: u32) -> u128 {
    x.wrapping_add(y) & mask(w)
}
fn r_sub(x: u128, y: u128, w: u32) -> u128 {
    x.wrapping_sub(y) & mask(w)
}
fn r_mul(x: u128, y: u128, w: u32) -> u128 {
    x.wrapping_mul(y) & mask(w)
}
fn r_udiv(x: u128, y: u128, w: u32) -> u128 {
    // SMT-LIB: bvudiv by zero = all-ones.
    x.checked_div(y).unwrap_or(mask(w))
}
fn r_urem(x: u128, y: u128, _w: u32) -> u128 {
    // SMT-LIB: bvurem by zero = the dividend.
    if y == 0 { x } else { x % y }
}
fn r_and(x: u128, y: u128, w: u32) -> u128 {
    (x & y) & mask(w)
}
fn r_or(x: u128, y: u128, w: u32) -> u128 {
    (x | y) & mask(w)
}
fn r_xor(x: u128, y: u128, w: u32) -> u128 {
    (x ^ y) & mask(w)
}
fn r_shl(x: u128, sh: u128, w: u32) -> u128 {
    if sh >= w as u128 {
        0
    } else {
        (x << sh) & mask(w)
    }
}
fn r_lshr(x: u128, sh: u128, w: u32) -> u128 {
    if sh >= w as u128 { 0 } else { x >> sh }
}
fn r_ashr(x: u128, sh: u128, w: u32) -> u128 {
    let m = mask(w);
    let sign = (x >> (w - 1)) & 1 == 1;
    if sh >= w as u128 {
        if sign { m } else { 0 }
    } else if sign {
        ((x >> sh) | (m & !(m >> sh))) & m
    } else {
        x >> sh
    }
}
fn r_rotr(x: u128, sh: u128, w: u32) -> u128 {
    let r = (sh % w as u128) as u32;
    if r == 0 {
        x & mask(w)
    } else {
        ((x >> r) | (x << (w - r))) & mask(w)
    }
}

/// Prove a binary `Word -> Word -> Word` blaster equal to its `u128` reference
/// for every symbolic input, at width `$w`.
macro_rules! bv_bin_proof {
    ($name:ident, $blast:path, $ref:ident, $w:expr) => {
        #[kani::proof]
        fn $name() {
            let w: u32 = $w;
            let mut aig = Aig::new();
            let a = word_input(&mut aig, w);
            let b = word_input(&mut aig, w);
            let out = $blast(&mut aig, &a, &b);
            let inputs = any_bits((2 * w) as usize);
            let vals = aig.simulate(&inputs);
            let av = word_value(&aig, &vals, &a);
            let bv = word_value(&aig, &vals, &b);
            let got = word_value(&aig, &vals, &out);
            assert_eq!(got, $ref(av, bv, w));
        }
    };
}

use crate::blast::arith::{blast_add, blast_sub};
use crate::blast::bitwise::{blast_and, blast_or, blast_xor};
use crate::blast::muldiv::{blast_mul, blast_udiv, blast_urem};
use crate::blast::shift::{blast_ashr, blast_lshr, blast_rotr, blast_shl};

// ── Arithmetic ────────────────────────────────────────────────────────────
bv_bin_proof!(add_8, blast_add, r_add, 8);
bv_bin_proof!(add_32, blast_add, r_add, 32);
bv_bin_proof!(add_64, blast_add, r_add, 64);
bv_bin_proof!(sub_8, blast_sub, r_sub, 8);
bv_bin_proof!(sub_32, blast_sub, r_sub, 32);
bv_bin_proof!(sub_64, blast_sub, r_sub, 64);

// ── Bitwise ───────────────────────────────────────────────────────────────
bv_bin_proof!(and_8, blast_and, r_and, 8);
bv_bin_proof!(and_32, blast_and, r_and, 32);
bv_bin_proof!(and_64, blast_and, r_and, 64);
bv_bin_proof!(or_8, blast_or, r_or, 8);
bv_bin_proof!(or_32, blast_or, r_or, 32);
bv_bin_proof!(or_64, blast_or, r_or, 64);
bv_bin_proof!(xor_8, blast_xor, r_xor, 8);
bv_bin_proof!(xor_32, blast_xor, r_xor, 32);
bv_bin_proof!(xor_64, blast_xor, r_xor, 64);

// ── Shifts ────────────────────────────────────────────────────────────────
bv_bin_proof!(shl_8, blast_shl, r_shl, 8);
bv_bin_proof!(shl_32, blast_shl, r_shl, 32);
bv_bin_proof!(shl_64, blast_shl, r_shl, 64);
bv_bin_proof!(lshr_8, blast_lshr, r_lshr, 8);
bv_bin_proof!(lshr_32, blast_lshr, r_lshr, 32);
bv_bin_proof!(lshr_64, blast_lshr, r_lshr, 64);
bv_bin_proof!(ashr_8, blast_ashr, r_ashr, 8);
bv_bin_proof!(ashr_32, blast_ashr, r_ashr, 32);
bv_bin_proof!(ashr_64, blast_ashr, r_ashr, 64);
bv_bin_proof!(rotr_8, blast_rotr, r_rotr, 8);
bv_bin_proof!(rotr_32, blast_rotr, r_rotr, 32);
bv_bin_proof!(rotr_64, blast_rotr, r_rotr, 64);

// ── Multiply / divide (heavy — 32/64 may be compute-bound) ────────────────
bv_bin_proof!(mul_8, blast_mul, r_mul, 8);
bv_bin_proof!(mul_32, blast_mul, r_mul, 32);
bv_bin_proof!(mul_64, blast_mul, r_mul, 64);
bv_bin_proof!(udiv_8, blast_udiv, r_udiv, 8);
bv_bin_proof!(udiv_32, blast_udiv, r_udiv, 32);
bv_bin_proof!(udiv_64, blast_udiv, r_udiv, 64);
bv_bin_proof!(urem_8, blast_urem, r_urem, 8);
bv_bin_proof!(urem_32, blast_urem, r_urem, 32);
bv_bin_proof!(urem_64, blast_urem, r_urem, 64);

// ── Comparisons (Word × Word → 1 bit) ──────────────────────────────────────
fn r_eq(x: u128, y: u128, _w: u32) -> bool {
    x == y
}
fn r_ne(x: u128, y: u128, _w: u32) -> bool {
    x != y
}
fn r_ult(x: u128, y: u128, _w: u32) -> bool {
    x < y
}
fn r_ule(x: u128, y: u128, _w: u32) -> bool {
    x <= y
}
fn r_ugt(x: u128, y: u128, _w: u32) -> bool {
    x > y
}
fn r_uge(x: u128, y: u128, _w: u32) -> bool {
    x >= y
}
fn r_slt(x: u128, y: u128, w: u32) -> bool {
    to_signed(x, w) < to_signed(y, w)
}
fn r_sle(x: u128, y: u128, w: u32) -> bool {
    to_signed(x, w) <= to_signed(y, w)
}
fn r_sgt(x: u128, y: u128, w: u32) -> bool {
    to_signed(x, w) > to_signed(y, w)
}
fn r_sge(x: u128, y: u128, w: u32) -> bool {
    to_signed(x, w) >= to_signed(y, w)
}

/// Prove a `Word × Word → Lit` comparison equal to its bool reference.
macro_rules! bv_cmp_proof {
    ($name:ident, $blast:path, $ref:ident, $w:expr) => {
        #[kani::proof]
        fn $name() {
            let w: u32 = $w;
            let mut aig = Aig::new();
            let a = word_input(&mut aig, w);
            let b = word_input(&mut aig, w);
            let out = $blast(&mut aig, &a, &b);
            let inputs = any_bits((2 * w) as usize);
            let vals = aig.simulate(&inputs);
            let av = word_value(&aig, &vals, &a);
            let bv = word_value(&aig, &vals, &b);
            let got = aig.lit_value(&vals, out);
            assert_eq!(got, $ref(av, bv, w));
        }
    };
}

use crate::blast::arith::{
    blast_sge, blast_sgt, blast_sle, blast_slt, blast_uge, blast_ugt, blast_ule, blast_ult,
};
use crate::blast::bitwise::{blast_eq, blast_ne};

bv_cmp_proof!(eq_8, blast_eq, r_eq, 8);
bv_cmp_proof!(eq_32, blast_eq, r_eq, 32);
bv_cmp_proof!(eq_64, blast_eq, r_eq, 64);
bv_cmp_proof!(ne_8, blast_ne, r_ne, 8);
bv_cmp_proof!(ne_32, blast_ne, r_ne, 32);
bv_cmp_proof!(ne_64, blast_ne, r_ne, 64);
bv_cmp_proof!(ult_8, blast_ult, r_ult, 8);
bv_cmp_proof!(ult_32, blast_ult, r_ult, 32);
bv_cmp_proof!(ult_64, blast_ult, r_ult, 64);
bv_cmp_proof!(ule_8, blast_ule, r_ule, 8);
bv_cmp_proof!(ule_32, blast_ule, r_ule, 32);
bv_cmp_proof!(ule_64, blast_ule, r_ule, 64);
bv_cmp_proof!(ugt_8, blast_ugt, r_ugt, 8);
bv_cmp_proof!(ugt_32, blast_ugt, r_ugt, 32);
bv_cmp_proof!(ugt_64, blast_ugt, r_ugt, 64);
bv_cmp_proof!(uge_8, blast_uge, r_uge, 8);
bv_cmp_proof!(uge_32, blast_uge, r_uge, 32);
bv_cmp_proof!(uge_64, blast_uge, r_uge, 64);
bv_cmp_proof!(slt_8, blast_slt, r_slt, 8);
bv_cmp_proof!(slt_32, blast_slt, r_slt, 32);
bv_cmp_proof!(slt_64, blast_slt, r_slt, 64);
bv_cmp_proof!(sle_8, blast_sle, r_sle, 8);
bv_cmp_proof!(sle_32, blast_sle, r_sle, 32);
bv_cmp_proof!(sle_64, blast_sle, r_sle, 64);
bv_cmp_proof!(sgt_8, blast_sgt, r_sgt, 8);
bv_cmp_proof!(sgt_32, blast_sgt, r_sgt, 32);
bv_cmp_proof!(sgt_64, blast_sgt, r_sgt, 64);
bv_cmp_proof!(sge_8, blast_sge, r_sge, 8);
bv_cmp_proof!(sge_32, blast_sge, r_sge, 32);
bv_cmp_proof!(sge_64, blast_sge, r_sge, 64);

// ── Structural (wiring rules — trivial for Kani) ───────────────────────────
use crate::aig::Lit;
use crate::blast::bitwise::blast_ite;
use crate::blast::structural::{blast_concat, blast_extract, blast_sign_ext, blast_zero_ext};

/// Concat: hi occupies the high bits, lo the low bits.
macro_rules! concat_proof {
    ($name:ident, $wh:expr, $wl:expr) => {
        #[kani::proof]
        fn $name() {
            let (wh, wl) = ($wh, $wl);
            let mut aig = Aig::new();
            let hi = word_input(&mut aig, wh);
            let lo = word_input(&mut aig, wl);
            let out = blast_concat(&hi, &lo);
            let inputs = any_bits((wh + wl) as usize);
            let vals = aig.simulate(&inputs);
            let hv = word_value(&aig, &vals, &hi);
            let lv = word_value(&aig, &vals, &lo);
            let got = word_value(&aig, &vals, &out);
            assert_eq!(got, ((hv << wl) | lv) & mask(wh + wl));
        }
    };
}
concat_proof!(concat_4_4, 4, 4);
concat_proof!(concat_16_16, 16, 16);
concat_proof!(concat_32_32, 32, 32);

/// Extract bits [hi..=lo] from a width-`w` word.
macro_rules! extract_proof {
    ($name:ident, $w:expr, $hi:expr, $lo:expr) => {
        #[kani::proof]
        fn $name() {
            let (w, hi, lo) = ($w, $hi, $lo);
            let mut aig = Aig::new();
            let a = word_input(&mut aig, w);
            let out = blast_extract(&a, hi, lo);
            let inputs = any_bits(w as usize);
            let vals = aig.simulate(&inputs);
            let av = word_value(&aig, &vals, &a);
            let got = word_value(&aig, &vals, &out);
            assert_eq!(got, (av >> lo) & mask(hi - lo + 1));
        }
    };
}
extract_proof!(extract_16_hi, 16, 15, 8);
extract_proof!(extract_16_lo, 16, 7, 0);
extract_proof!(extract_32_mid, 32, 23, 8);
extract_proof!(extract_64_hi, 64, 63, 32);

/// Zero-extend a width-`w` word by `by` bits (value unchanged, wider).
macro_rules! zext_proof {
    ($name:ident, $w:expr, $by:expr) => {
        #[kani::proof]
        fn $name() {
            let (w, by) = ($w, $by);
            let mut aig = Aig::new();
            let a = word_input(&mut aig, w);
            let out = blast_zero_ext(&a, by);
            let inputs = any_bits(w as usize);
            let vals = aig.simulate(&inputs);
            let av = word_value(&aig, &vals, &a);
            let got = word_value(&aig, &vals, &out);
            assert_eq!(got, av & mask(w + by));
        }
    };
}
zext_proof!(zext_8_8, 8, 8);
zext_proof!(zext_16_16, 16, 16);
zext_proof!(zext_32_32, 32, 32);

/// Sign-extend a width-`w` word by `by` bits.
macro_rules! sext_proof {
    ($name:ident, $w:expr, $by:expr) => {
        #[kani::proof]
        fn $name() {
            let (w, by) = ($w, $by);
            let mut aig = Aig::new();
            let a = word_input(&mut aig, w);
            let out = blast_sign_ext(&a, by);
            let inputs = any_bits(w as usize);
            let vals = aig.simulate(&inputs);
            let av = word_value(&aig, &vals, &a);
            let full = mask(w + by);
            let want = if (av >> (w - 1)) & 1 == 1 {
                (av | (full & !mask(w))) & full
            } else {
                av
            };
            let got = word_value(&aig, &vals, &out);
            assert_eq!(got, want);
        }
    };
}
sext_proof!(sext_8_8, 8, 8);
sext_proof!(sext_16_16, 16, 16);
sext_proof!(sext_32_32, 32, 32);

/// Ite: `cond ? then : else` over width `w`.
macro_rules! ite_proof {
    ($name:ident, $w:expr) => {
        #[kani::proof]
        fn $name() {
            let w = $w;
            let mut aig = Aig::new();
            let cond: Lit = aig.input();
            let then_ = word_input(&mut aig, w);
            let else_ = word_input(&mut aig, w);
            let out = blast_ite(&mut aig, cond, &then_, &else_);
            let inputs = any_bits((1 + 2 * w) as usize);
            let vals = aig.simulate(&inputs);
            let cv = aig.lit_value(&vals, cond);
            let tv = word_value(&aig, &vals, &then_);
            let ev = word_value(&aig, &vals, &else_);
            let got = word_value(&aig, &vals, &out);
            assert_eq!(got, if cv { tv } else { ev });
        }
    };
}
ite_proof!(ite_8, 8);
ite_proof!(ite_32, 32);
ite_proof!(ite_64, 64);
