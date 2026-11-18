//! WASM trap / partiality semantics (issue #59 / TR-019).
//!
//! WASM operations like `div_s`, `load`, `call_indirect`, and `unreachable` are
//! **partial**: they trap on some inputs. A verifier that proves only *value*
//! equivalence over a model in which every op is total cannot see a
//! transformation that *drops a trap* — deleting a trapping op looks value-equal
//! (loom#273/#274/#278, synth#633/#666/#665/#642). This module builds the
//! **trap condition** of each partial op as a QF_BV [`BoolTerm`] over its
//! operand/pointer *bits*, and composes trap-preservation verification
//! conditions, so trap-equivalence becomes a checkable obligation.
//!
//! **Boundary held:** ordeal *classifies* bits — it never models op *values*
//! (those are consumer-supplied) and never does floating-point arithmetic. Every
//! builder here is `BoolTerm`/`BvTerm` over the existing closed fragment: no new
//! operations, no FP theory. Soundness is unchanged — a trap-equivalence VC is
//! decided by the normal certificate-checked pipeline, so `Unsat` is
//! LRAT-validated and re-checkable ([`crate::Certificate::recheck`]).
//!
//! Consumers: synth's `translation_validator` (VCR-VER-002) gates div/rem,
//! `call_indirect`, and `unreachable` on the full [`trap_equivalence_vc`], and
//! memory ops on [`trap_condition_equivalence`] (trap-clause only, since synth
//! models no memory *contents*); loom (loom#279) uses the same builders.

use crate::eval;
use crate::solver::{CheckResult, Solver};
use crate::term::{BoolTerm, BvTerm, Sort};

fn bx(t: BvTerm) -> Box<BvTerm> {
    Box::new(t)
}
fn bb(t: BoolTerm) -> Box<BoolTerm> {
    Box::new(t)
}

/// A trivially-true `BoolTerm`. The fragment has no boolean constant, so truth
/// is encoded as a constant equality (`0 == 0` at width 8, which the AIG folds
/// to the `TRUE` literal).
fn bool_true() -> BoolTerm {
    let z = || {
        bx(BvTerm::Const {
            value: 0,
            sort: Sort::new(8),
        })
    };
    BoolTerm::Eq(z(), z())
}

/// A trivially-false `BoolTerm` (`¬true`).
fn bool_false() -> BoolTerm {
    BoolTerm::Not(bb(bool_true()))
}

/// A zero constant matching `t`'s width (width taken from the sort oracle; a
/// width-8 fallback is harmless because an ill-sorted input makes the whole
/// query `Unknown` regardless).
fn zero_like(t: &BvTerm) -> BvTerm {
    let width = eval::bv_sort(t).map(|s| s.width).unwrap_or(8);
    BvTerm::Const {
        value: 0,
        sort: Sort::new(width),
    }
}

/// A value paired with the condition under which the op **traps** instead of
/// producing it. `value` is supplied by the caller — ordeal models no op values
/// — and `may_trap` is built by the helpers in this module.
#[derive(Clone, Debug)]
pub struct DefineOrTrap {
    /// The op's result value (consumer-supplied `BvTerm`).
    pub value: BvTerm,
    /// The condition under which the op traps.
    pub may_trap: BoolTerm,
}

/// Which division/remainder op, for [`trap_div`].
#[derive(Clone, Copy, Debug)]
pub enum DivOp {
    /// `i32.div_u` / `i64.div_u`.
    DivU,
    /// `i32.div_s` / `i64.div_s`.
    DivS,
    /// `i32.rem_u` / `i64.rem_u`.
    RemU,
    /// `i32.rem_s` / `i64.rem_s`.
    RemS,
}

impl DivOp {
    /// Whether this op traps on the `INT_MIN / -1` overflow pair.
    ///
    /// **Only `div_s` does.** Per WASM Core §4.4.1 `idiv_s` traps there because
    /// the true quotient `2^(N-1)` is not representable, but `irem_s` is
    /// *defined*: `irem_s(INT_MIN, -1) = 0` (ordeal's own `bvsrem` reference
    /// agrees). `rem_s` therefore traps on divisor-zero and nothing else.
    ///
    /// Getting this wrong was ordeal#72: the clause was gated on
    /// "is the op signed", which wrongly swept in `RemS` and made the library
    /// demand a trap WASM does not have — rejecting correct `rem_s` lowerings
    /// (and blessing spuriously-trapping ones). It hid because both sides of a
    /// trap-equivalence VC used this same builder: consistent wrongness is
    /// invisible to a consistency gate. synth caught it by deriving the ARM side
    /// independently, from the emitted guard structure.
    fn traps_on_overflow(self) -> bool {
        matches!(self, DivOp::DivS)
    }
}

/// Trap condition for a division/remainder op: divide-by-zero for all four,
/// plus the `INT_MIN / -1` overflow for **`div_s` only** (see
/// [`DivOp::traps_on_overflow`] — `rem_s` does NOT trap there).
/// Pure compares — `Eq(divisor, 0)` and `And(Eq(dividend, INT_MIN), Eq(divisor, -1))`.
pub fn trap_div(op: DivOp, dividend: &BvTerm, divisor: &BvTerm, width: u32) -> BoolTerm {
    let sort = Sort::new(width);
    let zero = BvTerm::Const { value: 0, sort };
    let div_by_zero = BoolTerm::Eq(bx(divisor.clone()), bx(zero));
    if !op.traps_on_overflow() {
        return div_by_zero;
    }
    // Signed overflow: dividend == INT_MIN and divisor == -1 (all ones).
    let int_min = 1u128 << (width - 1);
    let all_ones = if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    };
    let overflow = BoolTerm::And(
        bb(BoolTerm::Eq(
            bx(dividend.clone()),
            bx(BvTerm::Const {
                value: int_min,
                sort,
            }),
        )),
        bb(BoolTerm::Eq(
            bx(divisor.clone()),
            bx(BvTerm::Const {
                value: all_ones,
                sort,
            }),
        )),
    );
    BoolTerm::Or(bb(div_by_zero), bb(overflow))
}

/// Trap condition for `unreachable`: an unconditional trap.
pub fn trap_always() -> BoolTerm {
    bool_true()
}

/// Trap condition for an OOB `load`/`store`: a `size`-byte access at `addr`
/// exceeds `mem_bound` (`addr + size >u mem_bound`). **Wraparound-safe** — each
/// operand is zero-extended by one bit before the add, so `addr + size` cannot
/// alias a small value. `addr`, `size`, and `mem_bound` must share a width;
/// `mem_bound` is the caller's symbolic linear-memory extent.
pub fn trap_mem_oob(addr: &BvTerm, size: &BvTerm, mem_bound: &BvTerm) -> BoolTerm {
    let ext = |t: &BvTerm| {
        bx(BvTerm::ZeroExt {
            by: 1,
            arg: bx(t.clone()),
        })
    };
    let end = BvTerm::Add(ext(addr), ext(size));
    BoolTerm::Ugt(bx(end), ext(mem_bound))
}

/// The type-check mode of a `call_indirect`, per its table.
pub enum TypeTrap<'a> {
    /// Heterogeneous table: the element type is checked at runtime against the
    /// call's expected type id — traps on `Ne(actual_type_id, expected_id)`.
    Runtime {
        /// The table element's runtime type-id term.
        actual_type_id: &'a BvTerm,
        /// The call site's expected type-id term.
        expected_id: &'a BvTerm,
    },
    /// Closed-world / homogeneous table: the signature is discharged at compile
    /// time by the selector, so there is no runtime type-id and the type clause
    /// contributes `false` (the VC never demands a term that does not exist).
    StaticallyDischarged,
}

/// The operands of a `call_indirect` trap check (WASM §4.4.8).
pub struct CallIndirect<'a> {
    /// The table index operand.
    pub index: &'a BvTerm,
    /// The table's element count.
    pub table_size: &'a BvTerm,
    /// The loaded funcref word; a null (zero) slot traps before the call.
    pub slot_ptr: &'a BvTerm,
    /// How the element's type is checked.
    pub type_trap: TypeTrap<'a>,
}

/// Trap condition for `call_indirect`: `bounds ∨ null-slot ∨ type`
/// (`Uge(index, table_size)`, `Eq(slot_ptr, 0)`, and the [`TypeTrap`] clause).
pub fn trap_call_indirect(ci: &CallIndirect) -> BoolTerm {
    let bounds = BoolTerm::Uge(bx(ci.index.clone()), bx(ci.table_size.clone()));
    let null_slot = BoolTerm::Eq(bx(ci.slot_ptr.clone()), bx(zero_like(ci.slot_ptr)));
    let type_clause = match &ci.type_trap {
        TypeTrap::Runtime {
            actual_type_id,
            expected_id,
        } => BoolTerm::Ne(bx((*actual_type_id).clone()), bx((*expected_id).clone())),
        TypeTrap::StaticallyDischarged => bool_false(),
    };
    BoolTerm::Or(bb(BoolTerm::Or(bb(bounds), bb(null_slot))), bb(type_clause))
}

// ---------------------------------------------------------------------------
// Float→int truncation traps (Phase B, synth #709).
//
// WASM `iN.trunc_fM_s/u` traps on NaN, ±∞, and when the round-toward-zero
// truncation falls outside the target integer range. ordeal stays QF_BV: the
// float enters ONLY as its bit pattern (BV32/BV64) and is *classified* with
// extracts and unsigned compares — no FP theory, no new ops. The key fact is
// IEEE-754's monotonic bit order: for a fixed sign, a float's magnitude is
// strictly monotonic in the unsigned integer value of its sign-stripped bit
// pattern, so "|x| ≥ threshold" is a single `Uge` against a constant pattern.
// ---------------------------------------------------------------------------

/// An IEEE-754 binary interchange format, for the trunc-trap classifiers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FpFmt {
    /// binary32: 1 sign / 8 exponent / 23 mantissa bits.
    F32,
    /// binary64: 1 sign / 11 exponent / 52 mantissa bits.
    F64,
}

impl FpFmt {
    /// Total width of the bit pattern (32 / 64).
    pub const fn total_bits(self) -> u32 {
        match self {
            FpFmt::F32 => 32,
            FpFmt::F64 => 64,
        }
    }
    /// Width of the biased-exponent field (8 / 11).
    pub const fn exp_bits(self) -> u32 {
        match self {
            FpFmt::F32 => 8,
            FpFmt::F64 => 11,
        }
    }
    /// Width of the trailing-significand (mantissa) field (23 / 52).
    pub const fn mant_bits(self) -> u32 {
        match self {
            FpFmt::F32 => 23,
            FpFmt::F64 => 52,
        }
    }
    /// Exponent bias (127 / 1023).
    const fn bias(self) -> u32 {
        match self {
            FpFmt::F32 => 127,
            FpFmt::F64 => 1023,
        }
    }
    /// The all-ones exponent-field value (NaN/∞ marker: 0xFF / 0x7FF).
    const fn exp_all_ones(self) -> u128 {
        (1u128 << self.exp_bits()) - 1
    }
}

/// The integer target of a truncation, for [`fp_trunc_out_of_range`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntTarget {
    /// `i32` (WASM `i32.trunc_f*`).
    I32,
    /// `i64` (WASM `i64.trunc_f*`).
    I64,
}

impl IntTarget {
    /// Bit width of the target integer (32 / 64).
    pub const fn width(self) -> u32 {
        match self {
            IntTarget::I32 => 32,
            IntTarget::I64 => 64,
        }
    }
}

/// Extract the biased-exponent field `bits[total-2 : mant]`.
fn fp_exp_field(bits: &BvTerm, fmt: FpFmt) -> BvTerm {
    BvTerm::Extract {
        hi: fmt.total_bits() - 2,
        lo: fmt.mant_bits(),
        arg: bx(bits.clone()),
    }
}

/// Extract the trailing-significand field `bits[mant-1 : 0]`.
fn fp_mant_field(bits: &BvTerm, fmt: FpFmt) -> BvTerm {
    BvTerm::Extract {
        hi: fmt.mant_bits() - 1,
        lo: 0,
        arg: bx(bits.clone()),
    }
}

/// Extract the sign bit `bits[total-1]` (1-bit term).
fn fp_sign_bit(bits: &BvTerm, fmt: FpFmt) -> BvTerm {
    let hi = fmt.total_bits() - 1;
    BvTerm::Extract {
        hi,
        lo: hi,
        arg: bx(bits.clone()),
    }
}

/// Extract the sign-stripped magnitude pattern `bits[total-2 : 0]`. For a fixed
/// sign, IEEE float magnitude is monotonic in this unsigned value.
fn fp_magnitude(bits: &BvTerm, fmt: FpFmt) -> BvTerm {
    BvTerm::Extract {
        hi: fmt.total_bits() - 2,
        lo: 0,
        arg: bx(bits.clone()),
    }
}

/// `exp field == all-ones` (the NaN/∞ exponent marker).
fn fp_exp_is_all_ones(bits: &BvTerm, fmt: FpFmt) -> BoolTerm {
    BoolTerm::Eq(
        bx(fp_exp_field(bits, fmt)),
        bx(BvTerm::Const {
            value: fmt.exp_all_ones(),
            sort: Sort::new(fmt.exp_bits()),
        }),
    )
}

/// The float's bits encode a NaN: exponent all-ones AND mantissa ≠ 0.
pub fn fp_is_nan(bits: &BvTerm, fmt: FpFmt) -> BoolTerm {
    let mant_nonzero = BoolTerm::Ne(
        bx(fp_mant_field(bits, fmt)),
        bx(BvTerm::Const {
            value: 0,
            sort: Sort::new(fmt.mant_bits()),
        }),
    );
    BoolTerm::And(bb(fp_exp_is_all_ones(bits, fmt)), bb(mant_nonzero))
}

/// The float's bits encode ±∞: exponent all-ones AND mantissa == 0.
pub fn fp_is_inf(bits: &BvTerm, fmt: FpFmt) -> BoolTerm {
    let mant_zero = BoolTerm::Eq(
        bx(fp_mant_field(bits, fmt)),
        bx(BvTerm::Const {
            value: 0,
            sort: Sort::new(fmt.mant_bits()),
        }),
    );
    BoolTerm::And(bb(fp_exp_is_all_ones(bits, fmt)), bb(mant_zero))
}

/// Sign-stripped bit pattern of `2^k` in `fmt`: exponent field `bias + k`,
/// mantissa 0. Exact for every `k` used here (k ≤ 64 ≪ exponent range).
fn pow2_magnitude_pattern(fmt: FpFmt, k: u32) -> u128 {
    ((fmt.bias() + k) as u128) << fmt.mant_bits()
}

/// Sign-stripped bit pattern of the **smallest** float of `fmt` whose value is
/// `≥ 2^k + 1` — the negative-side trap threshold for a signed target of width
/// `k + 1` (trap iff `x ≤ -(2^k + 1)`, i.e. `|x| ≥ 2^k + 1`).
///
/// If the format has ≥ `k` mantissa bits, `2^k + 1` is exactly representable:
/// pattern of `2^k` with mantissa bit `mant - k` set. Otherwise the next float
/// above `2^k` (pattern + 1, one ULP) is the smallest one `≥ 2^k + 1`.
fn min_pattern_ge_pow2_plus_1(fmt: FpFmt, k: u32) -> u128 {
    let p2 = pow2_magnitude_pattern(fmt, k);
    if fmt.mant_bits() >= k {
        p2 | (1u128 << (fmt.mant_bits() - k))
    } else {
        p2 + 1
    }
}

/// The float's truncation (round-toward-zero) falls outside the target integer
/// range — **finite values only** (NaN/∞ are `false` here; they are separate
/// disjuncts of [`trap_trunc`]). Matches WASM `iN.trunc_fM_s/u` (synth #709):
///
/// - signed:   in-range iff `trunc(x) ∈ [-2^(N-1), 2^(N-1)-1]`, i.e.
///   `-(2^(N-1)+1) < x < 2^(N-1)`. Positive trap: `|x| ≥ 2^(N-1)` (so
///   `x == 2^(N-1)` traps). Negative trap: `|x| ≥ 2^(N-1)+1` (so
///   `x == -2^(N-1)` converts, and any float in `(-(2^(N-1)+1), -2^(N-1)]`
///   truncates to `-2^(N-1)`).
/// - unsigned: in-range iff `trunc(x) ∈ [0, 2^N-1]`, i.e. `-1 < x < 2^N`.
///   Positive trap: `|x| ≥ 2^N`. Negative trap: `|x| ≥ 1` (so `x == -1.0`
///   traps but `-1 < x < 0`, incl. `-0.0`, truncates to 0).
///
/// Each magnitude bound is one unsigned compare against a constant bit pattern
/// (IEEE monotonic bit order), split on the sign bit.
pub fn fp_trunc_out_of_range(
    bits: &BvTerm,
    fmt: FpFmt,
    target: IntTarget,
    signed: bool,
) -> BoolTerm {
    let mag_sort = Sort::new(fmt.total_bits() - 1);
    let mag = fp_magnitude(bits, fmt);
    let is_neg = BoolTerm::Eq(
        bx(fp_sign_bit(bits, fmt)),
        bx(BvTerm::Const {
            value: 1,
            sort: Sort::new(1),
        }),
    );
    let finite = BoolTerm::Not(bb(fp_exp_is_all_ones(bits, fmt)));

    // Positive side: trap iff x ≥ 2^k, k = N (unsigned) / N-1 (signed).
    let k = target.width() - u32::from(signed);
    let pos_thresh = pow2_magnitude_pattern(fmt, k);
    // Negative side: trap iff |x| ≥ 2^(N-1)+1 (signed) / ≥ 1.0 (unsigned).
    let neg_thresh = if signed {
        min_pattern_ge_pow2_plus_1(fmt, target.width() - 1)
    } else {
        pow2_magnitude_pattern(fmt, 0) // bit pattern of 1.0
    };

    let uge_const = |t: BvTerm, value: u128| {
        BoolTerm::Uge(
            bx(t),
            bx(BvTerm::Const {
                value,
                sort: mag_sort,
            }),
        )
    };
    let pos_oob = BoolTerm::And(
        bb(BoolTerm::Not(bb(is_neg.clone()))),
        bb(uge_const(mag.clone(), pos_thresh)),
    );
    let neg_oob = BoolTerm::And(bb(is_neg), bb(uge_const(mag, neg_thresh)));
    BoolTerm::And(bb(finite), bb(BoolTerm::Or(bb(pos_oob), bb(neg_oob))))
}

/// Trap condition for WASM `iN.trunc_fM_s/u` (synth #709):
/// `NaN ∨ ±∞ ∨ out-of-range` over the float's bit pattern.
pub fn trap_trunc(bits: &BvTerm, fmt: FpFmt, target: IntTarget, signed: bool) -> BoolTerm {
    BoolTerm::Or(
        bb(BoolTerm::Or(
            bb(fp_is_nan(bits, fmt)),
            bb(fp_is_inf(bits, fmt)),
        )),
        bb(fp_trunc_out_of_range(bits, fmt, target, signed)),
    )
}

/// Compose a block's trap condition from its partial ops: `may_trap` holds iff
/// **any** of `conds` holds (an `Or`-fold; empty ⇒ never traps). Sound for
/// straight-line code — control-flow sequencing is the consumer's VC's job.
pub fn trap_any(conds: &[BoolTerm]) -> BoolTerm {
    match conds.split_first() {
        None => bool_false(),
        Some((first, rest)) => rest
            .iter()
            .fold(first.clone(), |acc, c| BoolTerm::Or(bb(acc), bb(c.clone()))),
    }
}

/// Material biconditional `a ⇔ b`, desugared to `And/Or/Not` (the fragment has
/// no boolean XOR/iff).
fn iff(a: &BoolTerm, b: &BoolTerm) -> BoolTerm {
    let imp =
        |x: &BoolTerm, y: &BoolTerm| BoolTerm::Or(bb(BoolTerm::Not(bb(x.clone()))), bb(y.clone()));
    BoolTerm::And(bb(imp(a, b)), bb(imp(b, a)))
}

/// **Trap-condition equivalence** (conjunct 1 only): `orig.may_trap ⇔ opt.may_trap`.
/// Lets a consumer that does not model an op's *value* still prove the trap was
/// not dropped or spuriously added — the whole win for memory ops (OOB/null),
/// where synth has the trap clause but no memory-contents model. Returns the
/// goal to prove **valid**.
pub fn trap_condition_equivalence(orig_may_trap: &BoolTerm, opt_may_trap: &BoolTerm) -> BoolTerm {
    iff(orig_may_trap, opt_may_trap)
}

/// **Trap-preservation VC** (both conjuncts): the lowering preserves traps *and*
/// values —
/// `(orig.may_trap ⇔ opt.may_trap) ∧ (¬orig.may_trap ⇒ orig.value == opt.value)`.
/// Returns the goal to prove **valid** (assert its negation and check; `Unsat`
/// ⟹ preserved).
pub fn trap_equivalence_vc(orig: &DefineOrTrap, opt: &DefineOrTrap) -> BoolTerm {
    let trap_eq = iff(&orig.may_trap, &opt.may_trap);
    // ¬orig.may_trap ⇒ value_eq  ==  orig.may_trap ∨ (orig.value == opt.value)
    let value_eq = BoolTerm::Eq(bx(orig.value.clone()), bx(opt.value.clone()));
    let guarded_value = BoolTerm::Or(bb(orig.may_trap.clone()), bb(value_eq));
    BoolTerm::And(bb(trap_eq), bb(guarded_value))
}

/// One-call trap-preservation gate over the full VC ([`trap_equivalence_vc`]).
/// `Unsat` ⟹ the lowering preserves traps and values.
///
/// Delegates to the public [`Solver::prove_valid`] (issue #66): this module's
/// gate *is* "prove the trap-equivalence VC valid", so it uses the shared
/// primitive rather than its own copy.
pub fn prove_trap_equivalence(orig: &DefineOrTrap, opt: &DefineOrTrap) -> CheckResult {
    Solver::prove_valid(trap_equivalence_vc(orig, opt))
}

/// One-call trap-drop gate over conjunct 1 only ([`trap_condition_equivalence`]).
/// `Unsat` ⟹ the lowering neither drops nor spuriously adds a trap (value clause
/// not considered — for consumers without a value model on this op).
pub fn prove_trap_condition_equivalence(
    orig_may_trap: &BoolTerm,
    opt_may_trap: &BoolTerm,
) -> CheckResult {
    Solver::prove_valid(trap_condition_equivalence(orig_may_trap, opt_may_trap))
}

// ---------------------------------------------------------------------------
// Trap REFINEMENT (issue #284, TR-082; loom#313 / loom#300).
//
// Equivalence ([`trap_equivalence_vc`]) demands that the optimised code
// produce the SAME value as the original. That is too strong for WASM float
// results: when an op yields a NaN, the spec (Core §4.3.3, `nans_N`) lets it
// yield any member of a SET of NaNs, so an optimiser that constant-folds
// `0.0 / 0.0` to the canonical NaN `0x7fc00000` is correct even though the
// original's model produced another member of the set. What loom needs is
// REFINEMENT: the optimised code traps exactly when the original does, and
// otherwise produces a value the original was ALLOWED to produce.
//
// The set is described over bit patterns only. "Is a NaN", "is a canonical
// NaN" and "is an arithmetic NaN" are extracts and constant compares on the
// exponent and trailing-significand fields; no floating-point value is ever
// computed and no operation is added to the closed fragment.
// ---------------------------------------------------------------------------

/// The value-field pattern of the canonical NaN payload: only the most
/// significant trailing-significand bit set (`1 << (mant - 1)`; WASM Core
/// §4.3.3 `canon_N = 2^(signif(N) - 1)`).
const fn canon_payload(fmt: FpFmt) -> u128 {
    1u128 << (fmt.mant_bits() - 1)
}

/// The float's bits encode a **canonical NaN** (WASM Core §4.3.3): exponent
/// all-ones and trailing significand exactly `canon_N` (only its top bit set),
/// with either sign. `0x7fc00000` / `0xffc00000` for f32,
/// `0x7ff8000000000000` / `0xfff8000000000000` for f64.
pub fn fp_is_canonical_nan(bits: &BvTerm, fmt: FpFmt) -> BoolTerm {
    let payload_canon = BoolTerm::Eq(
        bx(fp_mant_field(bits, fmt)),
        bx(BvTerm::Const {
            value: canon_payload(fmt),
            sort: Sort::new(fmt.mant_bits()),
        }),
    );
    BoolTerm::And(bb(fp_exp_is_all_ones(bits, fmt)), bb(payload_canon))
}

/// The float's bits encode an **arithmetic NaN** (WASM Core §4.3.3): exponent
/// all-ones and the top trailing-significand bit (the quiet bit) set, i.e. the
/// payload is `≥ canon_N`. Every canonical NaN is arithmetic; a signalling NaN
/// (quiet bit clear, payload non-zero) is a NaN that is not arithmetic.
pub fn fp_is_arithmetic_nan(bits: &BvTerm, fmt: FpFmt) -> BoolTerm {
    let m = fmt.mant_bits();
    let quiet = BoolTerm::Eq(
        bx(BvTerm::Extract {
            hi: m - 1,
            lo: m - 1,
            arg: bx(bits.clone()),
        }),
        bx(BvTerm::Const {
            value: 1,
            sort: Sort::new(1),
        }),
    );
    BoolTerm::And(bb(fp_exp_is_all_ones(bits, fmt)), bb(quiet))
}

/// Which NaNs a float result may be, when it is a NaN.
#[derive(Clone, Debug)]
pub enum NanSet {
    /// Any canonical NaN, either sign ([`fp_is_canonical_nan`]).
    Canonical,
    /// Any arithmetic NaN, either sign ([`fp_is_arithmetic_nan`]).
    Arithmetic,
    /// WASM's `nans_N{z*}` (Core §4.3.3) for an op whose float operands are
    /// `z*` (each with its own format, so `f64.promote_f32` passes an f32
    /// operand): the canonical NaNs when every operand that is a NaN is a
    /// canonical NaN (vacuously, when no operand is a NaN), the arithmetic
    /// NaNs otherwise. The choice is made per input, inside the formula.
    Propagating(Vec<(BvTerm, FpFmt)>),
}

/// The set of values the ORIGINAL code may produce when it does not trap.
///
/// **Why this representation** (TR-082). loom's semantics of a WASM op is one
/// bit pattern, except for the float ops whose NaN result the spec leaves
/// open. So the set is either a single pattern, or "this pattern, unless it
/// is a NaN, in which case any NaN of the stated kind". Both are a predicate
/// on the optimised value built from compares and extracts (see
/// [`value_set_member`]), so the refinement VC stays in the closed QF_BV
/// fragment. An "any NaN at all" set is deliberately not offered: the ops
/// with NaN freedom never return a signalling NaN (`nans_N` holds only
/// canonical or arithmetic NaNs), so that set would be wider than the
/// original's and would accept an optimisation that is not a refinement
/// (see the `x + -0.0 → x` test).
#[derive(Clone, Debug)]
pub enum ValueSet {
    /// Exactly this value. Every integer op; and the float ops the spec makes
    /// bit-exact on NaN (`neg`, `abs`, `copysign`, `reinterpret`, loads,
    /// `select`).
    Exact(BvTerm),
    /// A float result of format `fmt` with the spec's NaN freedom: when
    /// `value` is not a NaN the set is `{value}`; when `value` is a NaN the
    /// set is `nans`. `value` is the consumer's model of the result (ordeal
    /// computes no float value); its NaN payload does not matter, only that
    /// it is a NaN.
    Float {
        /// The original's result bit pattern (width `fmt.total_bits()`).
        value: BvTerm,
        /// The float format of the result.
        fmt: FpFmt,
        /// The NaNs the result may be when `value` is a NaN.
        nans: NanSet,
    },
}

/// The original side of a refinement check: the condition under which it
/// traps, and the set of values it may produce when it does not. The
/// set-valued twin of [`DefineOrTrap`] (which converts into it with an
/// [`ValueSet::Exact`] set).
#[derive(Clone, Debug)]
pub struct DefineSetOrTrap {
    /// The values the original may produce when it does not trap.
    pub values: ValueSet,
    /// The condition under which the original traps.
    pub may_trap: BoolTerm,
}

impl From<DefineOrTrap> for DefineSetOrTrap {
    fn from(d: DefineOrTrap) -> Self {
        DefineSetOrTrap {
            values: ValueSet::Exact(d.value),
            may_trap: d.may_trap,
        }
    }
}

/// `x ∈ nans`: `x` is a NaN of `fmt` of the kind `nans` names.
pub fn nan_set_member(x: &BvTerm, fmt: FpFmt, nans: &NanSet) -> BoolTerm {
    match nans {
        NanSet::Canonical => fp_is_canonical_nan(x, fmt),
        NanSet::Arithmetic => fp_is_arithmetic_nan(x, fmt),
        NanSet::Propagating(operands) => {
            // all_canon = ∧ (¬is_nan(z) ∨ is_canonical_nan(z)); empty ⇒ true.
            let all_canon = operands.iter().fold(bool_true(), |acc, (z, zf)| {
                let ok = BoolTerm::Or(
                    bb(BoolTerm::Not(bb(fp_is_nan(z, *zf)))),
                    bb(fp_is_canonical_nan(z, *zf)),
                );
                BoolTerm::And(bb(acc), bb(ok))
            });
            // all_canon ? canonical(x) : arithmetic(x)
            BoolTerm::Or(
                bb(BoolTerm::And(
                    bb(all_canon.clone()),
                    bb(fp_is_canonical_nan(x, fmt)),
                )),
                bb(BoolTerm::And(
                    bb(BoolTerm::Not(bb(all_canon))),
                    bb(fp_is_arithmetic_nan(x, fmt)),
                )),
            )
        }
    }
}

/// `x ∈ set`, as a bit-pattern predicate. `Exact(v)` is `x == v`;
/// `Float { value, fmt, nans }` is
/// `(¬is_nan(value) ∧ x == value) ∨ (is_nan(value) ∧ x ∈ nans)`. A non-NaN
/// float result must match bit for bit (so `+0.0` and `-0.0` differ).
pub fn value_set_member(x: &BvTerm, set: &ValueSet) -> BoolTerm {
    match set {
        ValueSet::Exact(v) => BoolTerm::Eq(bx(x.clone()), bx(v.clone())),
        ValueSet::Float { value, fmt, nans } => {
            let value_nan = fp_is_nan(value, *fmt);
            let same = BoolTerm::And(
                bb(BoolTerm::Not(bb(value_nan.clone()))),
                bb(BoolTerm::Eq(bx(x.clone()), bx(value.clone()))),
            );
            let in_nans = BoolTerm::And(bb(value_nan), bb(nan_set_member(x, *fmt, nans)));
            BoolTerm::Or(bb(same), bb(in_nans))
        }
    }
}

/// **Trap-refinement violation** (issue #284): the formula
///
/// `orig.trap ≠ opt.trap ∨ (¬orig.trap ∧ opt.value ∉ orig.values)`
///
/// whose **`Unsat` means `opt` refines `orig`**: on every input `opt` traps
/// exactly when `orig` does, and when neither traps `opt`'s value is one
/// `orig` may produce. A model is an input on which the optimisation is
/// wrong — either a dropped or added trap, or a value outside the set.
///
/// Unlike the other VCs in this module this returns the formula to assert
/// (not the goal to prove valid), because that is the shape the issue and
/// loom state it in; [`prove_trap_refinement`] decides it.
pub fn trap_refinement_violation(orig: &DefineSetOrTrap, opt: &DefineOrTrap) -> BoolTerm {
    let trap_differs = BoolTerm::Not(bb(iff(&orig.may_trap, &opt.may_trap)));
    let value_outside = BoolTerm::And(
        bb(BoolTerm::Not(bb(orig.may_trap.clone()))),
        bb(BoolTerm::Not(bb(value_set_member(
            &opt.value,
            &orig.values,
        )))),
    );
    BoolTerm::Or(bb(trap_differs), bb(value_outside))
}

/// One-call refinement gate: assert [`trap_refinement_violation`] and decide
/// it on the certificate-checked pipeline. [`CheckResult::Unsat`] ⟹ `opt`
/// refines `orig` (the certificate was validated before return and
/// re-checks with `cert.recheck()`); [`CheckResult::Sat`] ⟹ the model is an
/// input on which it does not; [`CheckResult::Unknown`] ⟹ no claim (e.g. a
/// width mismatch) — keep the original.
pub fn prove_trap_refinement(orig: &DefineSetOrTrap, opt: &DefineOrTrap) -> CheckResult {
    let mut s = Solver::new();
    s.assert(trap_refinement_violation(orig, opt));
    s.check()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval::Env;

    fn v(name: &str, w: u32) -> BvTerm {
        BvTerm::Var {
            name: name.into(),
            sort: Sort::new(w),
        }
    }
    fn c(value: u128, w: u32) -> BvTerm {
        BvTerm::Const {
            value,
            sort: Sort::new(w),
        }
    }
    fn env2(a: u128, b: u128) -> Env {
        let mut e = Env::new();
        e.insert("a".into(), a);
        e.insert("b".into(), b);
        e
    }

    // ---- trap-condition builders: eval-equivalence against the reference ----

    /// Spec-grounded reference for WASM Core §4.4.1 div/rem trapping, derived
    /// from **result definability** — NOT from `trap_div`'s own predicates.
    ///
    /// That independence is the whole point: ordeal#72 hid because this test
    /// previously reused `DivOp::is_signed()`, the very predicate that was
    /// wrong, so it mirrored the bug instead of catching it. Here the answer
    /// comes from the spec's actual reason to trap — "the exact result is not
    /// representable" — computed in `i128`.
    fn wasm_div_traps(op: DivOp, x: u128, y: u128, w: u32) -> bool {
        // Divisor zero traps for all four ops.
        if y == 0 {
            return true;
        }
        let to_signed = |v: u128| -> i128 {
            let half = 1i128 << (w - 1);
            let val = v as i128;
            if val >= half { val - (1i128 << w) } else { val }
        };
        match op {
            // Unsigned div/rem are total once the divisor is non-zero.
            DivOp::DivU | DivOp::RemU => false,
            // irem_s is TOTAL for a non-zero divisor: |rem| < |divisor|, so the
            // result is always representable — including irem_s(INT_MIN, -1) = 0.
            DivOp::RemS => false,
            // idiv_s traps exactly when the exact quotient does not fit.
            DivOp::DivS => {
                let q = to_signed(x) / to_signed(y);
                let (lo, hi) = (-(1i128 << (w - 1)), (1i128 << (w - 1)) - 1);
                q < lo || q > hi
            }
        }
    }

    #[test]
    fn trap_div_matches_wasm_semantics() {
        let w = 8u32;
        let (a, b) = (v("a", w), v("b", w));
        for op in [DivOp::DivU, DivOp::DivS, DivOp::RemU, DivOp::RemS] {
            let cond = trap_div(op, &a, &b, w);
            for av in 0u128..256 {
                for bv in 0u128..256 {
                    let got = eval::eval_bool(&cond, &env2(av, bv)).unwrap();
                    let want = wasm_div_traps(op, av, bv, w);
                    assert_eq!(got, want, "{op:?} a={av:#04x} b={bv:#04x}");
                }
            }
        }
    }

    #[test]
    fn rem_s_does_not_trap_on_the_int_min_over_minus_one_pair() {
        // The ordeal#72 regression, pinned explicitly: div_s traps on the
        // overflow pair (quotient 2^(w-1) is unrepresentable) but rem_s does
        // NOT — irem_s(INT_MIN, -1) = 0. Found by synth's derived-ARM-trap gate
        // (synth#166) rejecting a CORRECT shipped rem_s lowering.
        for w in [8u32, 32] {
            let (a, b) = (v("a", w), v("b", w));
            let int_min = 1u128 << (w - 1);
            let minus_one = if w >= 128 {
                u128::MAX
            } else {
                (1u128 << w) - 1
            };
            let at = |op: DivOp| {
                let mut e = Env::new();
                e.insert("a".into(), int_min);
                e.insert("b".into(), minus_one);
                eval::eval_bool(&trap_div(op, &a, &b, w), &e).unwrap()
            };
            assert!(at(DivOp::DivS), "div_s MUST trap on INT_MIN/-1 (w{w})");
            assert!(!at(DivOp::RemS), "rem_s must NOT trap on INT_MIN/-1 (w{w})");
            assert!(!at(DivOp::RemU), "rem_u must NOT trap on INT_MIN/-1 (w{w})");
            // …and every op still traps on divisor zero.
            for op in [DivOp::DivU, DivOp::DivS, DivOp::RemU, DivOp::RemS] {
                let mut e = Env::new();
                e.insert("a".into(), int_min);
                e.insert("b".into(), 0);
                assert!(
                    eval::eval_bool(&trap_div(op, &a, &b, w), &e).unwrap(),
                    "{op:?} must trap on divisor zero (w{w})"
                );
            }
        }
    }

    #[test]
    fn trap_always_is_true() {
        assert!(eval::eval_bool(&trap_always(), &Env::new()).unwrap());
    }

    #[test]
    fn trap_mem_oob_matches_reference_and_is_wraparound_safe() {
        // 8-bit address space; access size 4. OOB iff addr + 4 > bound.
        let addr = v("a", 8);
        let bound = v("b", 8);
        let size = c(4, 8);
        let cond = trap_mem_oob(&addr, &size, &bound);
        for a in 0u128..256 {
            for b in 0u128..256 {
                let got = eval::eval_bool(&cond, &env2(a, b)).unwrap();
                // Reference in wide arithmetic (no 8-bit wraparound).
                assert_eq!(got, a + 4 > b, "addr={a} bound={b}");
            }
        }
        // Explicit wraparound guard: addr=254, size=4 → end 258 > any 8-bit
        // bound, must be OOB even though 254+4 wraps to 2 in 8-bit modular add.
        assert!(eval::eval_bool(&cond, &env2(254, 255)).unwrap());
    }

    #[test]
    fn trap_call_indirect_covers_bounds_null_and_type() {
        let index = v("a", 32);
        let table_size = c(10, 32);
        let slot = v("b", 32);
        // Runtime type check against expected id 7.
        let actual = BvTerm::Var {
            name: "t".into(),
            sort: Sort::new(32),
        };
        let expected = c(7, 32);
        let ci = CallIndirect {
            index: &index,
            table_size: &table_size,
            slot_ptr: &slot,
            type_trap: TypeTrap::Runtime {
                actual_type_id: &actual,
                expected_id: &expected,
            },
        };
        let cond = trap_call_indirect(&ci);
        let eval = |idx: u128, slotv: u128, t: u128| {
            let mut e = Env::new();
            e.insert("a".into(), idx);
            e.insert("b".into(), slotv);
            e.insert("t".into(), t);
            eval::eval_bool(&cond, &e).unwrap()
        };
        assert!(eval(10, 1, 7), "index == size is out of bounds");
        assert!(eval(3, 0, 7), "null slot traps");
        assert!(eval(3, 1, 9), "type mismatch traps");
        assert!(
            !eval(3, 1, 7),
            "in-bounds, non-null, matching type: no trap"
        );
    }

    #[test]
    fn statically_discharged_type_never_contributes_a_trap() {
        let index = v("a", 32);
        let table_size = c(10, 32);
        let slot = v("b", 32);
        let ci = CallIndirect {
            index: &index,
            table_size: &table_size,
            slot_ptr: &slot,
            type_trap: TypeTrap::StaticallyDischarged,
        };
        let cond = trap_call_indirect(&ci);
        // In-bounds + non-null ⇒ no trap, regardless of any (absent) type id.
        let mut e = Env::new();
        e.insert("a".into(), 3);
        e.insert("b".into(), 1);
        assert!(!eval::eval_bool(&cond, &e).unwrap());
    }

    #[test]
    fn trap_any_is_the_or_fold() {
        assert!(!eval::eval_bool(&trap_any(&[]), &Env::new()).unwrap());
        let a_zero = BoolTerm::Eq(Box::new(v("a", 8)), Box::new(c(0, 8)));
        let b_zero = BoolTerm::Eq(Box::new(v("b", 8)), Box::new(c(0, 8)));
        let any = trap_any(&[a_zero, b_zero]);
        assert!(eval::eval_bool(&any, &env2(0, 5)).unwrap());
        assert!(eval::eval_bool(&any, &env2(5, 0)).unwrap());
        assert!(!eval::eval_bool(&any, &env2(5, 5)).unwrap());
    }

    // ---- float→int truncation traps (Phase B, synth #709) ----
    //
    // The proof style: build the BoolTerm classifier, then evaluate it with
    // `eval::eval_bool` against a reference predicate computed on the REAL
    // Rust float (`f32::from_bits` / `f64::from_bits`, `is_nan`,
    // `is_infinite`, `trunc`). The reference does all range math in f64,
    // which is exact for every case here: f32→f64 is exact, `trunc` of a
    // finite float is an exactly-representable integer-valued f64, the
    // bounds ±2^31, ±2^63, 2^32, 2^64, 0 are exact f64 values, and for an
    // integer t, `t ≤ 2^N - 1 ⟺ t < 2^N` (so the unrepresentable 2^63-1 /
    // 2^64-1 bounds are never materialized).

    /// The float value (widened to f64, exactly) of a bit pattern.
    fn fval(fmt: FpFmt, p: u128) -> f64 {
        match fmt {
            FpFmt::F32 => f32::from_bits(p as u32) as f64,
            FpFmt::F64 => f64::from_bits(p as u64),
        }
    }

    /// Reference: finite `x` truncates (round-toward-zero) outside the target
    /// range. Caller guards non-finite inputs.
    fn ref_out_of_range(x: f64, target: IntTarget, signed: bool) -> bool {
        let t = x.trunc();
        let n = target.width() as i32;
        if signed {
            !(t >= -(2f64.powi(n - 1)) && t < 2f64.powi(n - 1))
        } else {
            !(t >= 0.0 && t < 2f64.powi(n))
        }
    }

    /// Reference: the exact WASM `iN.trunc_fM_s/u` trap predicate.
    fn ref_trap_trunc(x: f64, target: IntTarget, signed: bool) -> bool {
        !x.is_finite() || ref_out_of_range(x, target, signed)
    }

    /// The derived magnitude thresholds must be the bit patterns of the IEEE
    /// values the WASM spec bounds are stated in. Cross-checked against the
    /// host float's `to_bits`, plus the one-ULP semantics of the negative
    /// signed threshold (smallest float ≥ 2^k + 1).
    #[test]
    fn derived_threshold_constants_match_ieee_bit_patterns() {
        for k in [0u32, 31, 32, 63, 64] {
            assert_eq!(
                pow2_magnitude_pattern(FpFmt::F32, k),
                2f32.powi(k as i32).to_bits() as u128,
                "f32 2^{k}"
            );
            assert_eq!(
                pow2_magnitude_pattern(FpFmt::F64, k),
                2f64.powi(k as i32).to_bits() as u128,
                "f64 2^{k}"
            );
        }
        // Spelled-out constants, for clean-room comparison.
        assert_eq!(pow2_magnitude_pattern(FpFmt::F32, 31), 0x4F00_0000);
        assert_eq!(pow2_magnitude_pattern(FpFmt::F32, 32), 0x4F80_0000);
        assert_eq!(pow2_magnitude_pattern(FpFmt::F32, 63), 0x5F00_0000);
        assert_eq!(pow2_magnitude_pattern(FpFmt::F32, 64), 0x5F80_0000);
        assert_eq!(pow2_magnitude_pattern(FpFmt::F32, 0), 0x3F80_0000);
        assert_eq!(
            pow2_magnitude_pattern(FpFmt::F64, 31),
            0x41E0_0000_0000_0000
        );
        assert_eq!(
            pow2_magnitude_pattern(FpFmt::F64, 32),
            0x41F0_0000_0000_0000
        );
        assert_eq!(
            pow2_magnitude_pattern(FpFmt::F64, 63),
            0x43E0_0000_0000_0000
        );
        assert_eq!(
            pow2_magnitude_pattern(FpFmt::F64, 64),
            0x43F0_0000_0000_0000
        );
        assert_eq!(pow2_magnitude_pattern(FpFmt::F64, 0), 0x3FF0_0000_0000_0000);
        // Negative-side signed thresholds: smallest float ≥ 2^k + 1.
        assert_eq!(min_pattern_ge_pow2_plus_1(FpFmt::F32, 31), 0x4F00_0001);
        assert_eq!(min_pattern_ge_pow2_plus_1(FpFmt::F32, 63), 0x5F00_0001);
        assert_eq!(
            min_pattern_ge_pow2_plus_1(FpFmt::F64, 31),
            0x41E0_0000_0020_0000
        );
        assert_eq!(
            min_pattern_ge_pow2_plus_1(FpFmt::F64, 63),
            0x43E0_0000_0000_0001
        );
        // One-ULP semantics of each: value at the threshold is ≥ 2^k + 1,
        // one ULP below is < 2^k + 1.
        for (fmt, k, thresh) in [
            (FpFmt::F32, 31u32, 0x4F00_0001u128),
            (FpFmt::F32, 63, 0x5F00_0001),
            (FpFmt::F64, 31, 0x41E0_0000_0020_0000),
            (FpFmt::F64, 63, 0x43E0_0000_0000_0001),
        ] {
            if k <= 52 {
                // 2^k + 1 is an exact f64; floats near 2^k may be fractional
                // (f64 spacing < 1 there) but every one is f64-exact.
                let bound = 2f64.powi(k as i32) + 1.0;
                assert!(fval(fmt, thresh) >= bound, "{fmt:?} 2^{k}+1 at threshold");
                assert!(fval(fmt, thresh - 1) < bound, "{fmt:?} 2^{k}+1 one below");
            } else {
                // 2^63 + 1 is NOT an f64 (needs 64 significand bits) — but
                // every float near 2^63 is an integer (spacing ≥ 2048), so
                // compare exactly in u128.
                let bound = (1u128 << k) + 1;
                assert!(
                    fval(fmt, thresh) as u128 >= bound,
                    "{fmt:?} 2^{k}+1 at threshold"
                );
                assert!(
                    (fval(fmt, thresh - 1) as u128) < bound,
                    "{fmt:?} 2^{k}+1 one below"
                );
            }
        }
    }

    /// `fp_is_nan` / `fp_is_inf` ⇔ the host float's `is_nan` / `is_infinite`,
    /// over every exponent value × structured mantissa samples × both signs.
    #[test]
    fn nan_inf_classifiers_match_ieee_reference() {
        for fmt in [FpFmt::F32, FpFmt::F64] {
            let f = v("f", fmt.total_bits());
            let nan_t = fp_is_nan(&f, fmt);
            let inf_t = fp_is_inf(&f, fmt);
            let mut env = Env::new();
            for p in structured_patterns(fmt) {
                env.insert("f".into(), p);
                let x = fval(fmt, p);
                assert_eq!(
                    eval::eval_bool(&nan_t, &env).unwrap(),
                    x.is_nan(),
                    "is_nan {fmt:?} pattern {p:#x}"
                );
                assert_eq!(
                    eval::eval_bool(&inf_t, &env).unwrap(),
                    x.is_infinite(),
                    "is_inf {fmt:?} pattern {p:#x}"
                );
            }
        }
    }

    /// Structured pattern sweep for a format: every exponent value × mantissa
    /// samples (0..=3, top three, thirds, and every single-bit mantissa) ×
    /// both signs. Covers all exponent boundaries and every mantissa bit
    /// position — 15,872 patterns for f32 (256 × 31 × 2), 245,760 for f64
    /// (2048 × 60 × 2).
    fn structured_patterns(fmt: FpFmt) -> Vec<u128> {
        let m = fmt.mant_bits();
        let mant_max = (1u128 << m) - 1;
        let mut mants = vec![
            0,
            1,
            2,
            3,
            mant_max,
            mant_max - 1,
            mant_max - 2,
            mant_max / 3,
            mant_max / 2,
            2 * (mant_max / 3),
        ];
        for i in 2..m {
            mants.push(1u128 << i);
        }
        let mut out = Vec::new();
        for exp in 0..=fmt.exp_all_ones() {
            for &mant in &mants {
                for sign in [0u128, 1] {
                    out.push((sign << (fmt.total_bits() - 1)) | (exp << m) | mant);
                }
            }
        }
        out
    }

    /// One trunc variant, proven two ways against the real-float reference:
    /// the structured sweep of [`structured_patterns`], plus a ±64-ULP
    /// magnitude sweep (both signs) around BOTH derived threshold patterns —
    /// i.e. the ±2^31 / ±2^32 / ±2^63 / ±2^64 / ±1.0 neighborhoods at ULP
    /// granularity.
    fn sweep_trunc_variant(fmt: FpFmt, target: IntTarget, signed: bool) {
        let f = v("f", fmt.total_bits());
        let oor_t = fp_trunc_out_of_range(&f, fmt, target, signed);
        let trap_t = trap_trunc(&f, fmt, target, signed);
        let mut env = Env::new();
        let mut check = |p: u128| {
            env.insert("f".into(), p);
            let x = fval(fmt, p);
            assert_eq!(
                eval::eval_bool(&oor_t, &env).unwrap(),
                x.is_finite() && ref_out_of_range(x, target, signed),
                "out_of_range {fmt:?}->{target:?} signed={signed} pattern {p:#x} value {x:e}"
            );
            assert_eq!(
                eval::eval_bool(&trap_t, &env).unwrap(),
                ref_trap_trunc(x, target, signed),
                "trap_trunc {fmt:?}->{target:?} signed={signed} pattern {p:#x} value {x:e}"
            );
        };
        for p in structured_patterns(fmt) {
            check(p);
        }
        let k = target.width() - u32::from(signed);
        let pos_thresh = pow2_magnitude_pattern(fmt, k);
        let neg_thresh = if signed {
            min_pattern_ge_pow2_plus_1(fmt, target.width() - 1)
        } else {
            pow2_magnitude_pattern(fmt, 0)
        };
        for thresh in [pos_thresh, neg_thresh] {
            for mag in (thresh - 64)..=(thresh + 64) {
                for sign in [0u128, 1] {
                    check((sign << (fmt.total_bits() - 1)) | mag);
                }
            }
        }
    }

    #[test]
    fn trunc_f32_to_i32_signed_matches_reference() {
        sweep_trunc_variant(FpFmt::F32, IntTarget::I32, true);
    }
    #[test]
    fn trunc_f32_to_i32_unsigned_matches_reference() {
        sweep_trunc_variant(FpFmt::F32, IntTarget::I32, false);
    }
    #[test]
    fn trunc_f32_to_i64_signed_matches_reference() {
        sweep_trunc_variant(FpFmt::F32, IntTarget::I64, true);
    }
    #[test]
    fn trunc_f32_to_i64_unsigned_matches_reference() {
        sweep_trunc_variant(FpFmt::F32, IntTarget::I64, false);
    }
    #[test]
    fn trunc_f64_to_i32_signed_matches_reference() {
        sweep_trunc_variant(FpFmt::F64, IntTarget::I32, true);
    }
    #[test]
    fn trunc_f64_to_i32_unsigned_matches_reference() {
        sweep_trunc_variant(FpFmt::F64, IntTarget::I32, false);
    }
    #[test]
    fn trunc_f64_to_i64_signed_matches_reference() {
        sweep_trunc_variant(FpFmt::F64, IntTarget::I64, true);
    }
    #[test]
    fn trunc_f64_to_i64_unsigned_matches_reference() {
        sweep_trunc_variant(FpFmt::F64, IntTarget::I64, false);
    }

    /// The synth #709 boundary cases, spelled out one by one.
    #[test]
    fn trunc_boundary_cases_synth_709() {
        #[track_caller]
        fn t(fmt: FpFmt, target: IntTarget, signed: bool, p: u128, want: bool, label: &str) {
            let f = v("f", fmt.total_bits());
            let term = trap_trunc(&f, fmt, target, signed);
            let mut e = Env::new();
            e.insert("f".into(), p);
            assert_eq!(eval::eval_bool(&term, &e).unwrap(), want, "{label}");
        }
        let b32 = |x: f32| x.to_bits() as u128;
        let b64 = |x: f64| x.to_bits() as u128;
        use FpFmt::{F32, F64};
        use IntTarget::{I32, I64};

        // --- i32.trunc_f32_s ---
        t(
            F32,
            I32,
            true,
            b32(2f32.powi(31)),
            true,
            "f32→i32_s: 2^31 traps",
        );
        #[allow(clippy::approx_constant)]
        {
            // (2^31 - 1) is not an f32; the literal rounds UP to 2^31 — traps.
            assert_eq!((2_147_483_647f32).to_bits(), 0x4F00_0000);
        }
        t(
            F32,
            I32,
            true,
            b32(-(2f32.powi(31))),
            false,
            "f32→i32_s: -2^31 is in range",
        );
        t(
            F32,
            I32,
            true,
            b32(2_147_483_520.0), // 2^31 - 128: largest f32 below 2^31
            false,
            "f32→i32_s: largest f32 below 2^31 converts",
        );
        t(
            F32,
            I32,
            true,
            0xCF00_0001, // -(2^31 + 256): next f32 below -2^31
            true,
            "f32→i32_s: -(2^31+256) traps",
        );
        t(F32, I32, true, b32(f32::NAN), true, "f32→i32_s: NaN traps");
        t(
            F32,
            I32,
            true,
            b32(f32::INFINITY),
            true,
            "f32→i32_s: +∞ traps",
        );
        t(
            F32,
            I32,
            true,
            b32(f32::NEG_INFINITY),
            true,
            "f32→i32_s: -∞ traps",
        );
        t(F32, I32, true, b32(0.5), false, "f32→i32_s: 0.5 → 0");
        t(F32, I32, true, b32(-0.5), false, "f32→i32_s: -0.5 → 0");

        // --- i32.trunc_f32_u ---
        t(F32, I32, false, b32(-1.0), true, "f32→i32_u: -1.0 traps");
        t(F32, I32, false, b32(0.5), false, "f32→i32_u: 0.5 → 0");
        t(F32, I32, false, b32(-0.5), false, "f32→i32_u: -0.5 → 0");
        t(F32, I32, false, b32(-0.0), false, "f32→i32_u: -0.0 → 0");
        t(
            F32,
            I32,
            false,
            b32(f32::from_bits(0xBF7F_FFFF)), // -(1 - 2^-24): just above -1
            false,
            "f32→i32_u: -(1-ε) → 0",
        );
        t(
            F32,
            I32,
            false,
            b32(2f32.powi(32)),
            true,
            "f32→i32_u: 2^32 traps",
        );
        t(
            F32,
            I32,
            false,
            b32(4_294_967_040.0), // 2^32 - 256: largest f32 below 2^32
            false,
            "f32→i32_u: largest f32 below 2^32 converts",
        );
        t(F32, I32, false, b32(f32::NAN), true, "f32→i32_u: NaN traps");

        // --- i32.trunc_f64_s ---
        t(
            F64,
            I32,
            true,
            b64(2f64.powi(31)),
            true,
            "f64→i32_s: 2^31 traps",
        );
        t(
            F64,
            I32,
            true,
            b64(2_147_483_647.5),
            false,
            "f64→i32_s: 2^31-0.5 → 2^31-1",
        );
        t(
            F64,
            I32,
            true,
            b64(-(2f64.powi(31))),
            false,
            "f64→i32_s: -2^31 is in range",
        );
        t(
            F64,
            I32,
            true,
            b64(-2_147_483_648.5),
            false,
            "f64→i32_s: -(2^31+0.5) → -2^31",
        );
        t(
            F64,
            I32,
            true,
            b64(-2_147_483_649.0),
            true,
            "f64→i32_s: -(2^31+1) traps",
        );
        t(F64, I32, true, b64(f64::NAN), true, "f64→i32_s: NaN traps");

        // --- i32.trunc_f64_u ---
        t(F64, I32, false, b64(-1.0), true, "f64→i32_u: -1.0 traps");
        t(
            F64,
            I32,
            false,
            b64(-0.999_999_999),
            false,
            "f64→i32_u: just above -1 → 0",
        );
        t(
            F64,
            I32,
            false,
            b64(2f64.powi(32)),
            true,
            "f64→i32_u: 2^32 traps",
        );
        t(
            F64,
            I32,
            false,
            b64(4_294_967_295.5),
            false,
            "f64→i32_u: 2^32-0.5 → 2^32-1",
        );

        // --- i64.trunc_f32_s ---
        t(
            F32,
            I64,
            true,
            b32(2f32.powi(63)),
            true,
            "f32→i64_s: 2^63 traps",
        );
        t(
            F32,
            I64,
            true,
            b32(f32::from_bits(0x5EFF_FFFF)), // largest f32 below 2^63
            false,
            "f32→i64_s: largest f32 below 2^63 converts",
        );
        t(
            F32,
            I64,
            true,
            b32(-(2f32.powi(63))),
            false,
            "f32→i64_s: -2^63 is in range",
        );
        t(
            F32,
            I64,
            true,
            0xDF00_0001, // next f32 below -2^63
            true,
            "f32→i64_s: below -2^63 traps",
        );

        // --- i64.trunc_f32_u ---
        t(
            F32,
            I64,
            false,
            b32(2f32.powi(64)),
            true,
            "f32→i64_u: 2^64 traps",
        );
        t(
            F32,
            I64,
            false,
            b32(f32::from_bits(0x5F7F_FFFF)), // largest f32 below 2^64
            false,
            "f32→i64_u: largest f32 below 2^64 converts",
        );
        t(F32, I64, false, b32(-1.0), true, "f32→i64_u: -1.0 traps");

        // --- i64.trunc_f64_s ---
        t(
            F64,
            I64,
            true,
            b64(2f64.powi(63)),
            true,
            "f64→i64_s: 2^63 traps",
        );
        t(
            F64,
            I64,
            true,
            0x43DF_FFFF_FFFF_FFFF, // 2^63 - 1024: largest f64 below 2^63
            false,
            "f64→i64_s: largest f64 below 2^63 converts",
        );
        t(
            F64,
            I64,
            true,
            b64(-(2f64.powi(63))),
            false,
            "f64→i64_s: -2^63 is in range",
        );
        t(
            F64,
            I64,
            true,
            0xC3E0_0000_0000_0001, // -(2^63 + 2048): next f64 below -2^63
            true,
            "f64→i64_s: below -2^63 traps",
        );

        // --- i64.trunc_f64_u ---
        t(
            F64,
            I64,
            false,
            b64(2f64.powi(64)),
            true,
            "f64→i64_u: 2^64 traps",
        );
        t(
            F64,
            I64,
            false,
            0x43EF_FFFF_FFFF_FFFF, // 2^64 - 2048: largest f64 below 2^64
            false,
            "f64→i64_u: largest f64 below 2^64 converts",
        );
        t(F64, I64, false, b64(-1.0), true, "f64→i64_u: -1.0 traps");
        t(
            F64,
            I64,
            false,
            0xBFEF_FFFF_FFFF_FFFF, // -(1 - 2^-53): just above -1
            false,
            "f64→i64_u: -(1-ε) → 0",
        );
    }

    /// Exhaustive proof for f32→i32, both signednesses: ALL 2^32 bit patterns
    /// evaluated against the real-float reference. ~8.6e9 term evaluations —
    /// ignored by default; run explicitly in release:
    /// `cargo test -p ordeal --release --lib trap:: -- --ignored`
    #[test]
    #[ignore = "exhaustive 2^32 sweep; run with --release --ignored"]
    fn exhaustive_f32_to_i32_all_bit_patterns() {
        let threads = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(8);
        let chunk = (1u64 << 32).div_ceil(threads as u64);
        std::thread::scope(|s| {
            for tid in 0..threads {
                s.spawn(move || {
                    let f = v("f", 32);
                    let signed_t = trap_trunc(&f, FpFmt::F32, IntTarget::I32, true);
                    let unsigned_t = trap_trunc(&f, FpFmt::F32, IntTarget::I32, false);
                    let mut env = Env::new();
                    let lo = tid as u64 * chunk;
                    let hi = ((tid as u64 + 1) * chunk).min(1u64 << 32);
                    for p in lo..hi {
                        env.insert("f".into(), p as u128);
                        let x = f32::from_bits(p as u32) as f64;
                        assert_eq!(
                            eval::eval_bool(&signed_t, &env).unwrap(),
                            ref_trap_trunc(x, IntTarget::I32, true),
                            "i32.trunc_f32_s pattern {p:#010x}"
                        );
                        assert_eq!(
                            eval::eval_bool(&unsigned_t, &env).unwrap(),
                            ref_trap_trunc(x, IntTarget::I32, false),
                            "i32.trunc_f32_u pattern {p:#010x}"
                        );
                    }
                });
            }
        });
    }

    // ---- VC helpers: preservation proves, trap-drop is caught ----

    #[test]
    fn dropped_trunc_trap_is_caught_and_preserved_lowering_proves() {
        // End-to-end through the certificate-checked solver: `i32.trunc_f32_s`
        // whose lowering DROPS the trap (may_trap = false) must be caught with
        // a counterexample that really traps; the preserving lowering must
        // prove Unsat with a re-checkable certificate. The #709 shape.
        let f = v("f", 32);
        let trap = trap_trunc(&f, FpFmt::F32, IntTarget::I32, true);
        let orig = DefineOrTrap {
            value: f.clone(),
            may_trap: trap.clone(),
        };
        let dropped = DefineOrTrap {
            value: f.clone(),
            may_trap: bool_false(),
        };
        match prove_trap_equivalence(&orig, &dropped) {
            CheckResult::Sat(m) => {
                let p = m
                    .assignments
                    .iter()
                    .find(|(n, _)| n == "f")
                    .map(|(_, x)| *x)
                    .expect("model must assign f");
                let x = f32::from_bits(p as u32) as f64;
                assert!(
                    ref_trap_trunc(x, IntTarget::I32, true),
                    "counterexample {p:#010x} must be a genuinely trapping input"
                );
            }
            other => panic!("dropped trunc trap must be Sat, got {other:?}"),
        }
        let preserved = DefineOrTrap {
            value: f.clone(),
            may_trap: trap,
        };
        match prove_trap_equivalence(&orig, &preserved) {
            CheckResult::Unsat(cert) => cert.recheck().expect("trunc-trap cert re-checks"),
            other => panic!("preserved trunc trap must be Unsat, got {other:?}"),
        }
    }

    #[test]
    fn preserved_div_lowering_proves_unsat() {
        // orig and opt: same trap (÷0) and same value ⇒ trap-equivalent.
        let (a, b) = (v("a", 8), v("b", 8));
        let value = BvTerm::Udiv(Box::new(a.clone()), Box::new(b.clone()));
        let d = |val: BvTerm, t: BoolTerm| DefineOrTrap {
            value: val,
            may_trap: t,
        };
        let orig = d(value.clone(), trap_div(DivOp::DivU, &a, &b, 8));
        let opt = d(value, trap_div(DivOp::DivU, &a, &b, 8));
        match prove_trap_equivalence(&orig, &opt) {
            CheckResult::Unsat(cert) => cert.recheck().expect("trap-equiv cert re-checks"),
            other => panic!("preserved lowering must be Unsat, got {other:?}"),
        }
    }

    #[test]
    fn dropped_trap_is_caught_with_counterexample() {
        // opt drops the ÷0 trap (may_trap = false) but keeps the value: the
        // #633/#666 shape. Must be SAT with divisor 0.
        let (a, b) = (v("a", 8), v("b", 8));
        let value = BvTerm::Udiv(Box::new(a.clone()), Box::new(b.clone()));
        let orig = DefineOrTrap {
            value: value.clone(),
            may_trap: trap_div(DivOp::DivU, &a, &b, 8),
        };
        let opt = DefineOrTrap {
            value,
            may_trap: bool_false(),
        };
        match prove_trap_equivalence(&orig, &opt) {
            CheckResult::Sat(m) => {
                let b_val = m
                    .assignments
                    .iter()
                    .find(|(n, _)| n == "b")
                    .map(|(_, x)| *x);
                assert_eq!(b_val, Some(0), "counterexample must set divisor to 0");
            }
            other => panic!("dropped trap must be Sat, got {other:?}"),
        }
    }

    #[test]
    fn dropped_bounds_check_caught_by_conjunct1_gate() {
        // Memory op: synth gates on conjunct-1 only (no value model). opt drops
        // the OOB trap ⇒ trap-condition-equivalence must be SAT.
        let addr = v("a", 8);
        let bound = v("b", 8);
        let size = c(4, 8);
        let orig_trap = trap_mem_oob(&addr, &size, &bound);
        let opt_trap = bool_false(); // lowering dropped the bounds check
        match prove_trap_condition_equivalence(&orig_trap, &opt_trap) {
            CheckResult::Sat(_) => {}
            other => panic!("dropped bounds check must be Sat, got {other:?}"),
        }
        // Preserved (same trap) proves Unsat.
        match prove_trap_condition_equivalence(&orig_trap, &orig_trap) {
            CheckResult::Unsat(cert) => cert.recheck().expect("re-check"),
            other => panic!("preserved bounds check must be Unsat, got {other:?}"),
        }
    }

    // ---- trap refinement (issue #284, TR-082) ----

    fn model_val(m: &crate::Model, name: &str) -> u128 {
        m.assignments
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, x)| *x)
            .unwrap_or_else(|| panic!("model must assign {name}"))
    }

    /// Spec-side reference for the NaN classes, from the host float's
    /// `is_nan` plus the WASM Core §4.3.3 payload definitions — NOT from the
    /// builders' extracts.
    fn ref_nan_class(fmt: FpFmt, p: u128) -> (bool, bool) {
        let m = fmt.mant_bits();
        let is_nan = fval(fmt, p).is_nan();
        let payload = p & ((1u128 << m) - 1);
        let canonical = is_nan && payload == 1u128 << (m - 1);
        let arithmetic = is_nan && payload >= 1u128 << (m - 1);
        (canonical, arithmetic)
    }

    // rivet: verifies VER-082
    /// `fp_is_canonical_nan` / `fp_is_arithmetic_nan` ⇔ the spec reference,
    /// over the structured sweep of both formats, plus the named patterns.
    #[test]
    fn nan_class_predicates_match_spec_reference() {
        for fmt in [FpFmt::F32, FpFmt::F64] {
            let f = v("f", fmt.total_bits());
            let canon_t = fp_is_canonical_nan(&f, fmt);
            let arith_t = fp_is_arithmetic_nan(&f, fmt);
            let mut env = Env::new();
            for p in structured_patterns(fmt) {
                env.insert("f".into(), p);
                let (canon, arith) = ref_nan_class(fmt, p);
                assert_eq!(eval::eval_bool(&canon_t, &env).unwrap(), canon, "{p:#x}");
                assert_eq!(eval::eval_bool(&arith_t, &env).unwrap(), arith, "{p:#x}");
            }
        }
        let at = |fmt: FpFmt, p: u128| {
            let f = v("f", fmt.total_bits());
            let mut env = Env::new();
            env.insert("f".into(), p);
            (
                eval::eval_bool(&fp_is_canonical_nan(&f, fmt), &env).unwrap(),
                eval::eval_bool(&fp_is_arithmetic_nan(&f, fmt), &env).unwrap(),
            )
        };
        assert_eq!(at(FpFmt::F32, 0x7fc0_0000), (true, true));
        assert_eq!(at(FpFmt::F32, 0xffc0_0000), (true, true));
        assert_eq!(at(FpFmt::F32, 0x7fc0_0001), (false, true));
        assert_eq!(at(FpFmt::F32, 0x7f80_0001), (false, false), "sNaN");
        assert_eq!(at(FpFmt::F32, 0x7f80_0000), (false, false), "+inf");
        assert_eq!(at(FpFmt::F32, 0x3fc0_0000), (false, false), "1.5");
        assert_eq!(at(FpFmt::F64, 0x7ff8_0000_0000_0000), (true, true));
        assert_eq!(at(FpFmt::F64, 0xfff8_0000_0000_0001), (false, true));
        assert_eq!(at(FpFmt::F64, 0x7ff0_0000_0000_0001), (false, false));
    }

    /// Reference for `x ∈ Float { value, F32, Propagating([z]) }`, spelled
    /// from the spec in plain Rust.
    fn ref_member_f32(x: u128, value: u128, z: u128) -> bool {
        let fmt = FpFmt::F32;
        if !fval(fmt, value).is_nan() {
            return x == value;
        }
        let z_ok = !fval(fmt, z).is_nan() || ref_nan_class(fmt, z).0;
        let (canon, arith) = ref_nan_class(fmt, x);
        if z_ok { canon } else { arith }
    }

    // rivet: verifies VER-082
    /// `value_set_member` for every set kind ⇔ its reference, over a cross
    /// product of interesting f32 patterns for the result, the original value
    /// and the operand.
    #[test]
    fn value_set_member_matches_reference() {
        let pats: [u128; 12] = [
            0x0000_0000,
            0x8000_0000,
            0x3f80_0000,
            0x7f80_0000,
            0xff80_0000,
            0x7fc0_0000,
            0xffc0_0000,
            0x7fc0_0001,
            0xffff_ffff,
            0x7f80_0001,
            0x7fbf_ffff,
            0x0000_0001,
        ];
        let (x, val, z) = (v("x", 32), v("val", 32), v("z", 32));
        let fl = |nans: NanSet| ValueSet::Float {
            value: val.clone(),
            fmt: FpFmt::F32,
            nans,
        };
        let exact = value_set_member(&x, &ValueSet::Exact(val.clone()));
        let canon = value_set_member(&x, &fl(NanSet::Canonical));
        let arith = value_set_member(&x, &fl(NanSet::Arithmetic));
        let prop = value_set_member(&x, &fl(NanSet::Propagating(vec![(z.clone(), FpFmt::F32)])));
        let prop0 = value_set_member(&x, &fl(NanSet::Propagating(vec![])));
        for &xp in &pats {
            for &vp in &pats {
                for &zp in &pats {
                    let mut e = Env::new();
                    e.insert("x".into(), xp);
                    e.insert("val".into(), vp);
                    e.insert("z".into(), zp);
                    let ev = |t: &BoolTerm| eval::eval_bool(t, &e).unwrap();
                    let v_nan = fval(FpFmt::F32, vp).is_nan();
                    let (xc, xa) = ref_nan_class(FpFmt::F32, xp);
                    assert_eq!(ev(&exact), xp == vp);
                    assert_eq!(ev(&canon), if v_nan { xc } else { xp == vp });
                    assert_eq!(ev(&arith), if v_nan { xa } else { xp == vp });
                    assert_eq!(
                        ev(&prop),
                        ref_member_f32(xp, vp, zp),
                        "x={xp:#x} v={vp:#x} z={zp:#x}"
                    );
                    // No operands: vacuously all-canonical, so the canonical set.
                    assert_eq!(ev(&prop0), ev(&canon));
                }
            }
        }
    }

    // rivet: verifies VER-082
    /// The builder is the issue's formula: over an 8-bit sweep, the violation
    /// holds iff `orig.trap ≠ opt.trap ∨ (¬orig.trap ∧ opt.value ≠ orig.value)`
    /// computed in Rust, and an `Exact` refinement agrees with trap
    /// equivalence (the `From<DefineOrTrap>` embedding).
    #[test]
    fn refinement_violation_is_the_issue_formula() {
        let (a, b) = (v("a", 8), v("b", 8));
        let orig = DefineOrTrap {
            value: BvTerm::Udiv(bx(a.clone()), bx(b.clone())),
            may_trap: trap_div(DivOp::DivU, &a, &b, 8),
        };
        // opt traps on b == 0 OR a == 1, and computes a >> 1.
        let opt = DefineOrTrap {
            value: BvTerm::Lshr(bx(a.clone()), bx(c(1, 8))),
            may_trap: BoolTerm::Or(
                bb(BoolTerm::Eq(bx(b.clone()), bx(c(0, 8)))),
                bb(BoolTerm::Eq(bx(a.clone()), bx(c(1, 8)))),
            ),
        };
        let viol = trap_refinement_violation(&orig.clone().into(), &opt);
        let equiv = trap_equivalence_vc(&orig, &opt);
        for av in 0u128..256 {
            for bv in 0u128..256 {
                let e = env2(av, bv);
                let ot = bv == 0;
                let pt = bv == 0 || av == 1;
                let want = ot != pt || (!ot && av.checked_div(bv).unwrap() != av >> 1);
                let got = eval::eval_bool(&viol, &e).unwrap();
                assert_eq!(got, want, "a={av} b={bv}");
                assert_eq!(got, !eval::eval_bool(&equiv, &e).unwrap());
            }
        }
    }

    /// loom's guarded division: `if b == 0 { unreachable } ; a /u b` at i32.
    /// The explicit guard traps exactly where the division would.
    fn guarded_div_u32() -> (BvTerm, BvTerm, DefineSetOrTrap) {
        let (a, b) = (v("a", 32), v("b", 32));
        let guard = BoolTerm::Eq(bx(b.clone()), bx(c(0, 32)));
        let orig = DefineOrTrap {
            value: BvTerm::Udiv(bx(a.clone()), bx(b.clone())),
            may_trap: trap_any(&[guard, trap_div(DivOp::DivU, &a, &b, 32)]),
        };
        (a, b, orig.into())
    }

    // rivet: verifies VER-082
    /// Worked loom example, positive: removing the now-redundant `b == 0`
    /// guard in front of `i32.div_u` refines the original. Unsat, and the
    /// certificate re-checks.
    #[test]
    fn loom_redundant_div_guard_removal_refines() {
        let (a, b, orig) = guarded_div_u32();
        let opt = DefineOrTrap {
            value: BvTerm::Udiv(bx(a.clone()), bx(b.clone())),
            may_trap: trap_div(DivOp::DivU, &a, &b, 32),
        };
        match prove_trap_refinement(&orig, &opt) {
            CheckResult::Unsat(cert) => cert.recheck().expect("refinement cert re-checks"),
            other => panic!("guard removal must refine (Unsat), got {other:?}"),
        }
    }

    // rivet: verifies VER-082
    /// Negative control, wrong TRAP behaviour: the optimiser replaces the
    /// guarded division by a "safe" total division `b == 0 ? 0 : a /u b`.
    /// Every non-trapping value is right, but the trap is dropped: Sat, and
    /// the model is the trapping input `b == 0`.
    #[test]
    fn loom_dropped_div_trap_is_not_a_refinement() {
        let (a, b, orig) = guarded_div_u32();
        let b_zero = BoolTerm::Eq(bx(b.clone()), bx(c(0, 32)));
        let opt = DefineOrTrap {
            value: BvTerm::Ite {
                cond: bb(b_zero),
                then_: bx(c(0, 32)),
                else_: bx(BvTerm::Udiv(bx(a.clone()), bx(b.clone()))),
            },
            may_trap: bool_false(),
        };
        match prove_trap_refinement(&orig, &opt) {
            CheckResult::Sat(m) => {
                assert_eq!(model_val(&m, "b"), 0, "the dropped trap is at b == 0")
            }
            other => panic!("dropped trap must be Sat, got {other:?}"),
        }
    }

    // rivet: verifies VER-082
    /// Negative control, wrong VALUE: strength-reducing `x /u 2` to the
    /// arithmetic shift `x >>s 1` (neither traps). Sat, and the model is an
    /// input with the sign bit set, on which the two really differ.
    #[test]
    fn loom_wrong_strength_reduction_is_not_a_refinement() {
        let x = v("x", 32);
        let orig = DefineOrTrap {
            value: BvTerm::Udiv(bx(x.clone()), bx(c(2, 32))),
            may_trap: trap_div(DivOp::DivU, &x, &c(2, 32), 32),
        };
        let bad = DefineOrTrap {
            value: BvTerm::Ashr(bx(x.clone()), bx(c(1, 32))),
            may_trap: bool_false(),
        };
        match prove_trap_refinement(&orig.clone().into(), &bad) {
            CheckResult::Sat(m) => {
                let xv = model_val(&m, "x");
                assert!(
                    xv >> 31 == 1,
                    "counterexample {xv:#x} must have the sign bit set"
                );
                let ashr = ((xv as u32 as i32) >> 1) as u32 as u128;
                assert_ne!(xv / 2, ashr, "the model must be a real difference");
            }
            other => panic!("wrong value must be Sat, got {other:?}"),
        }
        let good = DefineOrTrap {
            value: BvTerm::Lshr(bx(x.clone()), bx(c(1, 32))),
            may_trap: bool_false(),
        };
        match prove_trap_refinement(&orig.into(), &good) {
            CheckResult::Unsat(cert) => cert.recheck().expect("re-checks"),
            other => panic!("x /u 2 → x >>u 1 must refine, got {other:?}"),
        }
    }

    // rivet: verifies VER-082
    /// The NaN set is what makes float constant folding provable: loom folds
    /// `f32.div 0.0 0.0` to the canonical NaN `0x7fc00000`, while its model
    /// of the original produced the negative canonical NaN `0xffc00000` (the
    /// x86 default NaN). Under `nans{0.0, 0.0}` (no NaN operand ⇒ the
    /// canonical NaNs) that is a refinement: Unsat. Control: the same pair
    /// under `Exact` is Sat — equivalence would wrongly reject the fold.
    #[test]
    fn nan_constant_fold_refines_only_under_the_nan_set() {
        let zero = c(0, 32);
        let orig_value = c(0xffc0_0000, 32);
        let opt = DefineOrTrap {
            value: c(0x7fc0_0000, 32),
            may_trap: bool_false(),
        };
        let orig = DefineSetOrTrap {
            values: ValueSet::Float {
                value: orig_value.clone(),
                fmt: FpFmt::F32,
                nans: NanSet::Propagating(vec![(zero.clone(), FpFmt::F32), (zero, FpFmt::F32)]),
            },
            may_trap: bool_false(),
        };
        match prove_trap_refinement(&orig, &opt) {
            CheckResult::Unsat(cert) => cert.recheck().expect("re-checks"),
            other => panic!("NaN fold must refine under nans_N, got {other:?}"),
        }
        let exact = DefineSetOrTrap {
            values: ValueSet::Exact(orig_value),
            may_trap: bool_false(),
        };
        assert!(
            matches!(prove_trap_refinement(&exact, &opt), CheckResult::Sat(_)),
            "under Exact the two NaNs differ"
        );
    }

    /// loom's model of `f32.add x -0.0`: `x` when `x` is not a NaN (exact
    /// for ±0, ±∞ and every finite `x`), and `x` with its quiet bit set when
    /// it is (a member of the arithmetic NaNs).
    fn add_neg_zero_f32(x: &BvTerm) -> BvTerm {
        BvTerm::Ite {
            cond: bb(fp_is_nan(x, FpFmt::F32)),
            then_: bx(BvTerm::Or(bx(x.clone()), bx(c(0x0040_0000, 32)))),
            else_: bx(x.clone()),
        }
    }

    // rivet: verifies VER-082
    /// Negative control at the NaN boundary: `x + -0.0 → x` is NOT a WASM
    /// refinement — for a signalling-NaN `x` the add must return an
    /// arithmetic (quiet) NaN and `x` is not one. Sat, and the model is a
    /// signalling NaN. The quieting rewrite `x | quiet-if-NaN` refines.
    #[test]
    fn add_neg_zero_to_x_is_caught_on_signalling_nan() {
        let x = v("x", 32);
        let orig = DefineSetOrTrap {
            values: ValueSet::Float {
                value: add_neg_zero_f32(&x),
                fmt: FpFmt::F32,
                nans: NanSet::Propagating(vec![
                    (x.clone(), FpFmt::F32),
                    (c(0x8000_0000, 32), FpFmt::F32),
                ]),
            },
            may_trap: bool_false(),
        };
        let to_x = DefineOrTrap {
            value: x.clone(),
            may_trap: bool_false(),
        };
        match prove_trap_refinement(&orig, &to_x) {
            CheckResult::Sat(m) => {
                let p = model_val(&m, "x");
                let (_, arith) = ref_nan_class(FpFmt::F32, p);
                assert!(
                    fval(FpFmt::F32, p).is_nan() && !arith,
                    "counterexample {p:#010x} must be a signalling NaN"
                );
            }
            other => panic!("x + -0.0 → x must be Sat, got {other:?}"),
        }
        let quieted = DefineOrTrap {
            value: add_neg_zero_f32(&x),
            may_trap: bool_false(),
        };
        match prove_trap_refinement(&orig, &quieted) {
            CheckResult::Unsat(cert) => cert.recheck().expect("re-checks"),
            other => panic!("the quieting rewrite must refine, got {other:?}"),
        }
    }

    // ---- the refused constructs through the sliver (docs/consuming-ordeal.md) ----

    use crate::sliver::{ArrayTerm, ExtBoolTerm, ExtBvTerm, ext_of_core};

    fn ext_var(name: &str, w: u32) -> ExtBvTerm {
        ExtBvTerm::Core(v(name, w))
    }

    /// `i32.store8 [q] v ; i32.load8_u [p]` against a 32-bit memory bound,
    /// the load forwarded to `zero_ext(v)` by the optimiser. The load's byte
    /// is named by the core variable `ld`, which the sliver defines as the
    /// `select`: `ld == select(store(mem, q, v), p)`.
    fn store_forward_query(q: BvTerm) -> Vec<ExtBoolTerm> {
        let (p, val, bound) = (v("p", 32), v("val", 8), v("bound", 32));
        let one = c(1, 32);
        let store_trap = trap_mem_oob(&q, &one, &bound);
        let load_trap = trap_mem_oob(&p, &one, &bound);
        let orig = DefineOrTrap {
            value: BvTerm::ZeroExt {
                by: 24,
                arg: bx(v("ld", 8)),
            },
            may_trap: trap_any(&[store_trap.clone(), load_trap.clone()]),
        };
        let opt = DefineOrTrap {
            value: BvTerm::ZeroExt {
                by: 24,
                arg: bx(val.clone()),
            },
            // The store stays; the load is gone, so only its trap is kept as
            // an explicit bounds check.
            may_trap: trap_any(&[store_trap, load_trap]),
        };
        let mem = ArrayTerm::Store {
            array: Box::new(ArrayTerm::Var { name: "mem".into() }),
            index: Box::new(ExtBvTerm::Core(q)),
            value: Box::new(ExtBvTerm::Core(val)),
        };
        vec![
            ext_of_core(&trap_refinement_violation(&orig.into(), &opt)),
            ExtBoolTerm::Eq(
                ext_var("ld", 8),
                ExtBvTerm::Select {
                    array: Box::new(mem),
                    index: Box::new(ExtBvTerm::Core(p)),
                },
            ),
        ]
    }

    // rivet: verifies VER-082
    /// A `select`/`store` obligation mapped to `Solver::from_sliver`: store-
    /// to-load forwarding at the same address refines (Unsat, re-checks);
    /// forwarding a store to `p + 1` into a load from `p` does not (Sat, and
    /// the model really has `ld ≠ val`).
    #[test]
    fn sliver_store_to_load_forwarding_refinement() {
        let same = store_forward_query(v("p", 32));
        match Solver::from_sliver(&same).expect("in the sliver").check() {
            CheckResult::Unsat(cert) => cert.recheck().expect("re-checks"),
            other => panic!("same-address forwarding must refine, got {other:?}"),
        }
        let other_addr = store_forward_query(BvTerm::Add(bx(v("p", 32)), bx(c(1, 32))));
        match Solver::from_sliver(&other_addr)
            .expect("in the sliver")
            .check()
        {
            CheckResult::Sat(m) => assert_ne!(model_val(&m, "ld"), model_val(&m, "val")),
            other => panic!("forwarding from another address must be Sat, got {other:?}"),
        }
    }

    /// `pure_call f(arg) + b` behind a `b == 0` division guard, with the
    /// call's result named `r` and defined by `r == f(arg_orig)`; the
    /// optimiser's call `f(arg_opt)` is `s`.
    fn pure_call_query(arg_orig: BvTerm, arg_opt: BvTerm) -> Vec<ExtBoolTerm> {
        let b = v("b", 32);
        let call = |arg: BvTerm| ExtBvTerm::PureCall {
            name: "f".into(),
            args: vec![ExtBvTerm::Core(arg)],
            sort: Sort::new(32),
        };
        // The value is `r + b`, not `r /u b`: equal values from equal call
        // results is what the test is about, and two 32-bit dividers over
        // distinct variables are a hard equivalence for CDCL (it ran for
        // minutes) that says nothing about the mapping.
        let side = |res: &str| DefineOrTrap {
            value: BvTerm::Add(bx(v(res, 32)), bx(b.clone())),
            may_trap: trap_div(DivOp::DivU, &v(res, 32), &b, 32),
        };
        vec![
            ext_of_core(&trap_refinement_violation(&side("r").into(), &side("s"))),
            ExtBoolTerm::Eq(ext_var("r", 32), call(arg_orig)),
            ExtBoolTerm::Eq(ext_var("s", 32), call(arg_opt)),
        ]
    }

    // rivet: verifies VER-082
    /// A `pure_call` obligation mapped to `Solver::from_sliver`: rewriting the
    /// argument `a | a` to `a` refines by congruence (Unsat, re-checks);
    /// rewriting it to `a + 1` does not (Sat, with the two call results
    /// differing in the model).
    #[test]
    fn sliver_pure_call_argument_rewrite_refinement() {
        let a = v("a", 32);
        let ok = pure_call_query(BvTerm::Or(bx(a.clone()), bx(a.clone())), a.clone());
        match Solver::from_sliver(&ok).expect("in the sliver").check() {
            CheckResult::Unsat(cert) => cert.recheck().expect("re-checks"),
            other => panic!("congruent argument rewrite must refine, got {other:?}"),
        }
        let bad = pure_call_query(a.clone(), BvTerm::Add(bx(a), bx(c(1, 32))));
        match Solver::from_sliver(&bad).expect("in the sliver").check() {
            CheckResult::Sat(m) => assert_ne!(model_val(&m, "r"), model_val(&m, "s")),
            other => panic!("a different call argument must be Sat, got {other:?}"),
        }
    }

    /// The memory a store chain leaves behind, compared through a read at a
    /// FRESH index `k`: since the query is existential, `Unsat` means the two
    /// memories agree at every index (the sliver has no whole-array
    /// equality, so this is how an extensional comparison is asked).
    fn memory_differs_at_k(orig: ArrayTerm, opt: ArrayTerm) -> ExtBoolTerm {
        let read = |m: ArrayTerm| ExtBvTerm::Select {
            array: Box::new(m),
            index: Box::new(ext_var("k", 32)),
        };
        ExtBoolTerm::Ne(read(orig), read(opt))
    }

    fn st(m: ArrayTerm, i: BvTerm, val: BvTerm) -> ArrayTerm {
        ArrayTerm::Store {
            array: Box::new(m),
            index: Box::new(ExtBvTerm::Core(i)),
            value: Box::new(ExtBvTerm::Core(val)),
        }
    }

    // rivet: verifies VER-082
    /// A store's effect beside the refinement VC: `store8 [p] v; store8 [p] v`
    /// → one store (same trap, same memory) refines — the violation OR a
    /// memory difference at a fresh `k` is Unsat. Dropping a store that is
    /// not dead (`store8 [p] v; store8 [q] w` → `store8 [q] w`, the bounds
    /// checks kept) is Sat, at `k == p` with `p ≠ q`.
    #[test]
    fn sliver_store_effect_compared_at_a_fresh_index() {
        let (p, q, val, w, bound) = (
            v("p", 32),
            v("q", 32),
            v("val", 8),
            v("w", 8),
            v("bound", 32),
        );
        let one = c(1, 32);
        let mem = || ArrayTerm::Var { name: "mem".into() };
        let result = DefineOrTrap {
            value: c(0, 32),
            may_trap: trap_any(&[
                trap_mem_oob(&p, &one, &bound),
                trap_mem_oob(&q, &one, &bound),
            ]),
        };
        let query = |orig_mem: ArrayTerm, opt_mem: ArrayTerm| {
            vec![ExtBoolTerm::Or(
                Box::new(ext_of_core(&trap_refinement_violation(
                    &result.clone().into(),
                    &result,
                ))),
                Box::new(memory_differs_at_k(orig_mem, opt_mem)),
            )]
        };
        let twice = st(st(mem(), p.clone(), val.clone()), p.clone(), val.clone());
        let once = st(mem(), p.clone(), val.clone());
        match Solver::from_sliver(&query(twice, once))
            .expect("in the sliver")
            .check()
        {
            CheckResult::Unsat(cert) => cert.recheck().expect("re-checks"),
            other => panic!("the duplicate store is dead, got {other:?}"),
        }
        let both = st(st(mem(), p.clone(), val.clone()), q.clone(), w.clone());
        let only_q = st(mem(), q, w);
        match Solver::from_sliver(&query(both, only_q))
            .expect("in the sliver")
            .check()
        {
            CheckResult::Sat(m) => {
                assert_eq!(
                    model_val(&m, "k"),
                    model_val(&m, "p"),
                    "the lost byte is at p"
                );
                assert_ne!(model_val(&m, "p"), model_val(&m, "q"));
            }
            other => panic!("dropping a live store must be Sat, got {other:?}"),
        }
    }
}
