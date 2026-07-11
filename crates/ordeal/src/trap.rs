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
    fn is_signed(self) -> bool {
        matches!(self, DivOp::DivS | DivOp::RemS)
    }
}

/// Trap condition for a division/remainder op: divide-by-zero for all four,
/// plus `INT_MIN / -1` signed overflow for the signed ops (`div_s`/`rem_s`).
/// Pure compares — `Eq(divisor, 0)` and `And(Eq(dividend, INT_MIN), Eq(divisor, -1))`.
pub fn trap_div(op: DivOp, dividend: &BvTerm, divisor: &BvTerm, width: u32) -> BoolTerm {
    let sort = Sort::new(width);
    let zero = BvTerm::Const { value: 0, sort };
    let div_by_zero = BoolTerm::Eq(bx(divisor.clone()), bx(zero));
    if !op.is_signed() {
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

/// Decide a goal produced by this module by proving it **valid**: assert its
/// negation and run the certificate-checked pipeline. `Unsat(cert)` ⟹ the goal
/// holds for every input (and `cert.recheck()` re-validates it); `Sat(model)` ⟹
/// a counterexample input; `Unknown` ⟹ conservative, do **not** accept.
fn prove_valid(goal: BoolTerm) -> CheckResult {
    let mut s = Solver::new();
    s.assert(BoolTerm::Not(bb(goal)));
    s.check()
}

/// One-call trap-preservation gate over the full VC ([`trap_equivalence_vc`]).
/// `Unsat` ⟹ the lowering preserves traps and values.
pub fn prove_trap_equivalence(orig: &DefineOrTrap, opt: &DefineOrTrap) -> CheckResult {
    prove_valid(trap_equivalence_vc(orig, opt))
}

/// One-call trap-drop gate over conjunct 1 only ([`trap_condition_equivalence`]).
/// `Unsat` ⟹ the lowering neither drops nor spuriously adds a trap (value clause
/// not considered — for consumers without a value model on this op).
pub fn prove_trap_condition_equivalence(
    orig_may_trap: &BoolTerm,
    opt_may_trap: &BoolTerm,
) -> CheckResult {
    prove_valid(trap_condition_equivalence(orig_may_trap, opt_may_trap))
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

    #[test]
    fn trap_div_matches_wasm_semantics() {
        let (a, b) = (v("a", 8), v("b", 8));
        for op in [DivOp::DivU, DivOp::DivS, DivOp::RemU, DivOp::RemS] {
            let cond = trap_div(op, &a, &b, 8);
            for av in 0u128..256 {
                for bv in 0u128..256 {
                    let got = eval::eval_bool(&cond, &env2(av, bv)).unwrap();
                    let zero = bv == 0;
                    let overflow = op.is_signed() && av == 0x80 && bv == 0xFF;
                    assert_eq!(got, zero || overflow, "{op:?} a={av} b={bv}");
                }
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

    // ---- VC helpers: preservation proves, trap-drop is caught ----

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
}
