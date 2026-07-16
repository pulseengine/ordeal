//! Semantics-preserving canonicalization above the AIG (issue #35 / TR-009).
//!
//! Untrusted preprocessing that runs once per query, before bit-blasting. It
//! (1) constant-folds all-constant subterms to literals and (2) canonicalizes
//! commutative operands (`add`/`mul`/`and`/`or`/`xor`, `eq`/`ne`) and mirrors
//! the "greater" comparisons to their "less" form, so structurally-different but
//! semantically-equal terms — e.g. `mul(a, b)` and `mul(b, a)` — reduce to the
//! SAME term and thus the same AIG node (via structural hashing). That collapses
//! `Ne(Mul(a,b), Mul(b,a))` to `Ne(t, t)`, which the AIG folds to `false`
//! instead of handing the SAT core two multiplier circuits to prove equal the
//! hard way (synth's A5 cliff: did not finish in 590 s → instant).
//!
//! **Soundness is unaffected — these rewrites are on the UNTRUSTED side.** Every
//! `Unsat` is still validated by the `ordeal-lrat` checker, and every `Sat`
//! model is re-evaluated against the ORIGINAL assertions, so a wrong rewrite can
//! only make the solver slower or `Unknown`, never unsound. Each rule is
//! semantics-preserving under `eval` (the reference); the `canon.rs` tests
//! assert `eval(canonicalize(t)) == eval(t)` over random assignments.

use crate::eval::{self, Env};
use crate::term::{BoolTerm, BvTerm};
use std::cmp::Ordering;

fn bx(t: BvTerm) -> Box<BvTerm> {
    Box::new(t)
}

/// Any deterministic total order works; the canonical `Debug` form is total,
/// stable across runs, and handles every variant (including `Ite`'s `BoolTerm`)
/// uniformly. It runs once per query on small terms, off the solve hot path.
/// Correctness needs only determinism: equal terms compare equal, so the choice
/// of order never affects the verdict, only whether two equal subterms share a
/// node.
fn cmp_bv(a: &BvTerm, b: &BvTerm) -> Ordering {
    format!("{a:?}").cmp(&format!("{b:?}"))
}

/// Fold an all-constant term to a literal. `eval_bv` returns the width-masked
/// value and errors on any free variable, so only fully-constant nodes fold.
fn fold_bv(node: BvTerm) -> BvTerm {
    if matches!(node, BvTerm::Const { .. }) {
        return node;
    }
    match (eval::eval_bv(&node, &Env::new()), eval::bv_sort(&node)) {
        (Ok(value), Ok(sort)) => BvTerm::Const { value, sort },
        _ => node,
    }
}

/// Build a commutative binary node with operands in canonical order.
fn comm(f: fn(Box<BvTerm>, Box<BvTerm>) -> BvTerm, a: BvTerm, b: BvTerm) -> BvTerm {
    if cmp_bv(&a, &b) == Ordering::Greater {
        f(bx(b), bx(a))
    } else {
        f(bx(a), bx(b))
    }
}

/// Canonicalize a bitvector term (bottom-up): canonicalize children, order
/// commutative operands, then constant-fold.
pub fn canonicalize_bv(t: &BvTerm) -> BvTerm {
    use BvTerm::*;
    let node = match t {
        Const { .. } | Var { .. } => t.clone(),
        // Commutative: order operands so a⊕b and b⊕a share a node.
        Add(a, b) => comm(Add, canonicalize_bv(a), canonicalize_bv(b)),
        Mul(a, b) => comm(Mul, canonicalize_bv(a), canonicalize_bv(b)),
        And(a, b) => comm(And, canonicalize_bv(a), canonicalize_bv(b)),
        Or(a, b) => comm(Or, canonicalize_bv(a), canonicalize_bv(b)),
        Xor(a, b) => comm(Xor, canonicalize_bv(a), canonicalize_bv(b)),
        // Non-commutative: canonicalize children, preserve operand order.
        Sub(a, b) => Sub(bx(canonicalize_bv(a)), bx(canonicalize_bv(b))),
        Udiv(a, b) => Udiv(bx(canonicalize_bv(a)), bx(canonicalize_bv(b))),
        Urem(a, b) => Urem(bx(canonicalize_bv(a)), bx(canonicalize_bv(b))),
        Shl(a, b) => Shl(bx(canonicalize_bv(a)), bx(canonicalize_bv(b))),
        Lshr(a, b) => Lshr(bx(canonicalize_bv(a)), bx(canonicalize_bv(b))),
        Ashr(a, b) => Ashr(bx(canonicalize_bv(a)), bx(canonicalize_bv(b))),
        Rotr(a, b) => Rotr(bx(canonicalize_bv(a)), bx(canonicalize_bv(b))),
        Extract { hi, lo, arg } => Extract {
            hi: *hi,
            lo: *lo,
            arg: bx(canonicalize_bv(arg)),
        },
        Concat(a, b) => Concat(bx(canonicalize_bv(a)), bx(canonicalize_bv(b))),
        ZeroExt { by, arg } => ZeroExt {
            by: *by,
            arg: bx(canonicalize_bv(arg)),
        },
        SignExt { by, arg } => SignExt {
            by: *by,
            arg: bx(canonicalize_bv(arg)),
        },
        Ite { cond, then_, else_ } => Ite {
            cond: Box::new(canonicalize_bool(cond)),
            then_: bx(canonicalize_bv(then_)),
            else_: bx(canonicalize_bv(else_)),
        },
    };
    fold_bv(node)
}

/// Build a commutative boolean comparison (`eq`/`ne`) with operands in
/// canonical order.
fn comm_cmp(f: fn(Box<BvTerm>, Box<BvTerm>) -> BoolTerm, a: BvTerm, b: BvTerm) -> BoolTerm {
    if cmp_bv(&a, &b) == Ordering::Greater {
        f(bx(b), bx(a))
    } else {
        f(bx(a), bx(b))
    }
}

/// Canonicalize a boolean term — the entry point the solve pipeline calls on
/// each assertion before blasting.
pub fn canonicalize_bool(t: &BoolTerm) -> BoolTerm {
    use BoolTerm::*;
    let cb = canonicalize_bv;
    match t {
        // Commutative equality/disequality: order operands.
        Eq(a, b) => comm_cmp(Eq, cb(a), cb(b)),
        Ne(a, b) => comm_cmp(Ne, cb(a), cb(b)),
        // Ordered comparisons: canonicalize operands; mirror the "greater"
        // forms to their "less" twins (a > b ≡ b < a, a ≥ b ≡ b ≤ a — same for
        // signed) so mirrored queries share structure.
        Ult(a, b) => Ult(bx(cb(a)), bx(cb(b))),
        Ule(a, b) => Ule(bx(cb(a)), bx(cb(b))),
        Ugt(a, b) => Ult(bx(cb(b)), bx(cb(a))),
        Uge(a, b) => Ule(bx(cb(b)), bx(cb(a))),
        Slt(a, b) => Slt(bx(cb(a)), bx(cb(b))),
        Sle(a, b) => Sle(bx(cb(a)), bx(cb(b))),
        Sgt(a, b) => Slt(bx(cb(b)), bx(cb(a))),
        Sge(a, b) => Sle(bx(cb(b)), bx(cb(a))),
        // Connectives: recurse.
        Not(x) => Not(Box::new(canonicalize_bool(x))),
        And(a, b) => And(
            Box::new(canonicalize_bool(a)),
            Box::new(canonicalize_bool(b)),
        ),
        Or(a, b) => Or(
            Box::new(canonicalize_bool(a)),
            Box::new(canonicalize_bool(b)),
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::Sort;

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

    #[test]
    fn commuted_products_canonicalize_identically() {
        // The A5 crux: mul(a,b) and mul(b,a) must reduce to the SAME term.
        let ab = BvTerm::Mul(Box::new(v("a", 32)), Box::new(v("b", 32)));
        let ba = BvTerm::Mul(Box::new(v("b", 32)), Box::new(v("a", 32)));
        assert_eq!(
            format!("{:?}", canonicalize_bv(&ab)),
            format!("{:?}", canonicalize_bv(&ba)),
            "commutative operands must canonicalize to one form"
        );
    }

    #[test]
    fn constants_fold() {
        // mul(2, 3) over 8 bits folds to the literal 6.
        let folded = canonicalize_bv(&BvTerm::Mul(Box::new(c(2, 8)), Box::new(c(3, 8))));
        assert!(
            matches!(folded, BvTerm::Const { value: 6, .. }),
            "mul(2,3) must fold to Const 6, got {folded:?}"
        );
        // Modular fold: 200 + 100 over 8 bits wraps to 44.
        let wrap = canonicalize_bv(&BvTerm::Add(Box::new(c(200, 8)), Box::new(c(100, 8))));
        assert!(matches!(wrap, BvTerm::Const { value: 44, .. }));
    }

    #[test]
    fn greater_comparisons_mirror_to_less() {
        // a > b canonicalizes to b < a (structurally an Ult with swapped args).
        let gt = BoolTerm::Ugt(Box::new(v("a", 32)), Box::new(v("b", 32)));
        match canonicalize_bool(&gt) {
            BoolTerm::Ult(l, r) => {
                assert_eq!(format!("{l:?}"), format!("{:?}", v("b", 32)));
                assert_eq!(format!("{r:?}"), format!("{:?}", v("a", 32)));
            }
            other => panic!("Ugt must mirror to Ult, got {other:?}"),
        }
    }

    #[test]
    fn canonicalization_preserves_bv_semantics() {
        // The soundness-relevant property: canonicalize(t) evaluates identically
        // to t on every assignment. Exercise a mix of commutative, const, and
        // structural shapes over an exhaustive 4-bit-ish sweep of two vars.
        let terms = [
            BvTerm::Mul(Box::new(v("a", 8)), Box::new(v("b", 8))),
            BvTerm::Add(Box::new(v("a", 8)), Box::new(c(3, 8))),
            BvTerm::Xor(
                Box::new(BvTerm::And(Box::new(v("a", 8)), Box::new(v("b", 8)))),
                Box::new(v("a", 8)),
            ),
            BvTerm::Sub(Box::new(v("b", 8)), Box::new(v("a", 8))),
            BvTerm::Or(Box::new(c(0xF0, 8)), Box::new(v("a", 8))),
        ];
        for t in &terms {
            let ct = canonicalize_bv(t);
            for a in (0u128..256).step_by(17) {
                for b in (0u128..256).step_by(13) {
                    let mut env = Env::new();
                    env.insert("a".into(), a);
                    env.insert("b".into(), b);
                    assert_eq!(
                        eval::eval_bv(t, &env),
                        eval::eval_bv(&ct, &env),
                        "canonicalization changed semantics of {t:?} at a={a},b={b}"
                    );
                }
            }
        }
    }

    #[test]
    fn canonicalization_preserves_bool_semantics() {
        let goals = [
            BoolTerm::Ne(
                Box::new(BvTerm::Mul(Box::new(v("a", 8)), Box::new(v("b", 8)))),
                Box::new(BvTerm::Mul(Box::new(v("b", 8)), Box::new(v("a", 8)))),
            ),
            BoolTerm::Ugt(Box::new(v("a", 8)), Box::new(v("b", 8))),
            BoolTerm::Sge(Box::new(v("a", 8)), Box::new(v("b", 8))),
        ];
        for g in &goals {
            let cg = canonicalize_bool(g);
            for a in (0u128..256).step_by(11) {
                for b in (0u128..256).step_by(7) {
                    let mut env = Env::new();
                    env.insert("a".into(), a);
                    env.insert("b".into(), b);
                    assert_eq!(
                        eval::eval_bool(g, &env),
                        eval::eval_bool(&cg, &env),
                        "canonicalization changed semantics of {g:?} at a={a},b={b}"
                    );
                }
            }
        }
    }
}
