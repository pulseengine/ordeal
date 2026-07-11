//! Translation validation with an **independently re-checkable** certificate.
//!
//! This mirrors what synth's `synth-verify` translation validator does — prove
//! a WASM operation is semantically equivalent to the ARM instruction sequence
//! a codegen rule lowers it to — but with ordeal's distinguishing property: the
//! `Unsat` (= "equivalent for every input") verdict is a **portable proof
//! object**, not solver faith. The caller re-runs the trusted `ordeal-lrat`
//! checker over the returned certificate and re-establishes the result with
//! zero trust in the (untrusted) solver.
//!
//! Contrast with a bare `z3.check() == Unsat`: that verdict is unchecked — if
//! the solver has a soundness bug, an *incorrect* lowering is silently accepted
//! as "proven equivalent". `cert.recheck()` is the gate that removes that trust.
//!
//! Run with: `cargo run -p ordeal --example translation_validation`

use ordeal::{BvTerm, CheckResult, Solver, Sort};

const W: u32 = 32;

fn var(name: &str) -> BvTerm {
    BvTerm::Var {
        name: name.into(),
        sort: Sort::new(W),
    }
}
fn konst(v: u128) -> BvTerm {
    BvTerm::Const {
        value: v,
        sort: Sort::new(W),
    }
}
fn b(t: BvTerm) -> Box<BvTerm> {
    Box::new(t)
}

/// Validate one lowering: is `wasm` ≡ `arm` for every input? Returns whether
/// the equivalence is *checked* — i.e. proven UNSAT **and** the certificate
/// independently re-validated.
fn validate(rule: &str, wasm: BvTerm, arm: BvTerm) -> bool {
    match Solver::prove_equiv(wasm, arm) {
        CheckResult::Unsat(cert) => {
            // The verdict is only as good as the proof behind it: re-check.
            match cert.recheck() {
                Ok(()) => {
                    println!(
                        "  [PROVEN]  {rule}: equivalent — certificate re-checked \
                         ({} CNF clauses, {} LRAT bytes)",
                        cert.cnf.len(),
                        cert.lrat.len()
                    );
                    true
                }
                Err(e) => {
                    // Would mean an ordeal bug: it returned Unsat with a
                    // certificate that does not validate. The consumer catches
                    // it here rather than trusting the verdict.
                    println!("  [REJECT]  {rule}: certificate failed re-check: {e}");
                    false
                }
            }
        }
        CheckResult::Sat(model) => {
            println!("  [WRONG]   {rule}: NOT equivalent — counterexample {model:?}");
            false
        }
        CheckResult::Unknown => {
            // Conservative: no equivalence claim. A validator must not accept.
            println!("  [UNKNOWN] {rule}: undecided — do not accept the lowering");
            false
        }
    }
}

fn main() {
    println!("Translation validation (WASM op ⇄ ARM lowering), certificate-checked:\n");

    // --- Correct lowerings a synth codegen rule would emit ---
    println!("Correct rules (expect PROVEN):");

    // i32.mul(x, 2)  ⇒  LSL x, #1     (strength reduction)
    assert!(validate(
        "i32.mul(x,2) ⇒ LSL x,#1",
        BvTerm::Mul(b(var("x")), b(konst(2))),
        BvTerm::Shl(b(var("x")), b(konst(1))),
    ));

    // i32.mul(x, 8)  ⇒  LSL x, #3
    assert!(validate(
        "i32.mul(x,8) ⇒ LSL x,#3",
        BvTerm::Mul(b(var("x")), b(konst(8))),
        BvTerm::Shl(b(var("x")), b(konst(3))),
    ));

    // i32.add(i32.mul(x,2), x)  ⇒  ADD (LSL x,#1), x   == x*3
    assert!(validate(
        "3*x via (x<<1)+x",
        BvTerm::Mul(b(var("x")), b(konst(3))),
        BvTerm::Add(b(BvTerm::Shl(b(var("x")), b(konst(1)))), b(var("x"))),
    ));

    // i32.and(x, x) ⇒ MOV x   (idempotence)
    assert!(validate(
        "i32.and(x,x) ⇒ x",
        BvTerm::And(b(var("x")), b(var("x"))),
        var("x"),
    ));

    // --- An INCORRECT lowering: the validator must reject it ---
    println!("\nBuggy rule (expect WRONG + counterexample):");

    // Buggy: claim i32.mul(x,3) ⇒ LSL x,#1  (that is x*2, not x*3)
    let accepted = validate(
        "i32.mul(x,3) ⇒ LSL x,#1  [BUG]",
        BvTerm::Mul(b(var("x")), b(konst(3))),
        BvTerm::Shl(b(var("x")), b(konst(1))),
    );
    assert!(!accepted, "a wrong lowering must never be accepted");

    // --- The distinguishing move: don't just trust the Unsat, re-check it ---
    println!("\nThe trust gap this closes:");
    match Solver::prove_equiv(
        BvTerm::Mul(b(var("x")), b(konst(2))),
        BvTerm::Shl(b(var("x")), b(konst(1))),
    ) {
        CheckResult::Unsat(cert) => {
            // A consumer can run the trusted checker themselves — or hand the
            // (cnf, lrat) pair to any independent LRAT checker. The proof is
            // portable; belief does not depend on ordeal being correct.
            assert!(cert.recheck().is_ok());
            println!("  Unsat carried a proof; ordeal_lrat::check re-validated it independently.");
            println!("  => 'equivalent' is evidence you can reproduce, not a verdict you trust.");
        }
        _ => unreachable!("x*2 ≡ x<<1"),
    }

    println!("\nAll lowerings validated as expected.");
}
