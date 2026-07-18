//! Consumer recipes for `Solver::prove_valid` / `Solver::prove_equiv` (issue
//! #66, FEAT-010 / TR-024).
//!
//! Each recipe is the *reusable shape* a PulseEngine consumer needs, expressed
//! as one certificate-checked call over the closed QF_BV fragment — so the
//! check lives in the toolchain instead of being re-derived per incident. Every
//! `Unsat` here carries an LRAT certificate the trusted `ordeal-lrat` checker
//! validated, re-checkable with `cert.recheck()`.
//!
//! The issue numbers below point at the consumer AREA each shape serves, not
//! a verbatim transcription of one issue's obligation (I checked: several of
//! #66's references are loose pointers). The exception is the meld guard,
//! which is the precise `base + N` fold from the root-caused, now-fixed
//! meld#338. Two of these are **regression guards** built from *real,
//! already-fixed* miscompiles — they are the checks that would have caught the bug, not claims
//! of a live catch. That distinction is deliberate: an honest guard says "this
//! stays fixed", not "I found this".
//!
//! Run with: `cargo run -p ordeal --example consumer_recipes`

use ordeal::{BoolTerm, BvTerm, CheckResult, Solver, Sort};

fn v(name: &str, w: u32) -> BvTerm {
    BvTerm::Var {
        name: name.into(),
        sort: Sort::new(w),
    }
}
fn k(val: u128, w: u32) -> BvTerm {
    BvTerm::Const {
        value: val,
        sort: Sort::new(w),
    }
}
fn eq(a: BvTerm, b: BvTerm) -> BoolTerm {
    BoolTerm::Eq(Box::new(a), Box::new(b))
}

/// Print a recipe's verdict, asserting it matches what a sound consumer expects.
/// `want_valid = true`  → expect UNSAT (the property holds; cert re-checks).
/// `want_valid = false` → expect SAT   (a counterexample exists; the guard fires).
fn report(name: &str, goal: BoolTerm, want_valid: bool) {
    match (Solver::prove_valid(goal), want_valid) {
        (CheckResult::Unsat(cert), true) => {
            cert.recheck().expect("certificate must re-check");
            println!(
                "  [valid]   {name}  ({} bytes of checked LRAT)",
                cert.lrat.len()
            );
        }
        (CheckResult::Sat(model), false) => {
            let witness: Vec<String> = model
                .assignments
                .iter()
                .map(|(n, val)| format!("{n}={val:#x}"))
                .collect();
            println!("  [refuted] {name}  counterexample: {}", witness.join(", "));
        }
        (got, _) => panic!("{name}: unexpected verdict {got:?}"),
    }
}

fn main() {
    println!("relay — codec round-trip (relay codec area):");
    // A byte-swap round-trip on a 16-bit field: swap(swap(x)) == x. Valid.
    {
        let x = v("x", 16);
        let lo = BvTerm::Extract {
            hi: 7,
            lo: 0,
            arg: Box::new(x.clone()),
        };
        let hi = BvTerm::Extract {
            hi: 15,
            lo: 8,
            arg: Box::new(x.clone()),
        };
        let swapped = BvTerm::Concat(Box::new(lo), Box::new(hi));
        // swap it again
        let lo2 = BvTerm::Extract {
            hi: 7,
            lo: 0,
            arg: Box::new(swapped.clone()),
        };
        let hi2 = BvTerm::Extract {
            hi: 15,
            lo: 8,
            arg: Box::new(swapped),
        };
        let twice = BvTerm::Concat(Box::new(lo2), Box::new(hi2));
        report("byteswap∘byteswap == id", eq(twice, x), true);
    }

    println!("spar — AADL↔WIT↔ABI byte-layout equivalence (spar layout area):");
    // Extracting the low field of a packed record recovers it. Valid.
    {
        let flags = v("flags", 8);
        let hi = v("hi", 32);
        let packed = BvTerm::Concat(Box::new(hi), Box::new(flags.clone()));
        let low8 = BvTerm::Extract {
            hi: 7,
            lo: 0,
            arg: Box::new(packed),
        };
        report(
            "extract_low(pack(hi, flags)) == flags",
            eq(low8, flags),
            true,
        );
    }

    println!("sigil — 64-bit varint overflow rejection (sigil parser area):");
    // A LEB128 continuation past 64 bits must be rejected. The guard: a 10th
    // group's payload bits that exceed bit 63 cannot be zero for a value that
    // set them — i.e. `x != 0 -> (x << 63) may lose bits`. Shown as: shifting a
    // set high bit out is NOT the identity, so a naive fold is refuted.
    {
        let x = v("x", 64);
        let shifted = BvTerm::Shl(Box::new(x.clone()), Box::new(k(63, 64)));
        // A sound decoder must NOT treat (x << 63) == x as an identity.
        report("(x << 63) == x is NOT an identity", eq(shifted, x), false);
    }

    println!("scry-bits — abstraction transfer soundness at 32 (scry transfer area, DO-333):");
    // Zero-extending an 8-bit abstract input to 32 bits and truncating back is
    // the identity — the abstraction transfer loses nothing. Valid.
    {
        let a = v("a", 8);
        let widened = BvTerm::ZeroExt {
            by: 24,
            arg: Box::new(a.clone()),
        };
        let narrowed = BvTerm::Extract {
            hi: 7,
            lo: 0,
            arg: Box::new(widened),
        };
        report("trunc8(zext32(a)) == a", eq(narrowed, a), true);
    }

    println!("meld — offset-fold REGRESSION GUARD (meld#338, fixed 2026-07-15):");
    // meld's `fuse` truncated a `global.get`-first extended-const expr, folding
    // `base + N` down to `base` and corrupting PIE data/element offsets. The
    // fold is unsound: base + 16 == base is refutable (base = anything).
    {
        let base = v("base", 32);
        let folded = eq(
            BvTerm::Add(Box::new(base.clone()), Box::new(k(16, 32))),
            base,
        );
        report("base + 16 == base (the bad fold)", folded, false);
    }

    println!("\nAll recipes behaved as expected; every [valid] carries a re-checked certificate.");
}
