# Consuming ordeal (loom / synth trial guide)

ordeal is a certificate-checked QF_BV SMT decision procedure. This is the
guide for trying it as a dependency and reporting back.

## Depend on it

```toml
[dependencies]
ordeal = "0.3.0"
```

`ordeal-lrat` (the trusted checker) is pulled transitively. The default
build has **zero external dependencies** and builds on `wasm32-wasip2`.
Requires a Rust toolchain with **edition 2024** support (rustc ≥ 1.85).

## The API

```rust
use ordeal::{Solver, BoolTerm, BvTerm, Sort, CheckResult};

let mut s = Solver::new();
s.assert(/* a BoolTerm: the negation of your equivalence */);
match s.check() {
    CheckResult::Unsat(cert) => { /* equivalence holds; cert.lrat is a
                                     checker-validated LRAT proof */ }
    CheckResult::Sat(model)  => { /* counterexample in model.assignments */ }
    CheckResult::Unknown     => { /* DO NOT optimize — see contract below */ }
}
```

Array/UF (linear memory + `pure_call`) queries use the sliver entry:

```rust
use ordeal::sliver::{ArrayTerm, ExtBvTerm, ExtBoolTerm};
let verdict = Solver::check_sliver(&[/* ExtBoolTerm assertions */]);
```

The fragment is the closed loom #246 op set (widths 8/32/64) plus the sliver
(`Array(BV32→BV8)` select/store over **concrete** offsets, uninterpreted
`pure_call`). Quantifiers, floating-point, optimization, and incremental
push/pop are out of scope by design.

### Layout / data-type equivalence (spar #38)

For "does layout A encode the same bits as layout B?" — e.g. spar checking a
generated WIT record faithfully encodes an AADL `data implementation` — use the
one-call `Solver::prove_equiv` helper. It's the standard equivalence-as-UNSAT
encoding (asserts the terms differ, decides), so `Unsat` = **equivalent**.

```rust
use ordeal::{Solver, BvTerm, Sort, CheckResult};

// A packed record's low field must survive pack+extract: the low 8 bits of
// concat(hi: u32, flags: u8) recover `flags`. Build the term graph directly —
// no SMT-LIB2 text round-trip on machine-generated queries.
let flags = BvTerm::Var { name: "flags".into(), sort: Sort::new(8) };
let hi    = BvTerm::Var { name: "hi".into(),    sort: Sort::new(32) };
let packed = BvTerm::Concat(Box::new(hi), Box::new(flags.clone())); // 40 bits
let low8   = BvTerm::Extract { hi: 7, lo: 0, arg: Box::new(packed) };

match Solver::prove_equiv(low8, flags) {
    CheckResult::Unsat(cert) => { /* layouts are equivalent; cert is checked */ }
    CheckResult::Sat(model)  => { /* NOT equivalent — inputs that differ */ }
    CheckResult::Unknown     => { /* no claim; a width mismatch lands here too */ }
}
```

Model field packing with `Concat` / `Extract{hi,lo}` / `ZeroExt` (offsets and
widths fall out directly); overflow/range checks are `bvult` / `bvule`
assertions; a conditional field selector (`cond ? A : B`) is `BvTerm::Ite`.
`prove_equiv` is decision-only — it does **not** grow an optimization/LP arm
(that problem class stays on HiGHS/good_lp).

## The soundness contract (read this)

- **`Unknown` is conservative.** It means "not proven" — the solver could
  not decide, would not stand behind an answer, or the query used a
  construct outside the enabled fragment (e.g. a symbolic array index).
  You MUST NOT apply an optimization / accept a transformation on `Unknown`.
  Keep the original.
- **`Unsat` is the only verdict that authorizes a transformation.** It
  carries an LRAT certificate that the formally-scrutinized `ordeal-lrat`
  checker already validated; you can independently re-check `cert.lrat` with
  `ordeal_lrat::check`.
- **`Sat` carries a counterexample** already re-evaluated against your
  assertions.

## Reporting trials back

Please file issues on `pulseengine/ordeal` with these labels so they triage
straight into the delivery loop:

- `field-report` — general "we tried it" feedback.
- `missing-capability` — a query shape/op you emit that comes back
  `Unknown` and needs deciding (tell us the exact term).
- `soundness` — any verdict you believe is wrong (attach the query; this is
  top priority).
- `perf` — a latency cliff on your real query mix (attach a measurement).

For `missing-capability` and `soundness`, a minimal reproducing `BoolTerm`
(or SMT-LIB) makes the turnaround fast.
