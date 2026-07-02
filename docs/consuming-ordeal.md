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
