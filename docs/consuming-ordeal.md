# Consuming ordeal (loom / synth trial guide)

ordeal is a certificate-checked QF_BV SMT decision procedure. This is the
guide for trying it as a dependency and reporting back.

## Depend on it

```toml
[dependencies]
ordeal = "0.7.0"
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
    CheckResult::Unsat(cert) => { /* equivalence holds; cert is a portable
                                     proof — cert.recheck() re-validates it */ }
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

### Translation validation (synth): a certificate you can re-check

A WASM→ARM translation validator proves each codegen rule equivalent: assert
the two results *differ*, and `Unsat` means "equal for every input". A bare
`z3.check() == Unsat` verdict is **unchecked** — if the solver has a soundness
bug, an *incorrect* lowering is silently accepted as proven. ordeal returns the
same `Unsat`, but as a **portable proof object**: the certificate carries both
the refuted CNF (`cert.cnf`) and the LRAT proof (`cert.lrat`), so the caller
re-establishes the result with zero trust in the solver.

```rust
use ordeal::{Solver, BvTerm, Sort, CheckResult};

// i32.mul(x, 2)  ⇒  LSL x, #1   (a strength-reduction the backend emits)
let x = || BvTerm::Var { name: "x".into(), sort: Sort::new(32) };
match Solver::prove_equiv(
    BvTerm::Mul(Box::new(x()), Box::new(BvTerm::Const { value: 2, sort: Sort::new(32) })),
    BvTerm::Shl(Box::new(x()), Box::new(BvTerm::Const { value: 1, sort: Sort::new(32) })),
) {
    CheckResult::Unsat(cert) => {
        // Re-run the trusted checker yourself. Ok(()) ⟺ the proof refutes the
        // CNF, so "equivalent" is evidence you reproduced — not solver faith.
        cert.recheck().expect("independent re-check confirms equivalence");
    }
    CheckResult::Sat(model) => { /* NOT equivalent: model is a counterexample */ }
    CheckResult::Unknown    => { /* undecided — do NOT accept the lowering */ }
}
```

`cert.recheck()` runs the formally-verified `ordeal-lrat` checker over
`(cert.cnf, cert.lrat)` — the same validation ordeal did internally, now
reproducible on your side or in a separate audit step. See the runnable
[`translation_validation` example](../crates/ordeal/examples/translation_validation.rs)
(`cargo run -p ordeal --example translation_validation`) for correct rules being
proven and a buggy `i32.mul(x,3) ⇒ LSL x,#1` being caught with a counterexample.

## Parallelize across queries, not inside them

Real workloads are many *independent* queries — synth validates many VCs,
loom checks many rewrite rules, a BMC gate asks one query per unrolling
depth and per property. That independence is where your speedup lives:

- `Solver` is one-shot and self-contained, and every API type (`Solver`,
  `BvTerm`, `BoolTerm`, `CheckResult`, `Certificate`, `Model`) is
  `Send + Sync` — guaranteed by a compile-time assertion in ordeal's test
  suite, so it cannot silently regress. Build one solver per query and fan
  the queries out over your thread pool (e.g. `rayon`'s `par_iter`); there
  is no shared state and no ordering requirement between checks.
- For BMC-style use: race all depths `k = 1..N` and all properties
  concurrently. Any SAT is your counterexample; all-UNSAT clears the depth.
  Measured single-query envelope to plan around (macOS arm64, certified
  end-to-end incl. the checker): a queue-overflow-shaped unrolling crosses
  1 s around k ≈ 90 and sits at ~2.5 s at k = 128; deadlock-shaped
  instances stay under ~275 ms through k = 96 (`benches/bmc.rs`).
- Blast/Tseitin are microseconds; the SAT search is the whole cost on hard
  queries. Parallelizing *inside* one solve is therefore deliberately not
  offered today: a seed portfolio would make certificates run-to-run
  nondeterministic (different proof bytes → different bundle hashes), and
  proof-carrying parallel CDCL is a research problem. If you hit a
  single-query latency wall that the `cadical` accelerator does not clear,
  report it — that measurement is what activates the parked portfolio work.

## The soundness contract (read this)

- **`Unknown` is conservative.** It means "not proven" — the solver could
  not decide, would not stand behind an answer, or the query used a
  construct outside the enabled fragment (e.g. a symbolic array index).
  You MUST NOT apply an optimization / accept a transformation on `Unknown`.
  Keep the original.
- **`Unsat` is the only verdict that authorizes a transformation.** It
  carries a self-contained proof — the refuted CNF (`cert.cnf`) and the LRAT
  refutation (`cert.lrat`) — that the formally-scrutinized `ordeal-lrat`
  checker already validated. Call `cert.recheck()` (or `ordeal_lrat::check(
  &cert.cnf, cert.lrat_text().unwrap())`) to re-validate it independently: your
  trust rests on the proof, not on the solver.
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
