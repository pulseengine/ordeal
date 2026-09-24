# Consuming ordeal (loom / synth trial guide)

ordeal is a certificate-checked QF_BV SMT decision procedure. This is the
guide for trying it as a dependency and reporting back.

## Depend on it

```toml
[dependencies]
ordeal = "0.19"
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
(`Array(BV32→BV8)` select/store over concrete **and symbolic** BV32 indices
— symbolic decided since v0.11.0 — plus uninterpreted `pure_call`).
Quantifiers, floating-point, optimization, and incremental push/pop are out
of scope by design.

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
  construct outside the enabled fragment (e.g. a bitvector width other
  than 8/32/64).
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

## SAT verdicts as evidence: the re-checkable witness

Since TR-038, `Solver::check_with_witness()` (no feature gate since #162)
returns `Sat` as a `SatCertificate`: the model **plus** the full CNF
assignment and per-variable bit map. `cert.recheck()` re-establishes the
verdict through the same trusted `ordeal-lrat` crate that validates UNSAT
proofs — every clause checked satisfied, every advertised model binding
checked consistent — so **both** verdict directions are now evidence you
reproduce rather than solver output you trust. `to_cert_v1()` /
`SatCertificate::from_cert_v1()` round-trip it as an `ordeal-cert/v1`
bundle with an optional `witness` block (hash-verified before parsing
returns). A `Sat` whose witness the trusted crate rejects is never
returned — it degrades to `Unknown`, symmetric with the UNSAT gate.

The SAT direction of the trusted crate is machine-checked too (v0.21.0,
TR-044 / VER-039, `lean/SatWitness.lean`, `sorry`-free and CI-gated like
the UNSAT proof): `kernel.spec.check_sat_sound` — an accepted witness
satisfies the *actual* carried CNF; `check_sat_satisfiable` — hence that
CNF is not unsatisfiable; `check_binding_sound` — bit `k` of an advertised
model value *is* the truth value of the CNF literal it is bound to; and
`verdicts_exclusive` — no CNF has both an accepted LRAT refutation and an
accepted witness. All four depend only on Lean's three standard axioms,
pinned in CI; `docs/formal-verification.md` states the trust boundary
exactly.

### At the command line

Since #162 (TR-045) the released binary carries the same witness:
`ordeal check foo.smt2 --format json` on `sat` prints `certificate.clauses`
and a `witness` block — `encoding` (`bitstring-lsb-var1`), the full
`assignment`, the per-variable `bit_map` (`name`, `width`, LSB-first signed
CNF literals) and `assignment_sha256` / `bit_map_sha256` — byte-identical
to the `ordeal-cert/v1` witness the API emits, so rivet's field mapping
(`witness-sha256`, `bit-map-sha256`) applies to CLI output too. Re-check
it exactly as the API's: `ordeal_lrat::check_sat(clauses, assignment)`
and `ordeal_lrat::check_binding(assignment, bits, value)` per model
variable. The hashes are computed in-tree (`ordeal::sha256`, FIPS-tested
and cross-checked against `sha2` in CI) so the default binary stays
dependency-free; they are integrity only — the verdict rests on the
recheck, never on the hash. A `sat` is only printed after the trusted
recheck passed; text mode notes the witness size on stderr.

## Supply chain: SBOM and VEX

From v0.20.0 each GitHub Release carries a CycloneDX SBOM
(`ordeal-<ver>.cdx.json`) and a CycloneDX VEX (`ordeal-<ver>.vex.json`),
both listed in the cosign-signed `SHA256SUMS.txt`. The VEX answers "does
advisory X affect the ordeal I'm running?" for the **shipped closure** —
the crates a release binary is built from. Because ordeal's default build
has no third-party dependencies (CI-asserted), that closure is `ordeal` +
`ordeal-lrat`, and the VEX normally carries no statements at all; it
records the RustSec advisory-db commit and the time it was asserted, so a
reader can tell how fresh the answer is.

A weekly job re-audits the latest release. If the answer changes, a person
classifies the new advisory and a re-issue is published as
`ordeal-<ver>.vex.r<N>.json` with its own cosign bundle (signing identity:
the `vex-reissue.yml` workflow). Take the highest revision present; the
release-time VEX is never overwritten, so the signed sums stay valid.
