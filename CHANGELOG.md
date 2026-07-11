# Changelog

All notable changes to this project are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.9.1] - 2026-07-11

**Phase B — float→int truncation trap classifier** (TR-020, issue #59). Completes
the trap library: the trap condition for `iN.trunc_fM_s/u` — NaN, ±∞, and
out-of-target-range — expressed as a QF_BV predicate over the **float's bits**,
so a consumer gates trunc trap-preservation with no new solver theory.

### Added — `crates/ordeal/src/trap.rs`
- `FpFmt` (F32/F64), `IntTarget` (I32/I64), and classifiers `fp_is_nan`,
  `fp_is_inf`, `fp_trunc_out_of_range`, and `trap_trunc` — the out-of-range check
  uses the IEEE **monotonic bit-order** (magnitude compares against derived
  `2^k` threshold bit-patterns, with the WASM sign asymmetry: `x == 2^(N-1)`
  traps but `x == -2^(N-1)` converts).

### Boundary (held)
No floating-point in the solver, no new operations — the float enters only as a
`BvTerm` bitvector, classified with `Extract`/`Eq`/`Ne`/`Uge`/`And`/`Or`/`Not`.
FP-value arithmetic equivalence (QF_FP) remains out of the fragment by design.

### Proof
Each classifier is verified by eval-equivalence against the **real Rust float**
WASM trunc trap predicate (range math in exact f64). **f32→i32 (signed and
unsigned) is EXHAUSTIVE** over all 2³² bit patterns; the other six
source×target×signedness variants use a structured exponent×mantissa sweep + a
±64-ULP boundary sweep; every synth#709 boundary case is an explicit assertion.
Independently clean-room-verified (own exhaustive re-run + independent threshold
constants). Consumer: synth trunc gate (#709 regression-lock).

### Falsification
Wrong if `trap_trunc(bits)` disagrees with `iN.trunc_fM_s/u`'s real-float trap
predicate for any bit pattern.

## [0.9.0] - 2026-07-11

**P6 (Phase A) — WASM trap/partiality semantics** (FEAT-007 / TR-019, issue #59).
A shared library that expresses each partial WASM op's **trap condition** as a
QF_BV predicate over its operand bits, so a verifier can prove **trap**-equivalence
— not just value-equivalence — and catch a transformation that *drops a trap*
(the root cause of loom#273/#274/#278 and synth#633/#666/#665/#642). Both
consumers adopt it: loom (loom#279) and synth's `translation_validator`
(VCR-VER-002).

### Added — `crates/ordeal/src/trap.rs`
- **Trap-condition builders** (each a `BoolTerm` over operand bits):
  - `trap_div` — ÷0 (all four div/rem) + `INT_MIN/-1` signed overflow.
  - `trap_always` — `unreachable`.
  - `trap_mem_oob(addr, size, mem_bound)` — OOB with a **caller-supplied symbolic
    `mem_bound`**, wraparound-safe.
  - `trap_call_indirect` — `bounds ∨ null-slot ∨ type`, where the type clause is
    `TypeTrap::Runtime` (runtime `Ne`) or `StaticallyDischarged` (closed-world
    tables, contributes `false`).
  - `trap_any` — Or-fold for block-local composition.
- **`DefineOrTrap`** `(value, may_trap)` wrapper and two VC helpers:
  - `trap_equivalence_vc` / `prove_trap_equivalence` — full
    `(trap ⇔ trap) ∧ (¬trap ⇒ value_eq)`.
  - `trap_condition_equivalence` / `prove_trap_condition_equivalence` — the
    **trap clause alone**, for consumers (synth memory ops) that model no op
    value; still catches a dropped bounds/null check.

### Boundary (held)
ordeal **classifies bits** — it adds **no operations** and does **no
floating-point arithmetic**. Trap-equivalence VCs are decided by the normal
certificate-checked pipeline, so `Unsat` is LRAT-validated and `recheck()`-able.
Phase B (float→int `trunc` classifier, proven against synth's #709 IEEE table)
and FP-value equivalence (QF_FP, out of the QF_BV fragment by design) are
separate.

### Falsification
Wrong if: a `trap_condition` builder ever disagrees with the WASM trap predicate
for some input (`eval` mismatch), or the VC reports a trap-dropping lowering as
`Unsat` (or a trap-preserving one as `Sat`).

## [0.8.0] - 2026-07-11

**P5 (core) — canonicalization + const-folding above the AIG** (FEAT-005 /
TR-018, issue #35). Closes a concrete, measured solver cliff by making
semantically-equal-but-structurally-different terms share an AIG node before
blasting — an untrusted preprocessing pass, so soundness is untouched.

### Added
- `crates/ordeal/src/canon.rs`: a semantics-preserving canonicalization pass
  run on every assertion before bit-blasting. It (1) orders the operands of
  commutative operators (`add`/`mul`/`and`/`or`/`xor`, `eq`/`ne`), (2) mirrors
  the "greater" comparisons to their "less" twins, and (3) constant-folds
  all-constant subterms. So `mul(a,b)` and `mul(b,a)` reduce to the **same**
  term → the same node via structural hashing.
- Kill criterion met: **synth's A5 shape** `Ne(Mul(a,b), Mul(b,a))` @ 32 now
  decides **UNSAT with a re-checkable certificate essentially instantly** (was:
  did not finish in 590 s). It is now decided by root propagation at any conflict
  budget — the v0.4.0 `check_with_limit` stopgap is no longer needed for it.

### Soundness (unchanged)
The rewrites are on the **untrusted side**: every `Unsat` is still validated by
`ordeal-lrat`, and every `Sat` model is re-evaluated against the **original**
assertions. A wrong rewrite could only make the solver slower or `Unknown`,
never unsound. Each rule is proven semantics-preserving under `eval` (the
reference) by `eval(canonicalize(t)) == eval(t)` sweeps in `canon.rs`.

### Deferred (tracked as #57)
LRAT-proof trimming, cross-pass incremental term-graph caching, and a full
criterion benchmark harness vs Z3 — none on the soundness path.

### Falsification
This release is wrong if: canonicalization ever changes a verdict — i.e. for
some query `check` disagrees with the pre-canonicalization pipeline or with the
Z3 differential, or `eval(canonicalize(t)) ≠ eval(t)` for some assignment.

## [0.7.0] - 2026-07-11

**P3 (ordeal side) — portable, independently re-checkable certificate + consumer
integration surface** (FEAT-003 / TR-017). Turns an UNSAT verdict from something
a consumer *trusts ordeal about* into a proof object a consumer *re-checks
itself* — the primitive a certifying translation validator (synth) needs, and
an adoption path for a solver-trusting rule verifier (loom).

### Added
- `Certificate` now carries the refuted DIMACS CNF (`cert.cnf`) alongside the
  LRAT proof (`cert.lrat`), and exposes **`Certificate::recheck()`** — re-runs
  the formally-verified `ordeal-lrat` checker over the `(cnf, lrat)` pair, so a
  consumer re-establishes UNSAT with **zero trust in the untrusted solver**.
  `lrat_text()` and the `CertificateError` type are public and re-exported.
- `crates/ordeal/examples/translation_validation.rs`: a runnable worked example
  mirroring synth's WASM→ARM translation-validation use case — proves correct
  lowerings (each certificate re-checked) and catches a buggy
  `i32.mul(x,3) ⇒ LSL x,#1` with a counterexample.
- `docs/consuming-ordeal.md`: new "Translation validation (synth)" section; the
  soundness contract now documents the actionable `cert.recheck()` path.

### Changed
- The `Certificate` doc's promise — "callers can independently re-check" — is
  now **true through the public API** (previously the CNF was discarded, so
  `ordeal_lrat::check` was uncallable by a consumer). No behavioural change to
  verdicts; the pipeline threads the already-computed CNF out to the caller.

### Falsification
This release is wrong if: a consumer holding an `Unsat(cert)` finds
`cert.recheck()` returns `Ok(())` for a `(cnf, lrat)` pair the standalone
`ordeal-lrat` checker rejects (or vice-versa) — i.e. the in-crate re-check and
an external LRAT checker ever disagree on the carried certificate.

### Scope (honest)
Cross-repo *adoption* is not claimed here and is owned by the consumers:
synth-verify already runs on ordeal with Z3 as a differential oracle
(synth#553); the portable-certificate upgrade is proposed on synth#667; loom
still verifies rules directly with Z3 and is invited to adopt on loom#277.

## [0.6.0] - 2026-07-11

**P4 — Kani proofs of bit-blaster correctness** (FEAT-004). Machine-checked
proofs that each bit-blasting rule equals the concrete reference semantics
(SMT-LIB QF_BV, mirroring `eval::eval_bv`/`eval_bool`) for **all** inputs — the
Z3-independent soundness evidence for the blaster.

### Added
- `crates/ordeal/src/blast/proofs.rs`: **79 Kani harnesses** — every operation
  (`add`/`sub`/`mul`/`udiv`/`and`/`or`/`xor`/`shl`/`lshr`/`ashr`/`rotr`, all 10
  comparisons, `concat`/`extract`/`zext`/`sext`/`ite`) at widths 8/32/64. Each
  asserts `word_value(blast) == r_op(inputs)` over symbolic input bits; Kani
  proves it for every assignment. Validated: every op family verifies
  `SUCCESSFUL` at width 8 (incl. the signed comparisons, sign-extend, extract).
- `.github/workflows/kani.yml`: nightly / on-demand Kani job (non-blocking)
  running the fast tier (every rule at width 8 + the structural rules).

### Changed
- `Aig`'s structural-hash cache is a **no-op under `cfg(kani)`** — the default
  `RandomState` hasher seeds from the OS RNG, which Kani cannot model. The
  un-deduped AIG simulates identically, so the proof covers the deduped
  production AIG. Production build is byte-for-byte unchanged (101 lib tests
  pass).

### Scope (honest)
The light ops (arithmetic, bitwise, shift, rotate, comparison, structural) are
Kani-tractable at 8/32/64. **64-bit `mul`/`udiv` are a compute frontier** — a
bit-blasted 64-bit multiplier is a huge SAT instance — and retain the
exhaustive-width-8 test + the Z3 differential oracle. So this release adds
proof-based soundness for the tractable majority of the op set; fully removing
Z3 awaits a tractable proof strategy for wide multiply/divide.

**Falsification statement:** this release is wrong if any enabled Kani harness
fails, or if a `r_*` reference diverges from `eval::eval_bv`/`eval_bool`.

## [0.5.1] - 2026-07-10

Soundness **drift-hardening**. No runtime code or API change — this release
strengthens the link between the v0.5.0 Lean proof and the shipped Rust.

- **Drift gap closed (verified).** Confirmed with the real Charon+Aeneas toolchain
  that the committed `lean/Kernel.lean` is **byte-identical** to the current Aeneas
  translation of `crates/ordeal-lrat/src/kernel.rs`. So `lrat_check_sound` is
  verified against the *actual shipped code*, not a stale model — closing the one
  residual gap called out in `docs/formal-verification.md`.
- **Model-drift guard operational** (#44). The `kernel-model-drift` CI workflow now
  runs on every PR (required-safe), passes in seconds when the model/kernel/regen
  script are unchanged, and on relevant changes regenerates via a cached
  Charon+Aeneas toolchain and fails on any diff. Advisory pending a warm-cache run
  before promotion to a required branch-protection check.
- Fixed a Rust 1.97 `clippy::unused_format_specs` lint (test-message format width)
  that was failing CI on the new stable toolchain.

**Falsification statement:** this release is wrong if a change to `kernel.rs` can
land on `main` with a stale `lean/Kernel.lean` and a green build once the drift
guard is a required check.

## [0.5.0] - 2026-07-08

The LRAT/RUP **checking algorithm** `kernel::check_steps` is now machine-checked
**sound** in Lean 4: if it accepts a certificate's steps against a CNF, that CNF
is unsatisfiable (`∀ σ, ¬ cnfHolds σ cnf`), proved with **zero `sorry`** over the
**Aeneas-generated** model of the Rust source (`crates/ordeal-lrat/src/kernel.rs`).
This closes issue #12 (TR-013). `#print axioms kernel.spec.lrat_check_sound`
reports **only** `propext` / `Classical.choice` / `Quot.sound` — no `sorryAx`,
no `native_decide` (axiom-clean, like the core `pure_check_sound`).

Scope and trust are stated precisely in
[docs/formal-verification.md](docs/formal-verification.md): the proof is over the
Aeneas translation (Charon+Aeneas trusted), soundness only (not completeness),
under the benign side condition `|cnf| + |steps| ≤ usize::MAX`. Certificate/DIMACS
parsing, I/O, the wasm harness and the (untrusted) solver are out of scope. No
Rust code changed; this release marks the trust-boundary milestone: the solver
stays untrusted, and the now-proven checker is trusted.

**Falsification statement:** this release is wrong if
`kernel.spec.lrat_check_sound` is found to depend on `sorryAx` (or any axiom
beyond `propext` / `Classical.choice` / `Quot.sound`), if `unsat` is not the
standard "no assignment satisfies", or if the committed `lean/Kernel.lean` does
not match `regen.sh`'s output on the shipped `kernel.rs`.

### Added
- `docs/formal-verification.md` — the precise "what is proven / what is trusted"
  trust-boundary statement.
- `kernel-model-drift` CI workflow (advisory) — re-runs `regen.sh` and fails on
  `lean/Kernel.lean` drift from the shipped `kernel.rs` (issue #44).

### Changed
- `ordeal-lrat`'s `check_steps` soundness is now machine-checked (Lean 4 /
  Aeneas); the Lean CI job is blocking and asserts a zero-`sorry` budget.

## [0.4.2] - 2026-07-03

spar's integration question (issue #38): a semantic oracle for its generated
WIT record data-type layouts — small, closed QF_BV equivalence queries, in
ordeal's existing fragment. This adds a one-call equivalence helper and a
worked example; no new fragment op, no optimization/LP surface. **Falsification
statement:** this release is wrong if `Solver::prove_equiv(a, b)` returns a
verdict that disagrees with asserting `BoolTerm::Ne(a, b)` and calling
`Solver::check` on the same terms.

### Added

- **`Solver::prove_equiv(a, b)`** — prove two same-width bitvector terms
  equivalent via the standard equivalence-as-UNSAT encoding. `Unsat` (with a
  checker-validated LRAT certificate) ⟹ equal for all inputs; `Sat` ⟹ a
  counterexample; `Unknown` (including a width mismatch) ⟹ conservative, no
  claim. Decision-only — it does not grow an optimization/LP arm.
- **`docs/consuming-ordeal.md`** — a layout/data-type equivalence section
  (pack+extract round-trip) showing the programmatic `BvTerm` graph + verdict.

## [0.4.1] - 2026-07-03

loom's v0.4.0 smoke-test (issue #34). loom asked for a text front-end so it
can drive ordeal without hand-building `BvTerm`s, and flagged that the README
still described a phase-0 skeleton. This patch ships both. **Falsification
statement:** this release is wrong if `ordeal check` returns a verdict for an
SMT-LIB2 query that disagrees with the equivalent `Solver` API call on the
same query, or if any construct inside the documented QF_BV subset is rejected
as `unsupported`.

### Added

- **SMT-LIB2 front-end — `ordeal check <file.smt2>`** (or `-`/stdin). A small
  hand-written s-expression reader (`ordeal::smtlib`, pure `std`, no new deps)
  over the QF_BV subset loom/synth emit: `declare-const`/`declare-fun`,
  `assert`, `check-sat`, `get-model`/`get-value`. Prints `sat` (+ SMT-LIB
  model), `unsat` (+ checker-validated LRAT byte count), or `unknown`. Every
  op routes through the existing closed core or `ordeal::lowering`; nothing new
  enters the fragment. Any out-of-subset construct → `unsupported: <what>`,
  exit 2. The reader lives in the library (unit-testable, wasip2-clean); the
  binary owns I/O, model formatting, and exit codes.

### Fixed

- **README staleness (loom #34)** — the status line described a "phase-0
  skeleton" returning `Unknown` for every query; corrected to the live v0.4.x
  engine and the new `check` subcommand documented in the quickstart.

## [0.4.0] - 2026-07-03

synth's burn-in asks (issue #29). Their v0.3.0 report — 34 real wasm≡arm
equivalence queries, **0 wrong verdicts, faster than Z3 on 33/34** —
identified the exact gaps blocking adoption behind synth-verify's solver
interface. This release closes asks 1–3. **Falsification statement:** this
release is wrong if `BvTerm::Ite`, any `ordeal::lowering` derived op, or any
`check_with_limit`-decided verdict disagrees with Z3 on the same query, or
if `check_with_limit` ever returns a verdict other than `Unknown` on budget
exhaustion.

### Added

- **`BvTerm::Ite(cond, then, else)`** — the bool→BV bridge (synth used `ite`
  49×). A native op with a proven bit-blasting rule (per-bit AIG mux on the
  condition literal), so it joins the closed fragment legitimately. Verified
  exhaustively at width 8 and across the Z3 differential corpus.
- **`ordeal::lowering`** — blessed derived-op constructors over the closed
  core for the ops synth emits but the fragment omits: `bvnot`, `bvneg`,
  `bvrotl`, `bvurem`, `bvsdiv`, `bvsrem`. No new blast rules (the checker
  still gates every `Unsat`); each form verified against Z3 including
  division-by-zero and `INT_MIN`/`-1` edges.
- **`Solver::check_with_limit(max_conflicts)`** — a resource-bounded check
  returning `Unknown` on budget exhaustion, preserving the conservative
  soundness contract. Makes hard shapes (synth's A5 mul-commutativity,
  previously DNF > 590 s) CI-survivable.

### Notes for consumers

- Depend on `ordeal = "0.4.0"`. `Unknown` stays conservative; only a
  certificate-checked `Unsat` authorizes a transformation.
- synth-verify's full query mix is now expressible with Z3 retained only as
  a differential oracle.

## [0.3.0] - 2026-07-02

The array/UF sliver — loom/synth can now try ordeal on their full query
mix, not just pure QF_BV. **Falsification statement:** this release is
wrong if any in-sliver query (array select/store over concrete offsets, or
uninterpreted `pure_call`) lowered by `Solver::check_sliver` yields a
verdict that disagrees with Z3's array/UF theories on the same query, or a
`Sat` model that does not re-evaluate to true.

### Added

- **`Solver::check_sliver`** — one-shot decision for extended (array/UF)
  queries. The sliver is eliminated into the closed QF_BV core and decided
  by the normal certificate-checked pipeline; out-of-sliver queries return
  `Unknown` (conservative). Soundness is unchanged — no array/UF construct
  reaches the bit-blaster; only the lowered core does.
- **`sliver` module** — the extended term language (`ArrayTerm`,
  `ExtBvTerm`, `ExtBoolTerm`) and `lower()`: eager read-over-write for
  `Array(BV32→BV8)` select/store over concrete offsets, and Ackermannization
  for uninterpreted `pure_call` congruence. Verified against Z3's array and
  UF theories across a 550-query differential corpus (zero disagreements).

### Notes for consumers (loom / synth)

- Depend on `ordeal = "0.3.0"`; `ordeal-lrat` is pulled transitively.
- Requires a Rust toolchain supporting **edition 2024** (rustc ≥ 1.85).
- Treat `Unknown` conservatively (never optimize / accept on it). Only a
  `CheckResult::Unsat` (which carries a checker-validated LRAT certificate)
  authorizes a transformation.
- Please file trials as issues on `pulseengine/ordeal` — see
  `docs/consuming-ordeal.md`.

## [0.2.0] - 2026-07-02

First public release: the QF_BV decision pipeline, oracle-verified and
certificate-checked. **Falsification statement:** this release is wrong if
any well-sorted query over the closed fragment yields a `Sat` model that
does not re-evaluate to true, an `Unsat` whose carried LRAT certificate the
`ordeal-lrat` checker rejects on re-check, or any verdict disagreeing with
Z3 on the same query.

### Added

- Verification evidence layer: `verification-execution` / `verification-verdict`
  artifacts pin each measure's executed result to CI runs (the right side of
  the V is now evidence, not plan). 47 artifacts advanced to `verified`;
  `rivet release status v0.1.0` reports **cuttable**. New CI job
  `Reproducible build` (VER-003): dependency-free assert + bit-identical
  double build. VER-004 (loom/synth call-site conformance) moved to v0.4.0
  and VER-008 (CaDiCaL parity) to v0.6.0 as logged scope decisions.

- **P2 certificate path: `Unsat` is now checker-validated.**
  - `lrat.rs` — LRAT emission from the CDCL proof trace (pure formatting of
    the RUP-ordered antecedent chains; strictly sequential ids in exactly
    the `ordeal-lrat` dialect).
  - `Solver::check` returns `CheckResult::Unsat(Certificate)` **only after
    the `ordeal-lrat` checker accepts the emitted certificate**; a rejected
    certificate degrades to `Unknown`. The certificate bytes carried in
    `Certificate::lrat` are the validated ones, re-checkable by callers.
  - Emission verified on directed UNSAT cases, PHP(4,3), and a random
    UNSAT 3-SAT corpus; mutation cases still rejected.
  - The remaining P2 obligation — the checker's formal soundness proof
    (Rust → Lean 4 via Aeneas, TR-013) — is scaffolded in `lean/README.md`
    and tracked as issue #12; until it discharges, trust rests on the
    small, dependency-free, mutation-tested Rust checker.

- **P1 engine: the full QF_BV decision pipeline** (blast → AIG → Tseitin CNF
  → own pure-Rust CDCL core → self-checked models), oracle-verified:
  - `eval.rs` — total concrete evaluator (executable SMT-LIB semantics), the
    test oracle for every blasting rule and the SAT-model self-check.
  - `aig.rs` — AIGER-convention And-Inverter Graph arena with constant
    folding and structural hashing.
  - `blast/` — per-op-family blasting rules (bitwise/eq, add/sub/comparisons,
    barrel shifts/rotate, mul/restoring-udiv, structural), each verified
    exhaustively at width 8 (65 536 operand pairs) and randomized at 32/64
    against the evaluator.
  - `cnf.rs` — Tseitin encoder (linear size), equisatisfiability-tested.
  - `sat.rs` — dependency-free CDCL (two-watched literals, first-UIP
    learning, VSIDS + phase saving, Luby restarts), deterministic and
    wasm-clean, with a proof trace whose antecedents form RUP chains so P2
    LRAT emission is a formatting step.
  - `solver.rs` — pipeline dispatcher with the op-enablement kill-criterion
    gate; `Sat` models are re-evaluated before being returned; engine-UNSAT
    is reported as `Unknown` until the P2 verified checker lands (no
    unchecked `Unsat`, ever). `Solver::validate` gives distinct
    well-sortedness errors.
  - `ordeal-lrat` — new zero-dependency crate: the RUP-only textual LRAT
    checker (the future sole trusted component), mutation-tested.
  - `oracle.rs` — real Z3 differential oracle (`z3` crate, optional,
    native-only, behind `oracle`): fragment translation, seeded corpus
    generator, and the differential harness. **Milestone: ordeal's raw
    verdicts agree with Z3 across the 300-query corpus (both SAT and UNSAT
    exercised, zero disagreements).**

### Changed

- Rivet release management adopted (requires rivet ≥ 0.23):
  - Phase artifacts renamed `FEAT-P0`…`FEAT-P5` → `FEAT-000`…`FEAT-005` so
    they are valid commit-trailer references (`Implements: FEAT-001`).
  - 33 artifacts scoped to releases via the `release:` field — v0.1.0 = P0
    (skeleton), v0.2.0 = P1, v0.3.0 = P2, v0.4.0 = P3, v0.5.0 = P4,
    v0.6.0 = P5. `rivet release status <version>` is the cuttability
    burn-down.

- Rivet artifact graph reconciled with the architecture decisions:
  - `FEAT-P0`…`FEAT-P5` now mirror ROADMAP.md's phase breakdown one-to-one
    (P0 skeleton, P1 bit-blaster + own SAT core, P2 LRAT + verified checker,
    P3 sliver + integration, P4 drop Z3 from soundness + op-by-op proofs,
    P5 performance); the rivet artifacts are the source of truth and
    ROADMAP.md is the human-readable mirror.
  - `TR-004`, `TR-011`, `ARC-005`, `ARC-008`, `VER-003`, `VER-008`, `VER-013`
    updated from the abandoned "CaDiCaL primary / varisat wasm fallback" plan
    to the decided backend story: ordeal's own pure-Rust CDCL core is primary
    on every target; CaDiCaL is an optional cfg-gated native accelerator;
    varisat is a reference only.
  - `FEAT-P0` marked `implemented` (the phase-0 skeleton is done and CI-gated).
  - Added the schema-authorable inverse links (`allocated-to`) so the
    requirement→architecture allocation is bidirectional.
- ROADMAP.md phase P4 now lists op-by-op bit-blaster verification explicitly.

### Added

- Initial project scaffold (phase-0 skeleton).
  - Cargo workspace with the `ordeal` crate (library + binary).
  - `term.rs`: the closed QF_BV fragment from loom issue #246 — `BvTerm`,
    `BoolTerm`, and `Sort` covering widths 8/32/64. The array/UF sliver is
    present only as a documented `TODO`.
  - `solver.rs`: one-shot `check-sat` interface (`Solver`, `CheckResult`,
    `Certificate`, `Model`). `check` conservatively returns `Unknown` — sound
    by construction — until the bit-blaster + SAT engine + verified LRAT
    checker land.
  - `oracle.rs`: Z3 differential-oracle stub behind the off-by-default `oracle`
    feature. The default build has zero external dependencies.
  - Minimal CLI printing the version and roadmap status notice.
  - Documentation: README, ARCHITECTURE, ROADMAP, AGENTS, CLAUDE.

[Unreleased]: https://github.com/pulseengine/ordeal/compare/v0.4.2...HEAD
[0.4.2]: https://github.com/pulseengine/ordeal/releases/tag/v0.4.2
[0.4.1]: https://github.com/pulseengine/ordeal/releases/tag/v0.4.1
[0.4.0]: https://github.com/pulseengine/ordeal/releases/tag/v0.4.0
[0.3.0]: https://github.com/pulseengine/ordeal/releases/tag/v0.3.0
[0.2.0]: https://github.com/pulseengine/ordeal/releases/tag/v0.2.0
