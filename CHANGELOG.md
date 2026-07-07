# Changelog

All notable changes to this project are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

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
