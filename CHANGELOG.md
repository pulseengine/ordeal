# Changelog

All notable changes to this project are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

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

[Unreleased]: https://github.com/pulseengine/ordeal/commits/main
