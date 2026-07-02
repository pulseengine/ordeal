# Changelog

All notable changes to this project are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Changed

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
