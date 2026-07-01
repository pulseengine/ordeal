# Changelog

All notable changes to this project are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

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
