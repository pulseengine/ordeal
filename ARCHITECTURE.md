# Ordeal Architecture

How ordeal decides a QF_BV query — and, more importantly, why you should
believe the answer.

## Table of Contents

1. [Overview](#overview)
2. [The trust boundary](#the-trust-boundary)
3. [The pipeline](#the-pipeline)
4. [SAT backend choice](#sat-backend-choice)
5. [The array / UF sliver](#the-array--uf-sliver)
6. [The differential oracle safety net](#the-differential-oracle-safety-net)
7. [Crate layout](#crate-layout)

## Overview

Ordeal answers one question, one shot at a time: **is this conjunction of
QF_BV assertions satisfiable?** For loom and synth the assertion is almost
always the *negation of an equivalence* (`optimized != original`), so an
**UNSAT** verdict means "the transformation preserves semantics" and a **SAT**
verdict hands back a concrete **counterexample**.

The design constraint that shapes everything below is inherited from the rest
of PulseEngine: **we do not accept an answer we cannot check.** A general SMT
solver asks you to trust its entire (large, fast, evolving) implementation.
Ordeal does not.

## The trust boundary

Ordeal is a **certifying algorithm** (CompCert-style; the concrete blueprint is
Lean 4's `bv_decide`, OOPSLA 2025). The system splits cleanly in two:

```
  ┌───────────────────────────────────────────────┐
  │  UNTRUSTED                                      │
  │  term graph → bit-blast → AIG → CNF → SAT       │  ← big, fast, may have bugs
  │                                    │            │
  │                                    ▼            │
  │                              LRAT certificate   │
  └───────────────────────────────────┬────────────┘
                                       │
  ┌────────────────────────────────────▼───────────┐
  │  TRUSTED (and formally verified)                │
  │  LRAT checker  ──▶  verdict is sound            │  ← small, proven
  └─────────────────────────────────────────────────┘
```

- The **solver is untrusted.** A bug anywhere in bit-blasting, AIG
  construction, CNF encoding, or the SAT search can, at worst, cause ordeal to
  *fail to produce a valid certificate*. It can **never** cause a wrong answer
  to be accepted, because —
- The **checker is the only trusted component.** It replays the LRAT proof
  against the CNF and confirms the empty clause is derivable. It is small
  enough to formally verify, and verifying it is the P2 milestone.

### Verifying the checker: Aeneas → Lean

The checker is written in ordinary Rust and its soundness theorem — *if the
checker accepts a certificate for a CNF, that CNF is UNSAT* — is discharged in
**Lean 4** by translating the Rust to Lean via **[Aeneas](https://github.com/AeneasVerif/aeneas)**
(the "not lots of hand-math" path: Aeneas produces a faithful functional Lean
model of the Rust, and the proof is done against that model rather than a
hand-transcribed one). This is the **chosen** checker path.

The alternative — writing the checker directly in Lean, `bv_decide`-style
(OOPSLA 2025) — remains a documented fallback should the Aeneas translation of
some construct prove awkward. Either way the trusted core is a small Lean-proved
checker with **no build or link dependency on the untrusted solver.**

The Lean side is built with the org's `rules_lean` Bazel rules, reserved (as a
commented placeholder) in `MODULE.bazel` until the checker crate exists.

For a **SAT** verdict the "certificate" is the model itself: ordeal (and its
callers) can independently evaluate the assignment against the assertions to
confirm satisfiability — checking a model is trivial and total.

The soundness argument therefore reduces to: *the LRAT checker is correct.* Not
"Z3 is correct," not "our bit-blaster is correct" — just the small checker.

## The pipeline

```
  BvTerm / BoolTerm        (crates/ordeal/src/term.rs — the closed fragment)
        │
        ▼
  ── bit-blast ──          each width-w bitvector op → w boolean gates
        │
        ▼
     AIG                   And-Inverter Graph: structural sharing, cheap
        │                  simplification (const-fold, strashing)
        ▼
  ── Tseitin CNF ──        AIG → equisatisfiable clause set (linear size)
        │
        ▼
      SAT                  ordeal's own pure-Rust CDCL core (all targets)
                           CaDiCaL = optional native accelerator/benchmark
        │
        ├── SAT  ─▶  decode assignment ─▶  Model (counterexample)
        │
        └── UNSAT ─▶  LRAT proof ─▶  verified checker ─▶  Certificate
```

1. **Term graph.** The query is a DAG of `BvTerm` / `BoolTerm` nodes (see
   `term.rs`). The fragment is closed and small on purpose — every node has one
   well-defined bit-blasting rule.
2. **Bit-blast.** Each `w`-bit operation expands to a fixed boolean-gate
   pattern (ripple-carry adder for `bvadd`, barrel shifter for `bvshl`, etc.).
   Widths are 8/32/64, so the blow-up is bounded and predictable.
3. **AIG.** Gates land in an And-Inverter Graph, which gives structural sharing
   (common subexpressions collapse) and cheap local simplification before we
   ever hit the SAT solver.
4. **Tseitin CNF.** The AIG is converted to an equisatisfiable CNF in linear
   size by introducing one fresh variable per gate.
5. **SAT.** The CNF goes to the SAT backend.
6. **Result.** SAT → decode the satisfying assignment back into a `Model`.
   UNSAT → the solver emits an **LRAT** proof, which the **verified checker**
   validates before we hand back a `Certificate`.

In the phase-0 skeleton none of stages 2–6 exist yet: `Solver::check` returns
`Unknown`, which is sound because callers must treat `Unknown` conservatively
(never optimize on it). The pipeline is filled in op-by-op, each op gaining a
proven bit-blasting rule before it is enabled.

## SAT backend choice

**We own the SAT core.** The primary engine on *every* target — including
`wasm32-wasip2` — is **ordeal's own pure-Rust CDCL solver**. This is a
deliberate full-control decision, not a fallback:

- **ordeal's own pure-Rust CDCL core — primary, all targets.** Because we write
  it, it is FFI-free (so it builds into the wasip2 component with no C
  toolchain), permissively licensed by construction, and emits **LRAT** in the
  exact format our verified checker consumes. The backend survey
  (`docs/research/smt-backend-survey.md`) found **no** off-the-shelf pure-Rust
  core that is simultaneously maintained, permissively licensed, and
  LRAT-emitting — varisat is stale (2019), splr is MPL-licensed and DRAT-only,
  CreuSAT is a verified *solver* (wrong shape for the untrusted-solver /
  verified-checker split). Owning the core is therefore the *only* path that
  satisfies wasip2 **and** certificate-checking together — and it is the moat.
- **CaDiCaL (C++ via FFI) — optional native accelerator / benchmark only.**
  Never load-bearing. It is `cfg`-gated off on wasm, and even on native it is an
  opt-in fast path plus the yardstick we benchmark our own core against. Same
  LRAT format ⇒ the same verified checker validates its output too.
- **varisat — a reference to study, not a dependency.** We mine its native-LRAT
  and proof-trimming implementation for ideas; we do not link it.

The backend is an implementation detail *below* the trust boundary. Whichever
core runs, the LRAT certificate is checked by the same verified checker, so the
choice changes performance, never soundness.

The **default build carries neither backend** — it is zero-external-deps and
wasip2-clean (the P0 skeleton). The split will be expressed in `Cargo.toml`:

```toml
# Our own pure-Rust CDCL core is an in-tree crate on ALL targets (no dep line).
# The only cfg-gated, optional extras are native-only accelerators/oracle:
[target.'cfg(not(target_family = "wasm"))'.dependencies]
# cadical = { version = "...", optional = true }  # optional native accelerator/benchmark
# z3      = { version = "...", optional = true }   # oracle feature only
```

## The wasm32-wasip2 target

`wasm32-wasip2` is a **first-class build target**, CI-gated and required:
loom compiles *itself* to a WebAssembly component and embeds ordeal to verify
its own optimizations in-process. If ordeal could not build as a wasip2
component, loom could not self-verify in that mode.

Two consequences drive the design:

1. **No FFI on the wasm path.** Our own pure-Rust core is the engine on every
   target, so the wasm path needs no C toolchain and no FFI; CaDiCaL (the
   optional native accelerator) is simply `cfg`-gated out.
2. **The default build stays wasip2-clean and zero-dep.** The P0 skeleton has
   no backend at all, which trivially satisfies this; the enforced CI gate is
   `cargo build --target wasm32-wasip2 --release`, kept green as backends land.

The Component Model packaging is produced by the org's `rules_wasm_component`
Bazel rules (see the build section below); the plain buildability guarantee is
the cargo command above.

## The array / UF sliver

loom will eventually emit two things that pure bit-blasting cannot express:

- **Non-extensional arrays** `Array(BV32 → BV8)` with `select` / `store`
  (modeling linear memory). Requires read-over-write reasoning, handled by
  lazy axiom instantiation (or a preprocessing pass that eliminates a bounded
  set of indices) rather than blasting an unbounded array.
- **Uninterpreted `pure_call`** with **congruence** (same arguments ⇒ same
  result). Requires congruence closure layered over the boolean core.

Both sit strictly *above* the bit-blasting core and are represented today only
as a `TODO` comment in `term.rs` — deliberately not implemented, so the closed,
provable fragment stays honest. They are ROADMAP phase P3.

## The differential oracle safety net

Z3 is not in the trusted computing base and is not the engine. It has exactly
two jobs, both non-production, both behind the off-by-default `oracle` feature:

1. **Differential oracle.** In development and CI, a query can be sent to both
   ordeal and Z3; any disagreement is an ordeal bug to chase. This catches
   *incompleteness* (ordeal says `Unknown`/`Sat` where Z3 proves `Unsat`) that
   the LRAT checker — which only guards *soundness* — cannot catch on its own.
2. **Benchmark rival.** We measure ordeal's amortized per-op latency against
   the Z3 integration path (see the README's honesty note: the win is
   integration overhead, not raw SAT speed).

The default build pulls in **no** `z3` dependency and has **zero** external
dependencies. ROADMAP phase P4 removes Z3 from the soundness argument entirely
— by then the verified checker stands alone.

## Crate layout

Single workspace, single crate today; the pipeline stages will become modules
(or crates, if compile times demand it) as they land.

| Path | Purpose |
|------|---------|
| `crates/ordeal/src/term.rs` | The closed QF_BV fragment (loom #246 op set). |
| `crates/ordeal/src/solver.rs` | One-shot `check-sat` interface; result / certificate / model types. |
| `crates/ordeal/src/oracle.rs` | Z3 differential oracle (behind the `oracle` feature). |
| `crates/ordeal/src/lib.rs` | Public API surface and re-exports. |
| `crates/ordeal/src/main.rs` | CLI entry point. |

## Build

Ordeal builds two ways, both from the same cargo workspace:

- **Cargo** — `cargo build` / `cargo test` (native), and
  `cargo build --target wasm32-wasip2 --release` for the component target. This
  is the source of truth and what the CI gates enforce.
- **Bazel** (org convention, mirrors synth) — `rules_rust` builds the crate,
  `rules_wasm_component` packages the wasip2 component, and `rules_lean` is
  reserved for the verified checker:

  | File | Purpose |
  |------|---------|
  | `MODULE.bazel` | Deps: `rules_rust`, `rules_wasm_component` (pinned to the pulseengine fork), commented `rules_lean` placeholder. Crates resolved from `Cargo.lock` via `crate_universe`. |
  | `.bazelrc` | Native + `--config=wasm` (wasm32-wasip2) build configs. |
  | `.bazelversion` | Bazel 7.4.1 (lockstep with synth). |
  | `BUILD.bazel` | Root: exported files + docs filegroup. |
  | `bazel/platforms/BUILD.bazel` | `wasm32_wasip2` platform for `--config=wasm`. |
  | `crates/ordeal/BUILD.bazel` | `rust_library` + `rust_binary` + `rust_test`; commented `rust_wasm_component` (activates once a WIT world exists). |

  The Bazel build is advisory in CI (the module graph fetches the org rules from
  the registry/git); the enforced wasip2 gate is the cargo command above.
