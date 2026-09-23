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
  enough to formally verify — and it is verified: its soundness theorem is
  discharged in Lean 4, sorry-free and CI-gated (see below).

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

The Lean side builds with `elan` + `lake` (the required *Lean model +
soundness proof* CI job regenerates the Aeneas models from the Rust sources
before every proof build — see `docs/formal-verification.md`). `rules_lean`
exists only as a commented placeholder in `MODULE.bazel` and has never been
part of the build.

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

The full pipeline is shipped: every stage above is implemented and the
closed fragment is decided end-to-end, each op having gained a proven
bit-blasting rule before it was enabled (the op-enablement gate in
`solver.rs`). `Solver::check` still returns `Unknown` when it cannot stand
behind an answer — which is sound because callers must treat `Unknown`
conservatively (never optimize on it).

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

The **default build carries no external backend** — it is
zero-external-deps and wasip2-clean. The split is expressed in
`crates/ordeal/Cargo.toml`: the pure-Rust CDCL core lives in-tree
(`src/sat.rs`, no dependency line at all), while the only optional extras
are native-scoped and off by default — `cadical-sys` behind the `cadical`
accelerator feature and `z3` behind the `oracle` feature, both under
`[target.'cfg(not(target_family = "wasm"))'.dependencies]`.

## The wasm32-wasip2 target

`wasm32-wasip2` is a **first-class build target**, CI-gated and required:
loom compiles *itself* to a WebAssembly component and embeds ordeal to verify
its own optimizations in-process. If ordeal could not build as a wasip2
component, loom could not self-verify in that mode.

Two consequences drive the design:

1. **No FFI on the wasm path.** Our own pure-Rust core is the engine on every
   target, so the wasm path needs no C toolchain and no FFI; CaDiCaL (the
   optional native accelerator) is simply `cfg`-gated out.
2. **The default build stays wasip2-clean and zero-dep.** The in-tree CDCL
   core is the backend, so the default build declares no external
   dependencies; the enforced CI gate is
   `cargo build --target wasm32-wasip2 --release`.

The Component Model packaging is produced by the org's `rules_wasm_component`
Bazel rules (see the build section below); the plain buildability guarantee is
the cargo command above.

## The array / UF sliver

loom emits two things that pure bit-blasting cannot express:

- **Non-extensional arrays** `Array(BV32 → BV8)` with `select` / `store`
  (modeling linear memory). Requires read-over-write reasoning, handled by
  a preprocessing pass that eliminates the accesses rather than blasting an
  unbounded array.
- **Uninterpreted `pure_call`** with **congruence** (same arguments ⇒ same
  result). Requires congruence closure layered over the boolean core.

Both are **implemented** in `crates/ordeal/src/sliver.rs`
(`Solver::check_sliver`) as a separate `Ext*` term layer that is
preprocessed away — eager read-over-write elimination (including
**symbolic** BV32 indices, a sound reduction into the closed fragment) and
Ackermannization — into plain `BoolTerm` assertions before bit-blasting.
The core `term.rs` fragment stays closed: no array/UF op ever reaches the
AIG, so the "every op has a proven bit-blasting rule" invariant is preserved
by construction.

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
dependencies. Phase P4 (shipped) removed Z3 from the soundness argument
entirely — the verified checker stands alone.

## Crate layout

One workspace, **two crates** — the untrusted solver and, separately, the
trusted checker. The separation *is* the trust boundary: `ordeal-lrat`
declares no dependencies at all (enforced by test) and never depends on the
solver.

| Path | Purpose |
|------|---------|
| `crates/ordeal-lrat/` | **THE TRUSTED COMPONENT** — the dependency-free LRAT checker (`kernel.rs` is the string-free proven core; soundness discharged in Lean 4). |
| `crates/ordeal/src/term.rs` | The closed QF_BV fragment (loom #246 op set). |
| `crates/ordeal/src/solver.rs` | One-shot `check-sat` interface; result / certificate / model types. |
| `crates/ordeal/src/blast/` | Bit-blasting rules per op family (`arith`, `bitwise`, `muldiv`, `shift`, `structural`) + the Kani proof harnesses (`proofs.rs`). |
| `crates/ordeal/src/blast_kernel.rs` | The Aeneas-friendly blaster core mirrored into Lean (`BlastKernel.lean`). |
| `crates/ordeal/src/aig.rs` | And-Inverter Graph with structural sharing + const-folding. |
| `crates/ordeal/src/cnf.rs` | Tseitin CNF encoding. |
| `crates/ordeal/src/sat.rs` | The in-tree pure-Rust CDCL core (primary engine, all targets; LRAT trace). |
| `crates/ordeal/src/sat_cadical.rs` | Optional CaDiCaL accelerator (`cadical` feature; never load-bearing). |
| `crates/ordeal/src/lrat.rs` | LRAT proof formatting from the CDCL trace. |
| `crates/ordeal/src/canon.rs` | Semantics-preserving canonicalization pass. |
| `crates/ordeal/src/eval.rs` | Concrete evaluator (model self-check, reference semantics). |
| `crates/ordeal/src/sliver.rs` | The array/UF sliver (symbolic-index read-over-write + Ackermannization). |
| `crates/ordeal/src/trap.rs` | WASM trap conditions as QF_BV predicates; trap-preservation VCs. |
| `crates/ordeal/src/layout.rs` | Little-endian byte split/reassembly for layout-equivalence queries. |
| `crates/ordeal/src/lowering.rs` | Derived-op lowering helpers. |
| `crates/ordeal/src/smtlib.rs` | Minimal SMT-LIB2 QF_BV front end (the `check` subcommand). |
| `crates/ordeal/src/verus.rs` | Verus `by (bit_vector)` obligation extraction (the `verus` subcommand). |
| `crates/ordeal/src/cert_bundle.rs` | `ordeal-cert/v1` bundle serialization (`cert-bundle` feature). |
| `crates/ordeal/src/bmc_corpus.rs` | BMC-shaped benchmark corpus (doc-hidden). |
| `crates/ordeal/src/oracle.rs` | Z3 differential oracle (behind the `oracle` feature). |
| `crates/ordeal/src/lib.rs` | Public API surface and re-exports. |
| `crates/ordeal/src/main.rs` | CLI entry point. |

## Build

Ordeal builds two ways, both from the same cargo workspace:

- **Cargo** — `cargo build` / `cargo test` (native), and
  `cargo build --target wasm32-wasip2 --release` for the component target. This
  is the source of truth and what the CI gates enforce.
- **Bazel** (org convention, mirrors synth) — `rules_rust` builds the crate
  and `rules_wasm_component` packages the wasip2 component. (`rules_lean`
  remains a commented placeholder in `MODULE.bazel`; the Lean proofs build
  with `elan` + `lake` in the required Lean CI job, not with Bazel.)

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
