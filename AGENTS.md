# AGENTS.md — Ordeal Project Instructions

## What This Is

Ordeal (meaning "verdict / judgment") is a specialized, **certificate-checked**
QF_BV SMT solver for the [PulseEngine](https://github.com/pulseengine)
toolchain. It replaces the Z3 static-link build pain in loom (verified WASM
optimizer) and synth (verified WASM→ARM codegen) — grounding: loom issue #246.

Part of PulseEngine: [loom](https://github.com/pulseengine/loom) (optimizer) +
[synth](https://github.com/pulseengine/synth) (codegen) +
[meld](https://github.com/pulseengine/meld) (fuser) + **ordeal** (solver).

## Core Philosophy: Provably Correct — the Solver Is Untrusted

Ordeal's design is the **certifying-algorithm** pattern (CompCert-style;
blueprint = Lean 4 `bv_decide`, OOPSLA 2025):

> The **solver is untrusted**. It emits a machine-checkable **LRAT UNSAT
> certificate**. A small checker whose soundness is **proven in Lean 4**
> (over the Aeneas translation of its Rust source) validates it, and the
> same trusted crate re-derives the CNF from the query the caller built.
> **Only that crate, plus the trusted base named below, is trusted.** A bug
> in the solver can at worst fail to produce a valid certificate — it can
> never make a wrong answer be accepted.

What stays trusted, on every path: the SMT-LIB / Verus front ends, the 1:1
copy of the trees into the kernel's mirror type
(`crates/ordeal/src/mirror.rs`, one `match` arm per constructor), and the
toolchain — Lean's kernel with its three standard axioms, the pinned
Charon/Aeneas translation of the Rust source, and rustc. (That sentence is
single-sourced in `docs/formal-verification.md` and gated by `claims.yaml`;
do not paraphrase it.)

This is not aspirational. It governs every decision:

1. **No unchecked answers.** An `Unsat` verdict is only returned once the
   trusted crate has validated its certificate against the CNF it re-derived
   from the query. A `Sat` verdict is returned only after the trusted crate
   confirmed the model satisfies the query (`check_query_model`,
   `check_tree_model`).
2. **Conservative `Unknown`.** If ordeal cannot decide (or cannot yet blast an
   op), it returns `Unknown`. Callers (loom/synth) MUST treat `Unknown`
   conservatively: **do not optimize, do not accept the transformation.** This
   mirrors loom's "conservative over fast" rule.
3. **The fragment is closed.** `term.rs` defines the *exact* op set. Do not
   widen it silently — a new operation needs a proven bit-blasting rule first.
4. **Z3 is not trusted.** It is a development/CI differential oracle and a
   benchmark rival, behind the off-by-default `oracle` feature. It is not part
   of the soundness argument; phase P4 (shipped) removed it from soundness
   reasoning entirely.
5. **Proof-first.** An operation is added, then its bit-blasting rule is
   justified, then it is enabled. Never the reverse.

Before every change, ask: does this keep the trusted component small and the
answer checkable? If a transformation cannot be checked, ordeal must not accept
it.

## Build Commands

```bash
# Default build — zero external dependencies
cargo build
cargo test

# Enable the Z3 differential oracle (development / CI only)
cargo build --features oracle

# Lint / format
cargo clippy --all-targets -- -D warnings
cargo fmt --check

# Run the CLI on an SMT-LIB2 file (`-` for stdin)
cargo run --bin ordeal -- check query.smt2

# The documentation claim gate (claims.yaml, TR-074) — also a step of the
# required Test job
python3 scripts/claim_check.py
```

## Layout

| Path | Purpose |
|------|---------|
| `crates/ordeal-lrat/` | **The trusted crate** (dependency-free): the LRAT checker, the proven lowering and the query / term / sliver / tree checks, proven in Lean 4 (`lean/`). |
| `crates/ordeal-cert/` | The certificate types, their `recheck()`s and (feature `json`) the `ordeal-cert/v1..v4` bundle codec — no solver dependency; re-exported by `ordeal` at the old paths (TR-075). |
| `crates/ordeal-recheck/` | The standalone `ordeal-recheck` bundle re-checker (native + wasm32-wasip2); its closure is gated solver-free by `scripts/recheck_closure.sh`. |
| `crates/ordeal/src/mirror.rs` | The trusted 1:1 copy of the caller's trees into the kernel's tree type. |
| `crates/ordeal/src/term.rs` | The closed QF_BV fragment (loom #246 op set). |
| `crates/ordeal/src/solver.rs` | One-shot `check-sat`; result / certificate / model types. |
| `crates/ordeal/src/oracle.rs` | Z3 differential oracle (behind `oracle` feature). |
| `crates/ordeal/src/lib.rs` | Public API and re-exports. |
| `crates/ordeal/src/main.rs` | CLI entry point. |

See `ARCHITECTURE.md` for the full pipeline (term → AIG → CNF → SAT → LRAT →
verified checker) and `ROADMAP.md` for phases P0–P5.

## Conventions

- Rust edition 2024 (`Cargo.toml`, workspace-wide).
- Keep the default build dependency-free. New external dependencies must be
  justified and, where they affect soundness, sit *below* the trust boundary
  (the verified checker never depends on an untrusted crate for its guarantee).
- Follow "Keep a Changelog" in `CHANGELOG.md`.

## Commit Traceability

This project uses [Rivet](https://github.com/pulseengine) for SDLC artifact
traceability (`rivet.yaml`). Commits require artifact trailers:

- `Implements` → link type `satisfies`
- `Fixes` → link type `fixes`
- `Verifies` → link type `verifies`
- `Trace` → link type `traces-to`

To skip traceability for a commit, add: `Trace: skip`.

Run `rivet validate` after modifying artifact YAML files.
