# Ordeal Roadmap

**Status:** P2 certificate path landed. The pipeline (bit-blast → AIG →
Tseitin → own pure-Rust CDCL → LRAT) decides the fragment; `Sat` verdicts
carry self-checked counterexample models, and `Unsat` verdicts carry an LRAT
certificate that the `ordeal-lrat` checker validated before the verdict was
returned. The remaining P2 obligation is the checker's formal soundness
proof (Aeneas → Lean 4, issue #12) — until it discharges, trust rests on the
small mutation-tested Rust checker.

Ordeal is built the same way loom and synth are: **step by step, proof
alongside.** No operation is enabled until it has a proven bit-blasting rule,
and no verdict is accepted until the verified checker validates it. When in
doubt we return `Unknown` — which callers must treat conservatively — rather
than guess.

Each phase is tracked in rivet as `FEAT-000`…`FEAT-005`
(`artifacts/features.yaml`) — **the rivet artifacts are the source of truth**.
This document is a human-readable mirror kept in sync by hand for now; the
plan is to generate it from rivet (and eventually retire the handcrafted
copy).

---

## Phase P0 — Skeleton (done)

Establish the closed fragment and a sound-by-construction interface.

| Task | Status |
|------|--------|
| Workspace + crate scaffold, zero-dependency default build | Done |
| `term.rs`: the closed loom #246 QF_BV fragment | Done |
| `solver.rs`: one-shot `check` returning conservative `Unknown` | Done |
| `oracle.rs`: Z3 differential-oracle stub behind `oracle` feature | Done |
| CI: `cargo build` / `cargo test` / `cargo build --features oracle` | Done |
| **`wasm32-wasip2` buildability (zero-dep, wasip2-clean) — CI-gated** | Done |
| Bazel build (`rules_rust` + `rules_wasm_component`; `rules_lean` reserved) | Done |

**Kill criterion / exit:** the crate compiles with and without the `oracle`
feature, and `check` is provably sound (returns only `Unknown`, which never
authorizes a transformation).

---

## Phase P1 — Bit-blaster + SAT (done)

Turn terms into a boolean problem and solve it (answer only, no certificate
yet).

| Task | Status |
|------|--------|
| Bit-blasting rules for every fragment op (widths 8/32/64) | Done — exhaustively oracle-verified at width 8, randomized at 32/64 |
| AIG construction with structural sharing + const-folding | Done |
| Tseitin CNF encoding | Done |
| Our own pure-Rust CDCL core — **primary engine on every target** (incl. `wasm32-wasip2`) | Done — deterministic, RUP-chain proof trace ready for P2 LRAT |
| CaDiCaL FFI — **optional native accelerator/benchmark only**, `cfg`-gated off on wasm | Planned (optional; not needed for P1 exit) |
| SAT → `Model` decoding (counterexamples) | Done — models self-checked before being returned |
| Differential oracle wired to real Z3 in CI | Done — 300-query seeded corpus, zero disagreements |

**Milestone (reached):** ordeal decides the fragment and agrees with the Z3
oracle across a differential corpus. UNSAT is *believed* but not yet
*checked* — the production path returns `Unknown` for engine-UNSAT until P2.

**Kill criterion:** if ordeal and the Z3 oracle disagree on any query, that op
is disabled (reverts to `Unknown`) until the bit-blasting rule is fixed.

---

## Phase P2 — Certificate-checked solver ★

The core deliverable: **soundness by checking, not by trust.**

| Task | Status |
|------|--------|
| LRAT proof emission from the SAT backend | Done — formatted from the CDCL RUP trace |
| Rust LRAT checker (the sole trusted component) | Done — `ordeal-lrat`, zero deps, mutation-tested |
| Verify the checker: Rust → Lean 4 via **Aeneas**, soundness theorem discharged (built with `rules_lean`) | Open — issue #12, obligation scaffolded in `lean/` |
| `Certificate` carries a checker-validated LRAT proof | Done — `Unsat` returned only on checker acceptance |
| Model self-check for SAT verdicts | Done (landed with P1) |

**Milestone:** every `Unsat` verdict is backed by a certificate that the
*verified* checker has validated. **Z3 is demoted** to oracle + benchmark only;
it is no longer consulted on the production path.

**Kill criterion:** an `Unsat` is never returned to a caller unless the verified
checker accepted its LRAT proof.

---

## Phase P3 — The sliver + integration

Cover loom's remaining needs and put ordeal in the hot path.

| Task | Status |
|------|--------|
| Non-extensional `Array(BV32 → BV8)` select/store | Planned |
| Uninterpreted `pure_call` congruence closure | Planned |
| loom integration (replace its Z3 verification path) | Planned |
| synth integration (translation-validation queries) | Planned |

**Milestone:** loom and synth verify against ordeal by default; the array/UF
sliver from `term.rs` is implemented and certificate-checked.

---

## Phase P4 — Drop Z3 from soundness ★

| Task | Status |
|------|--------|
| Op-by-op bit-blaster verification: each operator circuit proved equivalent to the formal BitVec semantics (closes the encoder trust gap) | Planned |
| Retire Z3 from the soundness argument entirely | Planned |
| Z3 retained only as an optional dev/CI differential oracle | Planned |
| Trust rests on the verified LRAT checker alone | Planned |

**Milestone:** the toolchain's soundness story no longer contains the words
"trust Z3." Removing the `oracle` feature removes Z3 completely with no effect
on correctness guarantees.

---

## Phase P5 — Performance

| Task | Status |
|------|--------|
| Amortized per-op latency at or below the Z3 integration path | Planned |
| Incremental term-graph caching across a loom/synth pass | Planned |
| Benchmark suite vs Z3 (integration latency, honest framing) | Planned |

**Milestone:** for loom/synth's real query mix, ordeal's amortized per-op
latency beats the Z3 integration path — the honest "beat Z3" claim (integration
overhead, not raw SAT throughput).

---

## Out of scope

Quantifiers, floating-point, `Optimize`, and incremental push/pop solving are
**not** planned. Ordeal is a specialized decision procedure for a closed
fragment, not a general SMT solver.

## Related issues

- loom [#246](https://github.com/pulseengine/loom/issues/246) — Z3 build pain (grounding).
- loom [#231](https://github.com/pulseengine/loom/issues/231) — verification tiering.
- synth [#76](https://github.com/pulseengine/synth/issues/76) — Z3 translation-validation integration.
- synth [#494](https://github.com/pulseengine/synth/issues/494) — SMT backend for codegen verification.
