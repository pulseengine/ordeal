<div align="center">

# Ordeal

<sup>A certificate-checked QF_BV SMT solver for the PulseEngine toolchain</sup>

&nbsp;

![Rust](https://img.shields.io/badge/Rust-CE422B?style=flat-square&logo=rust&logoColor=white&labelColor=1a1b27)
![License: Apache-2.0](https://img.shields.io/badge/License-Apache--2.0-blue?style=flat-square&labelColor=1a1b27)

&nbsp;

<h6>
  <a href="https://github.com/pulseengine/meld">Meld</a>
  &middot;
  <a href="https://github.com/pulseengine/loom">Loom</a>
  &middot;
  <a href="https://github.com/pulseengine/synth">Synth</a>
  &middot;
  <a href="https://github.com/pulseengine/ordeal">Ordeal</a>
  &middot;
  <a href="https://github.com/pulseengine/kiln">Kiln</a>
  &middot;
  <a href="https://github.com/pulseengine/sigil">Sigil</a>
</h6>

</div>

&nbsp;

Ordeal (meaning "verdict / judgment") is a specialized, **certificate-checked** QF_BV SMT solver. It decides bitvector equivalence and satisfiability queries for the [PulseEngine](https://github.com/pulseengine) toolchain — specifically the queries that [loom](https://github.com/pulseengine/loom) (verified WASM optimizer) and [synth](https://github.com/pulseengine/synth) (verified WASM→ARM codegen) actually emit.

**Status (v0.15.0, on [crates.io](https://crates.io/crates/ordeal)).** The engine is live: the full bit-blast → AIG → Tseitin CNF → pure-Rust CDCL → LRAT pipeline decides the closed QF_BV fragment, with a semantics-preserving canonicalization pass (commutative-operand ordering + const-folding, v0.8.0) that collapses structural-equivalence cliffs — e.g. `mul(a,b) ≢ mul(b,a)` @ 32, which went from not-finishing-in-590s to an instant certified UNSAT. A `trap` module (v0.9.0) expresses each partial WASM op's trap condition (`div`/`rem` ÷0 + overflow, OOB `load`/`store`, `call_indirect`, `unreachable`) as a QF_BV predicate and composes trap-preservation VCs, so consumers verify **trap**-equivalence and catch a transformation that drops a trap — classification of bits only, no floating-point. A `layout` module (v0.10.0) splits and reassembles little-endian bytes as pure `extract`/`concat`, so a wire-codec round-trip or an AADL↔WIT↔ABI record layout is one certificate-checked `prove_equiv` call; and `bvurem` is native, which makes the whole `bvudiv`/`bvurem`/`bvsdiv`/`bvsrem` family multiplier-free. `Sat` verdicts carry a self-checked counterexample model; `Unsat` verdicts carry an LRAT certificate that the `ordeal-lrat` checker validated before the verdict was returned — and as of v0.7.0 that `Certificate` carries the refuted CNF too (`cert.cnf` + `cert.lrat`), so a consumer can **independently re-check it** with `cert.recheck()` and re-establish UNSAT with zero trust in the solver; `Unknown` stays conservative (never optimize on it). The array/UF sliver (`Solver::check_sliver`), a bool→BV `ite` bridge, derived-op lowering helpers, a resource-bounded `check_with_limit`, and a one-call layout-equivalence oracle (`Solver::prove_equiv`, for spar's codegen checks) are all available. A minimal SMT-LIB2 front-end (`ordeal check foo.smt2`) reads the QF_BV subset loom/synth emit. The array sliver now resolves **symbolic** BV32 indices for `select`/`store` (v0.11.0, a sound read-over-write reduced into the closed fragment), which unblocks loom's verifier migration off Z3. And `ordeal verus <verus --log-all dir>` (v0.12.0) discharges the `by (bit_vector)` obligations **Verus itself emits** — all 62 of gale's, each with a re-checkable LRAT certificate — turning unchecked-Z3 ASIL-D evidence into the CompCert argument, with no hand transcription in the loop. The checker's soundness is now **machine-checked in Lean 4** (Rust → Aeneas → `kernel.spec.lrat_check_sound`, issue #12): if it accepts, the CNF is unsatisfiable — zero `sorry`, no `sorryAx`. The solver stays untrusted; only the now-proven, dependency-free checker is trusted. Each bit-blasting rule is additionally Kani-proven equal to its concrete reference semantics for all inputs (v0.6.0), so the blaster's soundness no longer leans on the Z3 differential. As of v0.5.1 the model↔code drift gap is closed: the committed Lean model is verified (via the real Charon+Aeneas toolchain, CI-guarded) to be the current translation of the shipped `kernel.rs`. Precise scope and trust boundary: [docs/formal-verification.md](docs/formal-verification.md).

Part of PulseEngine — a WebAssembly toolchain for safety-critical embedded systems:

| Project | Role |
|---------|------|
| [**Loom**](https://github.com/pulseengine/loom) | WASM optimizer with SMT verification |
| [**Synth**](https://github.com/pulseengine/synth) | WASM-to-ARM AOT compiler with Rocq proofs |
| [**Ordeal**](https://github.com/pulseengine/ordeal) | Certificate-checked QF_BV SMT solver |
| [**Meld**](https://github.com/pulseengine/meld) | WASM Component Model static fuser |
| [**Kiln**](https://github.com/pulseengine/kiln) | WASM runtime for safety-critical systems |
| [**Sigil**](https://github.com/pulseengine/sigil) | Supply chain attestation and signing |

## Why ordeal exists

Loom and synth both verify their transformations with an SMT solver, and both pay for it in build pain: statically linking Z3 is a recurring source of toolchain friction (header discovery, `Z3_SYS_Z3_HEADER`, `LIBRARY_PATH`, cross-compilation to `wasm32`, reproducibility). This is filed as **loom issue #246**.

The deeper problem is a *trust* problem, not just a build problem: Z3 is a large, fast, general-purpose solver, and when it says "UNSAT" we take it on faith. For a toolchain whose whole pitch is *provably correct* transformation, "trust the big C++ solver" is an uncomfortable link in the chain.

Ordeal fixes both:

- **Build pain:** a pure-Rust default build with **zero external dependencies**. No Z3 to link. The default build is also **`wasm32-wasip2`-clean**, so loom/synth can verify in-process even when compiled to a WebAssembly component.
- **Trust:** the solver is **untrusted**. It emits a machine-checkable certificate that a small, formally-verified checker validates. Only the checker is trusted.

## Architecture in brief

Ordeal follows the **certifying-algorithm** pattern (CompCert-style; blueprint = Lean 4's `bv_decide`, OOPSLA 2025):

> An **untrusted solver** produces an answer *plus a proof*. A **formally-verified checker** validates the proof. A bug in the (large, fast, evolving) solver can at worst make it fail to produce a valid certificate — it can never make a wrong answer be accepted.

For an UNSAT verdict the proof is an **LRAT certificate**; the verified checker replays it. Only the checker is in the trusted computing base.

**How the checker gets verified.** The checker is written in Rust and translated to **Lean 4 via [Aeneas](https://github.com/AeneasVerif/aeneas)**, where its soundness theorem (*accept ⇒ UNSAT*) is discharged — the "not lots of hand-math" path. This is the chosen route; the alternative of writing the checker directly in Lean (the `bv_decide` style) is kept as a documented fallback. The Lean side is built with the org's `rules_lean` (reserved in `MODULE.bazel`).

```
term graph → bit-blast → AIG → CNF (Tseitin) → SAT → LRAT → verified checker
```

- **SAT core — we own it.** The primary engine on **every** target (including `wasm32-wasip2`) is **ordeal's own pure-Rust CDCL solver** — FFI-free, permissively licensed, LRAT-emitting. This is a deliberate full-control decision: no off-the-shelf pure-Rust core is simultaneously maintained, permissive, and LRAT-emitting (varisat is stale, splr is MPL/DRAT-only, CreuSAT is the wrong shape), so owning it is the only way to satisfy wasip2 **and** certificate-checking together. Native **CaDiCaL** (C++ via FFI) is an *optional accelerator/benchmark only* — `cfg`-gated off on wasm, never load-bearing. The default build carries no external solver, so it stays zero-dep and wasip2-clean.
- **Z3 is a differential oracle + benchmark rival, not the engine.** During development/CI, queries can be cross-checked against Z3 (behind the off-by-default `oracle` feature); any disagreement is a bug. Z3 is *not* part of the soundness argument, and a later phase drops it from soundness reasoning entirely.

See [ARCHITECTURE.md](ARCHITECTURE.md) for the full pipeline and trust boundary.

### An honest note on "beating Z3"

Ordeal does **not** aim to out-solve Z3's SAT engine — Z3 is world-class and we will not beat it at raw SAT. The win is **amortized per-op integration latency**: ordeal runs *in-process*, with no SMT-LIB text to emit and parse, no process spawn, and no general theory-combination machinery for a fragment that never needs it. For the tight, repeated, small equivalence queries loom and synth emit, that integration overhead dominates — and that is what ordeal removes.

## Scope: the closed fragment

Ordeal decides a deliberately **closed** QF_BV fragment (widths 8 / 32 / 64):

- **Bitvector ops:** `bvadd`, `bvsub`, `bvmul`, `bvudiv`, `bvand`, `bvor`, `bvxor`, `bvshl`, `bvlshr`, `bvashr`, `bvrotr`, `extract{hi,lo}`, `concat`, `zero_ext{by}`, `sign_ext{by}`.
- **Boolean predicates** (what you assert/check): `eq`, `ne`, `ult`, `ule`, `ugt`, `uge`, `slt`, `sle`, `sgt`, `sge`, plus `not` / `and` / `or`.
- **Query shape:** one-shot `check-sat` expecting **UNSAT** (equivalence), returning a **counterexample model** when SAT.

A later **sliver** (represented today as a TODO in `term.rs`, not implemented): non-extensional `Array(BV32 → BV8)` select/store, plus uninterpreted `pure_call` congruence.

**Not in scope:** quantifiers, floating-point, `Optimize`, incremental solving.

## Quickstart

Requires Rust (edition 2024). The default build has no external dependencies.

```bash
git clone https://github.com/pulseengine/ordeal.git
cd ordeal
cargo build
cargo test

# Development-only: enable the Z3 differential oracle feature
cargo build --features oracle

# Run the CLI banner (documents the check subcommand)
cargo run --bin ordeal

# Decide an SMT-LIB2 file (QF_BV subset), or read from stdin with `-`
cargo run --bin ordeal -- check query.smt2
echo '(declare-const x (_ BitVec 32))(assert (= x #x0000002a))(check-sat)(get-model)' \
  | cargo run --bin ordeal -- check -
# → sat
#   ((x #x0000002a))
```

The primary production interface remains the Rust API; the `check` subcommand is
a convenience/front-end for SMT-LIB2 text. Any construct outside the closed
QF_BV subset is reported as `unsupported: <what>` and exits non-zero — the
certificate-checked solver never guesses.

### wasm32-wasip2 (first-class target)

loom self-optimizes as a WebAssembly component and embeds ordeal in-process, so
`wasm32-wasip2` is a **first-class, CI-gated build target** — not an
afterthought. Ordeal's own pure-Rust CDCL core is the engine here (as on every
target); the optional native CaDiCaL accelerator is `cfg`-gated out.

```bash
rustup target add wasm32-wasip2
cargo build --target wasm32-wasip2 --release
```

### Bazel (org build)

Ordeal also builds with the PulseEngine org Bazel rules (`rules_rust` for the
crate, `rules_wasm_component` for the wasip2 component; `rules_lean` reserved
for the future verified checker):

```bash
bazel build //...                         # native library + CLI
bazel build --config=wasm //crates/ordeal # wasm32-wasip2 component (once a WIT world exists)
```

The Bazel job is advisory in CI; the enforced wasip2 gate is the cargo command
above.

Library sketch:

```rust
use ordeal::{Solver, BoolTerm, BvTerm, Sort, CheckResult};

let bv32 = Sort::new(32);
let x = BvTerm::Var { name: "x".into(), sort: bv32 };

let mut s = Solver::new();
s.assert(BoolTerm::Eq(Box::new(x.clone()), Box::new(x)));

match s.check() {
    CheckResult::Unsat(cert) => { /* equivalence holds; validate cert */ }
    CheckResult::Sat(model)  => { /* counterexample in model */ }
    CheckResult::Unknown     => { /* MUST treat conservatively: do not optimize */ }
}
```

The crate is published as [`ordeal`](https://crates.io/crates/ordeal) on crates.io.

## Roadmap

Full detail in [ROADMAP.md](ROADMAP.md). Summary:

| Phase | Goal |
|-------|------|
| **P0** | Skeleton: closed fragment types, conservative `Unknown` solver, CI. |
| **P1** | Bit-blaster: fragment → AIG → CNF (Tseitin); SAT backend integrated. |
| **P2** | **Certificate-checked solver:** LRAT emission + formally-verified checker. Z3 demoted to oracle/benchmark. |
| **P3** | The array/UF sliver; loom & synth integrated as first callers. |
| **P4** | **Drop Z3 from the soundness argument** — trust rests on the verified checker alone. |
| **P5** | Performance: amortized per-op latency at or below the Z3 integration path. |

## Related issues

- loom [#246](https://github.com/pulseengine/loom/issues/246) — Z3 build pain (the grounding for ordeal).
- loom [#231](https://github.com/pulseengine/loom/issues/231) — verification tiering.
- synth [#76](https://github.com/pulseengine/synth/issues/76) — Z3 translation-validation integration.
- synth [#494](https://github.com/pulseengine/synth/issues/494) — SMT backend for codegen verification.

## License

Apache-2.0 — see [LICENSE](LICENSE).

---

<div align="center">

<sub>Part of <a href="https://github.com/pulseengine">PulseEngine</a> &mdash; WebAssembly toolchain for safety-critical systems</sub>

</div>
