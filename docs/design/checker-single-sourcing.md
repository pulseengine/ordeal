# Design: single-source the trusted models — drift becomes unrepresentable

**Issue:** #48 · **Release:** v0.19.0 · **rivet:** TR-034 (draft until this
design is approved) · **Status: PROPOSED — no code lands until this doc is
reviewed.**

## The claim being protected

The soundness story rests on two Aeneas-generated Lean models of Rust
sources, with proofs stated *about the generated models*:

| Runs (Rust, trusted)                  | Model (Lean, generated)  | Generator           | Proof                              | Freshness protection today |
|---------------------------------------|--------------------------|---------------------|------------------------------------|----------------------------|
| `crates/ordeal-lrat/src/kernel.rs`    | `lean/Kernel.lean`       | `lean/regen.sh`     | `Sound.lean` (`lrat_check_sound`)  | #44 drift guard (required CI check) |
| `crates/ordeal/src/blast_kernel.rs`   | `lean/BlastKernel.lean`  | `lean/regen-blaster.sh` | `BlasterProof.lean` (rule ≡ BitVec semantics) | **NONE** |

If a model is stale, the proof certifies code that no longer runs. Today
this is prevented by *checking* (and for the blaster: by discipline alone —
a live gap found while writing this design, 2026-08-12). #48's bar is
stronger: make the stale-model state **impossible to represent**, not
detected.

Two smaller drift surfaces ride along:

- The Charon/Aeneas pins (`AENEAS_REV`/`CHARON_REV`) are **duplicated**
  across the two regen scripts — they can diverge silently.
- `docs/formal-verification.md` still describes the pre-#44 world ("no CI
  job re-runs regen.sh") — stale prose about the very mechanism at issue.

## Options considered

### O1 — the model is a build product, never a committed artifact *(recommended)*

Remove `Kernel.lean` and `BlastKernel.lean` from the tree (`.gitignore`
them). The **Lean proof CI job regenerates both models from the Rust
sources, then builds the proofs** — every run, unconditionally. Locally,
`lean/regen.sh` (run once, nix) produces them for proof development.

Drift is unrepresentable in the strongest sense: there is no committed
model to be stale. "The proof is about the current translation of the code
that ships" stops being a checked property and holds by construction. The
#44 drift workflow is **retired**, not extended to the blaster.

Costs, honestly:
- The Lean CI job gains a nix + Charon/Aeneas dependency. Warm (cached nix
  store, keyed on the pins) regen is ~2 s; cold is ~15 min but only when
  the pins change — the same profile the drift job already has today.
- Local proof development requires nix once per pin-bump. (Proof iteration
  after that is pure `lake`, unchanged.)
- PR diffs no longer show the generated-model delta. This loses nothing
  real: nobody reviews 976 lines of machine-emitted Lean for faithfulness —
  that is Aeneas's job, and the proof re-verifying is the actual signal.

### O2 — keep the committed copy as a cache; the proof job regenerates and overwrites before building

The proof provably certifies the current translation (same as O1), but a
committed copy remains for convenience and can still go stale in-repo, so a
freshness *check* survives alongside. Weaker than the issue's bar
(drift is representable, merely harmless), and it keeps two mechanisms
alive. Fallback if O1's nix-in-the-proof-job proves flaky in practice.

### O3 — a single spec (SpecTec-style DSL) that emits both Rust and Lean

Rejected. It inverts the trust economics: today the trusted translator is
Aeneas — an externally maintained, purpose-built, increasingly audited
tool. A homegrown emitter would *join* the TCB while demoting the
hand-reviewed `kernel.rs` to generated output. More trusted code, less
reviewable code, for the same property O1 gets by deleting a file.

### O4 — Lean as the source, extract the Rust

Rejected. Lean→Rust extraction is immature, and it would surrender the
properties the Rust side is chosen for: a dependency-free, wasm-clean,
line-reviewable kernel in the Aeneas-translatable fragment.

## The proposal (O1), concretely

1. **Single pins file.** `lean/toolchain-pins.env` holds `AENEAS_REV` /
   `CHARON_REV`; both regen scripts source it. One place to bump, nothing
   to diverge.
2. **One entry point.** `lean/regen.sh all|kernel|blaster` regenerates the
   requested models (keeps the two Charon invocations, shared plumbing).
   `regen-blaster.sh` folds in.
3. **`.gitignore` the generated models**; `git rm` the committed copies.
   `lakefile` unchanged (files exist at build time, produced by step 4
   in CI / by the developer locally).
4. **Lean CI job** (`Lean model + soundness proof`, already required):
   installs nix, restores the pinned-toolchain cache, runs
   `lean/regen.sh all`, then `lake build` + the zero-`sorry` gate, for the
   checker *and* blaster proofs. The job is required today; its guarantee
   strictly grows.
5. **Retire `.github/workflows/kernel-model-drift.yml`** and remove its
   context from the branch-protection required set **in the same change**
   that makes the Lean job self-sufficient — the gate never shrinks below
   its current strength at any commit (ordering: land the workflow change,
   confirm the Lean job green with regeneration, then drop the drift
   context; the required-contexts count goes 8 → 7 with the drift
   guarantee absorbed, never absent).
6. **Rewrite the stale sections of `docs/formal-verification.md`**: the
   "known process gap" section becomes a description of generation-by-
   construction; the reproduce-the-checks block gains `./lean/regen.sh all`
   as its first line.

## What this retires from the trusted base — and what it does not

Retired: "the committed model is the current translation" as an assumption
(#44's checked property, and the blaster's unchecked one). Nothing needs to
believe it anymore; the artifact class is gone.

**Not retired** (and now the *entire* faithfulness residual):
**Charon/Aeneas translation faithfulness** at the pinned revisions, plus
the Lean kernel itself. That residual is exactly what **#47 (TR-035)
attacks next**: an independent bv_decide-style Lean checker run
adversarially against the Aeneas path on a shared LRAT corpus, where any
verdict disagreement is a hard error. The sequencing is deliberate — after
this design, #47's differential aims at the only faithfulness assumption
left standing.

## Verification criteria (TR-034)

1. `git ls-files lean/ | grep -E 'Kernel.lean|BlastKernel.lean'` is empty;
   both names are `.gitignore`d.
2. The required Lean CI job regenerates both models and proves both
   developments with zero `sorry` — green on an unrelated change (warm
   path) and after a pin bump (cold path), with wall times recorded.
3. **Mutation demonstration:** a scratch branch semantically alters
   `kernel.rs` (e.g. weakens the RUP conflict check) with **no manual model
   step**; the Lean job must go red on the regenerated model — the
   green-proof-over-stale-model state is unconstructible. Same
   demonstration once for `blast_kernel.rs`.
4. The drift workflow is deleted and its required context removed, with
   the branch-protection change recorded (before/after context lists) in
   the PR — the gate is never empty and never weaker.
5. Exactly one pins definition exists (`grep -r AENEAS_REV` finds the env
   file and its two consumers only).

## Falsification statement

This design is wrong if, after landing, any commit on `main` can be green
while `lake`-built proofs certify a model that is not the translation of
the `kernel.rs`/`blast_kernel.rs` at that same commit — in particular if
the Lean job can be skipped, satisfied from a stale artifact cache, or
passes without running regeneration.

## Open questions for review

1. **O1 vs O2**: accept the nix dependency inside the required Lean job
   (O1), or keep a committed cache + absorbed check (O2)? This doc
   recommends O1.
2. Is the local-dev bar (nix required once before proof work) acceptable
   for contributors? (`lean/README.md` would document the one command.)
3. Retire the drift workflow entirely (proposed) or keep it as a
   non-required fast advisory on PRs that touch the kernels?
4. Should the mutation demonstration (criterion 3) become a *recurring*
   CI exercise (a scheduled job that injects the mutation in a throwaway
   worktree and asserts the red), or is the one-time recorded evidence
   enough? One-time is proposed; recurring adds ~10 min nightly.
