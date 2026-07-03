# Working context — ordeal

## State

(owned by the pulseengine hooks — mechanical checkpoint lives here)

## Session notes

**As of 2026-07-02 (P1 campaign session):** ROADMAP P1 / FEAT-001 is DONE and
merged to main (PR #10 `695e2c9`, mirror sync PR #11 `ed36268`; main
post-merge CI + Fuzz Smoke both `completed:success`).

What landed: full pipeline (blast → AIG → Tseitin → own pure-Rust CDCL →
self-checked models), `ordeal-lrat` checker crate (RUP-only, zero deps),
real Z3 oracle behind `oracle` feature with seeded corpus + differential
harness. **Milestone evidence:** `differential_ordeal_vs_z3_on_corpus` —
300 queries, zero disagreements, SAT+UNSAT both exercised (green locally
with z3 4.15 AND in CI with distro z3 after the 2s per-query timeout).
Clean-room verified 11/12 claims (12th refuted only a stale count in the
claim text).

Key decisions (don't relitigate):
- Engine-UNSAT surfaces as `Unknown` on the production path until P2 —
  `CheckResult::Unsat` is unreachable by construction; the differential
  harness uses crate-internal `Solver::check_raw`.
- CDCL proof trace records RUP-ordered antecedent chains (level-0 unit
  reasons → 1UIP reasons in trail order → conflict clause last; index i<n =
  input clause i, n+k = k-th learned) so P2 LRAT emission is formatting.
- ordeal-lrat is sequential-id, RUP-only (rejects RAT with a dedicated
  error) — matches what the CDCL will emit.
- CI clippy gates DEFAULT features only; oracle-feature clippy lives in the
  non-blocking Z3 job (which installs libz3-dev).
- Statuses: artifacts go `implemented` when code+measure exist and pass;
  `verified` needs executed-result evidence (release-execution work).

**Pass 2 (same day): P2 + closure DONE** — certificate path merged (PR #13):
Unsat carries ordeal-lrat-validated LRAT; evidence layer merged (PR #14):
VE/VV artifacts with CI URLs, ~49 verified, v0.1.0+v0.2.0 CUTTABLE; repro
CI job; VER-004→v0.4.0, VER-008→v0.6.0 moved; dependabot #4/#6/#7 merged;
Lean obligation scaffolded (lean/README.md, issue #12) — TR-006/TR-013/
FEAT-002/VER-002/VER-015 block v0.3.0 until the proof discharges.

**Pass 3 (in flight): cutting v0.2.0 then starting v0.3.0** —
- Branch protection NOW ENFORCED on main (7 required checks, admins too).
- PR #16 = release prep (version 0.2.0, two-crate publish order: ordeal-lrat
  first; ordeal cannot `cargo package` before the checker is on the index).
- After merge: tag v0.2.0 → release.yml + crates.io publish; verify assets.
- Then v0.3.0: plan is to split ordeal-lrat into parser + string-free core
  so the Aeneas target is small; Aeneas NOT installed (OCaml toolchain).

**Pass 9: campaign to v0.6.0 — v0.3.0 CUT** —
- v0.3.0 tagged + release/publish triggered (be9b67e). Re-scoped: sliver
  artifacts → v0.3.0 (verified), Lean items → v0.5.0. docs/consuming-ordeal.md
  + issue labels (field-report/missing-capability/soundness) for the trial
  model. This is the release loom/synth try.
- v0.4.0 = field-hardening: BLOCKED until real loom/synth issues arrive
  (external repos try v0.3.0 and report). Nothing to do proactively beyond
  intake readiness (done).
- v0.5.0 (Lean proof) load_cnf leaf: de-risked to precise plumbing —
  clonei32_id (`simp [core.clone.CloneI32]`) and clonevec_id
  (`Slice.clone_spec (fun x _ => clonei32_id x)`, post `v = v'`) BOTH PROVEN.
  Remaining for load_cnf: `step*` walks the body but defers push's
  precondition `clauses.length < Usize.max` as a side goal → STRENGTHEN the
  loop invariant to also carry `clauses.val.length = i.val` (makes both the
  push precondition and the take_succ map-close provable). Then apply_delete,
  check_rup, check_steps_loop. Single `step` on push errors "goal is not
  spec"; use `step*` (defers preconditions as ordered side goals).
- v0.6.0 (P4) not yet started — next fresh track (Kani per-width op proofs).
- Upstream rivet defects: #648/#649 unchanged (--skip-external-validation).
