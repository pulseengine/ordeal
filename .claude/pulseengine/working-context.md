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

In flight / next:
- v0.2.0 burn-down: 30 implemented / 5 draft (TR-004 LRAT emission, VER-003
  reproducible-build job, VER-004 license check, VER-005 rejection suite,
  VER-008 CaDiCaL parity). Not cuttable until statuses reach `verified` —
  needs `rivet import-results` wiring of CI evidence.
- P2 next: LRAT emission from the CDCL trace + wire ordeal-lrat into
  `check` + Aeneas→Lean verification (TR-005/006/013, FEAT-002, v0.3.0).
- 3 dependabot PRs open (#4 attest-build-provenance 1→4, #6
  download-artifact 4→8, #7 checkout 4→7) — #4/#6 touch the tag-only
  release path; handle in a release-pipeline pass.
- Upstream rivet defects: #648 (non-authorable inverses; 82+ bidirectional
  findings permanently open), #649 (transitive externals fail validate; use
  `--skip-external-validation`). Both re-confirmed on rivet 0.23.0.
