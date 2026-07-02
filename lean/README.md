# The LRAT checker soundness obligation (TR-013 / FEAT-002)

This directory reserves the Lean 4 side of ordeal's trust story. It contains
**no proof yet** — the obligation below is tracked and open, and nothing in
CI claims otherwise.

## The obligation

The sole trusted component is `crates/ordeal-lrat` (a ~250-line,
dependency-free, RUP-only textual LRAT checker). Its soundness theorem:

> If `ordeal_lrat::check(cnf, cert)` returns `Ok(())`, then `cnf` is
> unsatisfiable.

Stated in Lean terms (against the Aeneas-generated functional model of the
Rust code):

```lean
theorem lrat_check_sound
    (cnf : List (List Int)) (cert : String)
    (h : OrdealLrat.check cnf cert = .ok ()) :
    ∀ σ : Assignment, ¬ Satisfies σ cnf
```

## The chosen path (ARCHITECTURE.md)

1. Translate `crates/ordeal-lrat` to a Lean 4 functional model with
   [Aeneas](https://github.com/AeneasVerif/aeneas).
2. Prove the theorem against that model (RUP-step soundness by induction
   over the hint chain; acceptance implies the empty clause is derivable).
3. Build with the org's `rules_lean` (reserved in `MODULE.bazel`) and gate
   CI on the proof discharging.

Fallback (documented in ARCHITECTURE.md): write the checker directly in
Lean, `bv_decide`-style, if the Aeneas translation of some construct proves
awkward.

## Status

**The Lean model exists and is complete.** `Kernel.lean` is the Aeneas
translation of `crates/ordeal-lrat/src/kernel.rs` (the string-free checking
core) — generated with ZERO translation errors after the kernel was written
in the Aeneas-friendly fragment (index loops, no early returns inside
loops, owned step in the main loop; see the kernel's module docs).
Regenerate with `lean/regen.sh` (pinned Charon/Aeneas via nix) after any
kernel change and commit the result.

Still open (issue #12):
1. A lakefile wiring the `Aeneas` Lean support library so `Kernel.lean`
   elaborates in CI.
2. Discharge the two axiomatized externals the model still carries
   (`core.num.I32.unsigned_abs`, `alloc.vec.Vec.is_empty`) — provide
   definitions or upstream Aeneas-std coverage.
3. State and prove `lrat_check_sound` over `kernel.check_steps`.

Until the theorem is discharged, an `Unsat` from ordeal is backed by a
certificate validated by the *mutation-tested but not formally verified*
Rust checker. That is strictly stronger than trusting the solver — the
checker is small, simple, and independent — but it is not yet the final
P2 trust story. TR-006/TR-013 and FEAT-002 stay un-`verified` in rivet
until this closes.
