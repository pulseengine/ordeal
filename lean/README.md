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

**The model elaborates.** This directory is a lake package (`lakefile.lean`
pins the Aeneas Lean library to the same revision as regen.sh; the
`lean-toolchain` matches Aeneas's). `lake build Kernel` — the CI gate — is
green: **zero axioms** (both former externals were eliminated at the Rust
source) and zero sorries in the model. `Sound.lean` states the CNF
semantics and the `lrat_check_sound` theorem; it type-checks against the
generated model and carries the one tracked `sorry` — it is deliberately
NOT a default target, and nothing claims the theorem is discharged.

Still open (issue #12):
1. Prove `lrat_check_sound` (proof plan documented in `Sound.lean`).
2. Trust-audit notes for the final story: the Aeneas *support library*
   itself currently contains 3 `sorry`s (`Aeneas/Std/Slice.lean` ×2,
   `Aeneas/Std/StringIter.lean` ×1) — the discharge must either avoid
   depending on those lemmas or get them fixed upstream.
3. Upstream Aeneas extraction bug (workaround in place): assigning an enum
   constant through an index projection (`clauses[i] = None`) extracts as a
   unit store (`Slice.update … ()`), which does not type-check; routing the
   write through a plain `&mut` helper (`clear_slot`) extracts correctly.
   Minimal repro = kernel.rs at the commit before `clear_slot` + regen.sh.
   Worth reporting to AeneasVerif/aeneas.

Until the theorem is discharged, an `Unsat` from ordeal is backed by a
certificate validated by the *mutation-tested but not formally verified*
Rust checker. That is strictly stronger than trusting the solver — the
checker is small, simple, and independent — but it is not yet the final
P2 trust story. TR-006/TR-013 and FEAT-002 stay un-`verified` in rivet
until this closes.
