# The LRAT checker soundness proof (TR-013 / FEAT-002)

This directory holds the Lean 4 side of ordeal's trust story. The soundness
theorem below is **proved** — `sorry`-free and axiom-clean — and the proof is
gated in CI (the *Lean model + soundness proof* job). Issue #12 is discharged.

## The obligation

The sole trusted component is `crates/ordeal-lrat` (a ~250-line,
dependency-free, RUP-only textual LRAT checker). Its soundness theorem:

> If `ordeal_lrat::check(cnf, cert)` returns `Ok(())`, then `cnf` is
> unsatisfiable.

Stated in Lean terms (against the Aeneas-generated functional model of the
Rust code), and proved as `kernel.spec.lrat_check_sound` in `Sound.lean`:

```lean
theorem lrat_check_sound
    (cnf : Slice (alloc.vec.Vec Std.I32)) (steps : Slice Step)
    (hfit : cnf.val.length + steps.val.length ≤ Std.Usize.max)
    (h : kernel.check_steps cnf steps = ok (core.result.Result.Ok ())) :
    unsat (cnf.val.map (fun c => c.val))
```

## The path taken (ARCHITECTURE.md)

1. Translate `crates/ordeal-lrat` to a Lean 4 functional model with
   [Aeneas](https://github.com/AeneasVerif/aeneas) (`Kernel.lean`).
2. Prove the theorem against that model (RUP-step soundness by induction
   over the hint chain; acceptance implies the empty clause is derivable).
3. Build with the org's `rules_lean` (reserved in `MODULE.bazel`) and gate
   CI on the proof discharging.

## Status — proved

**The Lean model exists and is complete.** `Kernel.lean` is the Aeneas
translation of `crates/ordeal-lrat/src/kernel.rs` (the string-free checking
core) — generated with ZERO translation errors after the kernel was written
in the Aeneas-friendly fragment (index loops, no early returns inside loops,
owned step in the main loop; see the kernel's module docs). Regenerate with
`lean/regen.sh` (pinned Charon/Aeneas via nix) after any kernel change and
commit the result. `lake build Kernel` — a CI gate — is green: **zero
axioms** (both former externals were eliminated at the Rust source) and zero
sorries in the model.

**The mathematics is proved.** `Sound.lean` contains a PURE, monad-free
restatement of the checker (`pCheckSteps`) and a complete, `sorry`-free proof
that it is sound — `pure_check_sound : pCheckSteps cnf steps = true → unsat
cnf`. This is the whole mathematical content of #12: RUP-step soundness, the
"every live clause is implied by the CNF" invariant carried through the
deletion/addition loop, and empty-clause ⇒ UNSAT.

**The simulation obligation is discharged.** `kernel_refines_pure` — that an
accepting run of the generated monadic Aeneas model is an accepting run of the
pure checker on the same data — is proved (Aeneas `progress` + loop lemmas
over the generated code). `lrat_check_sound` follows from `pure_check_sound`
composed with it, end to end. There is no remaining `sorry`.

**Axiom-clean and CI-gated.** `#print axioms kernel.spec.lrat_check_sound`
shows ONLY the three standard Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`) — no `sorryAx`, no `native_decide`. The *Lean model + soundness
proof* CI job is a real gate (no `continue-on-error`): it builds `Kernel` and
`Sound` and fails if `lake env lean Sound.lean` reports any sorry-bearing
declaration. A proven leaf cannot silently regress to `sorry`.

## Trust boundary (what the proof does and does not cover)

The theorem is about the **Aeneas-generated model** (`Kernel.lean`). Its
faithfulness to the actual Rust (`kernel.rs`) rests on `regen.sh` — CI does
**not** re-run Aeneas to confirm `Kernel.lean` is the current translation of
`kernel.rs`. That model-drift guard is a known gap tracked in **issue #44**
(freshness); the `kernel-model-drift` workflow is the intended closure. So:
`lrat_check_sound` is a mechanized proof modulo (a) the three standard Lean
axioms and (b) the assumption that the committed `Kernel.lean` matches
`kernel.rs`, which is a `regen.sh` convention rather than a re-run CI check.

Two developer notes:
- The Aeneas *support library* carries a few `sorry`s of its own
  (`Aeneas/Std/{Slice,StringIter}.lean`). `#print axioms` above confirms
  `lrat_check_sound` does **not** depend on any of them — the theorem is
  axiom-clean regardless.
- Upstream Aeneas extraction bug (workaround in place): assigning an enum
  constant through an index projection (`clauses[i] = None`) extracts as a
  unit store (`Slice.update … ()`), which does not type-check; routing the
  write through a plain `&mut` helper (`clear_slot`) extracts correctly.
  Minimal repro = `kernel.rs` at the commit before `clear_slot` + `regen.sh`.
  Worth reporting to AeneasVerif/aeneas.

With the theorem discharged, an `Unsat` from ordeal is backed by a certificate
whose acceptance criterion is now **formally proved** to imply unsatisfiability
(modulo the trust boundary above) — not merely validated by a mutation-tested
Rust checker. The remaining step toward the final P2 story is closing the
model-drift guard (#44), not any open mathematics.
