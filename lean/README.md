# The LRAT checker soundness proof (TR-013 / FEAT-002)

This directory holds the Lean 4 side of ordeal's trust story. The soundness
theorem below is **proved** — `sorry`-free and axiom-clean — and the proof is
gated in CI (the *Lean model + soundness proof* job). Issue #12 is discharged.

## The obligation

The sole trusted component is `crates/ordeal-lrat` (a small, dependency-free,
RUP-only textual LRAT checker; its string-free checking core, `kernel.rs`, is
486 lines). Its soundness theorem:

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
3. Build the proofs with `elan` + `lake` (the *Lean model + soundness proof*
   CI job) and gate CI on the proof discharging. (`rules_lean` is only a
   commented placeholder in `MODULE.bazel`; it has never built anything here.)

## Status — proved

**The Lean model exists and is complete.** `Kernel.lean` is the Aeneas
translation of `crates/ordeal-lrat/src/kernel.rs` (the string-free checking
core) — generated with ZERO translation errors after the kernel was written
in the Aeneas-friendly fragment (index loops, no early returns inside loops,
owned step in the main loop; see the kernel's module docs). The model is a
**build product** (TR-034): it is `.gitignore`d, and both models come from
`lean/regen.sh all` (pinned Charon/Aeneas via nix, pins single-sourced in
`toolchain-pins.env`) — run it once before proof development; the Lean CI
job runs it before every proof build, so the proofs always certify the
current translation. `lake build Kernel` — a CI gate — is green with zero
sorries in the model. The LRAT path reaches **no axiom** (both of its former
externals were eliminated at the Rust source); since TR-038 the model carries
**one opaque external again** — `i32::unsigned_abs`, called only by
`clause_satisfied` on the SAT-witness path (see the SAT-witness section
below for what that costs and how to remove it).

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

## The SAT-witness checker (TR-038 → TR-044 / VER-039)

`SatWitness.lean` extends the same semantics — nothing in `Sound.lean`
changes; `asnOf` is the only new definition — to the SAT direction,
`kernel::check_sat` / `kernel::check_binding` (the re-checkable witness of
TR-038), with four theorems, `sorry`-free and a default `lake build` target:

```lean
/-- DIMACS variable v ≥ 1 reads assignment[v-1]; past the end reads false. -/
def asnOf (assignment : List Bool) : Asn := fun v => assignment.getD (v - 1) false

theorem check_sat_sound (habs : UnsignedAbsSpec)
    (cnf : Slice (alloc.vec.Vec Std.I32)) (assignment : Slice Bool)
    (h : kernel.check_sat cnf assignment = ok (core.result.Result.Ok ())) :
    cnfHolds (asnOf assignment.val) (cnf.val.map (fun c => c.val))

theorem check_sat_satisfiable (habs : UnsignedAbsSpec) … :
    ¬ unsat (cnf.val.map (fun c => c.val))

theorem check_binding_sound
    (assignment : Slice Bool) (bits : Slice Std.I32) (value : Std.U128)
    (h : kernel.check_binding assignment bits value = ok (core.result.Result.Ok ())) :
    ∀ k, (hk : k < bits.val.length) →
      value.val.testBit k = decide (litHolds (asnOf assignment.val) bits.val[k])

theorem verdicts_exclusive (habs : UnsignedAbsSpec)
    (cnf : Slice (alloc.vec.Vec Std.I32)) (steps : Slice Step) (assignment : Slice Bool)
    (hfit : cnf.val.length + steps.val.length ≤ Std.Usize.max)
    (hu : kernel.check_steps cnf steps = ok (core.result.Result.Ok ()))
    (hs : kernel.check_sat cnf assignment = ok (core.result.Result.Ok ())) : False
```

- The CNF is the ACTUAL `check_sat` argument (`cnf.val`); the bundle, its
  hash check and its parser stay untrusted, exactly as for UNSAT.
- `asnOf`'s out-of-range default is never load-bearing: the strong form
  `check_sat_witnessed` shows every accepted clause has a literal the kernel
  validated (nonzero, non-`MIN`), read from a real slot
  (`1 ≤ |lit| ≤ |assignment|`) and found true.
- `check_binding_sound` is axiom-clean (`#print axioms` = the three standard
  axioms), pinned in `AxiomCheck.lean`.
- **One opaque external — the `habs` hypothesis.** `clause_satisfied` calls
  `i32::unsigned_abs`, which the pinned Aeneas has no model of, so
  `Kernel.lean` declares `axiom core.num.I32.unsigned_abs : I32 → Result U32`.
  Nothing is derivable about an opaque symbol, so the `check_sat` family is
  stated CONDITIONALLY on `UnsignedAbsSpec` (`∀ lit, unsigned_abs lit ⦃ u =>
  u.val = |lit.val| ⦄` — the std function's contract) as an explicit
  hypothesis, never an axiom added here. `#print axioms` on those theorems
  therefore lists that function symbol besides the three standard axioms;
  `AxiomCheck.lean` pins exactly that, so it cannot grow silently. The fix is
  at the Rust source, as for the LRAT path's former externals: route
  `clause_satisfied` through `lit_var` (which `check_binding` already uses);
  the hypothesis and the extra symbol then vanish and the pin shrinks.
- Kernel-review finding, recorded in the file header rather than papered
  over: `clause_satisfied` stops at the first true literal, so literals after
  it in an already-satisfied clause are not validated. Soundness is
  unaffected (a clause with a true literal holds whatever else it contains),
  which is why the spec speaks of "a witnessing literal", not "every literal
  in range".

## Trust boundary (what the proof does and does not cover)

The theorem is about the **Aeneas-generated model** (`Kernel.lean`). That
model is **generated, not checked** (TR-034): it is a `.gitignore`d build
product — there is no committed model that could go stale — and the required
*Lean model + soundness proof* CI job re-runs Charon + Aeneas
(`lean/regen.sh all`, pins single-sourced in `lean/toolchain-pins.env`)
**before every proof build**, so the proofs always certify the translation of
the current `kernel.rs` by construction. (Freshness was originally planned as
a separate drift-diff workflow — issue #44 — which this construction absorbed
and retired; see `docs/design/checker-single-sourcing.md`.)

What remains trusted, then: `lrat_check_sound` is a mechanized proof modulo
(a) the three standard Lean axioms plus Lean's kernel, and (b)
**Charon/Aeneas translation faithfulness** at the pinned revisions — the
translator is a research tool and not itself verified. That residual is now
witnessed adversarially by the TR-035 dual-mechanisation differential
(CI-gated): ordeal's Aeneas-proven checker is differenced against Lean core's
independently verified `Std.Tactic.BVDecide.LRAT.check` on a shared
pristine + mutant certificate corpus, and any verdict disagreement fails CI.

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
whose acceptance criterion is **formally proved** to imply unsatisfiability
(modulo the residual trust base above) — not merely validated by a
mutation-tested Rust checker. There is no open mathematics and no open
freshness gap: the model is regenerated under the same required CI job that
proves it.
