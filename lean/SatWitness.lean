/- Soundness of the SAT-witness checker (TR-038 follow-up, TR-044 / VER-039).

   This file is HAND-WRITTEN (unlike Kernel.lean, which regen.sh generates).
   It states what "the witness checker is sound" means and proves it over
   the Aeneas-generated model of `kernel::check_sat` / `kernel::check_binding`
   (crates/ordeal-lrat/src/kernel.rs), reusing the CNF semantics of
   Sound.lean unchanged — `asnOf` below is the ONLY new semantic notion.

   Spec-review notes (the property must be the RIGHT one, not just provable):
   * The theorem's CNF is the ACTUAL argument to `check_sat` (`cnf.val`, the
     mathematical list underlying the slice) — not anything derived from the
     bundle. The parser and the bundle format stay untrusted.
   * Acceptance is the exact success value: outer Aeneas `Result.ok` (no
     panic/divergence) wrapping the inner Rust `Ok ()`.
   * The assignment the witness denotes (`asnOf`) is a TOTAL map, so the
     conclusion `cnfHolds (asnOf …) cnf` is a plain satisfying assignment in
     the sense of `Sound.lean`'s `unsat`, and `check_sat_satisfiable` /
     `verdicts_exclusive` follow with no extra semantics. Variables past the
     end of the bitstring read `false`; that default is never load-bearing:
     `clause_satisfied_spec` shows each accepted clause has a WITNESSING
     literal that the kernel actually read (valid, in range, true).
   * Kernel-review finding recorded, not papered over: `clause_satisfied`
     stops at the first true literal, so literals AFTER it in a clause are
     never validated (a `0` / `i32::MIN` / out-of-range literal there is
     accepted). This does not affect soundness — a clause with a true
     literal holds whatever else it contains — but it is why the spec
     speaks of "a witnessing literal", not "every literal in range".
   * `i32::unsigned_abs` (used by `clause_satisfied`, NOT by `check_binding`,
     which goes through the fully-modelled `lit_var`) has no model in the
     pinned Aeneas Std library, so the generated Kernel.lean declares it as
     an opaque `axiom core.num.I32.unsigned_abs : I32 → Result U32`. Nothing
     about it is derivable, so every theorem about `check_sat` is explicitly
     CONDITIONAL on its (obviously true) specification `UnsignedAbsSpec`,
     taken as a hypothesis — never assumed as an axiom here. Consequently
     `#print axioms` on the `check_sat` family lists that opaque function
     symbol besides propext / Classical.choice / Quot.sound (pinned in
     AxiomCheck.lean); `check_binding_sound` is clean. Routing
     `clause_satisfied` through `lit_var` at the Rust source (as the LRAT
     path did for its former externals — see lean/README.md) removes the
     axiom from the model and the hypothesis from these theorems.
-/
-- rivet: verifies VER-039
import Kernel
import Sound

open Aeneas Aeneas.Std Result

namespace kernel.spec

/- ══════════════════════════ SEMANTICS ══════════════════════════ -/

/-- The total assignment a witness bitstring denotes: DIMACS variable `v ≥ 1`
    reads `assignment[v-1]`; variables past the end are `false` (the kernel
    rejects any literal it reads that reaches them — `AssignmentTooShort`). -/
def asnOf (assignment : List Bool) : Asn := fun v => assignment.getD (v - 1) false

/-- `litHolds` is decidable (through `litHolds_iff`), so a binding theorem can
    compare a bit with `decide (litHolds …)`. -/
instance (σ : Asn) (lit : Std.I32) : Decidable (litHolds σ lit) :=
  decidable_of_iff (σ (litVar lit) = polarity lit) (litHolds_iff σ lit).symm

/-- What an accepting scan of a clause certifies: a literal of the clause that
    the kernel actually validated (nonzero, non-`MIN`), read from a real slot
    of an `n`-bit assignment (`1 ≤ |lit| ≤ n`), and found true under `σ`. -/
def witnessed (σ : Asn) (n : Nat) (c : List Std.I32) : Prop :=
  ∃ lit ∈ c, ValidLit lit ∧ litVar lit ≤ n ∧ litHolds σ lit

/-- A witnessed clause holds (the witnessing literal is the disjunct). -/
theorem witnessed_clauseHolds {σ : Asn} {n : Nat} {c : List Std.I32}
    (h : witnessed σ n c) : clauseHolds σ c :=
  let ⟨lit, hmem, _, _, hh⟩ := h
  ⟨lit, hmem, hh⟩

/-- The specification of the one external the model leaves opaque:
    `i32::unsigned_abs` returns `|lit|` as a `u32` (total — it never panics;
    `MIN` maps to `2^31`, which fits). Taken as a HYPOTHESIS by the `check_sat`
    family below; see the header. -/
def UnsignedAbsSpec : Prop :=
  ∀ lit : Std.I32, core.num.I32.unsigned_abs lit ⦃ (u : Std.U32) => u.val = lit.val.natAbs ⦄

/- ═══════════════════════ SHARED ARITHMETIC LEMMAS ═══════════════════════ -/

/-- The two kernel-side literal checks (`lit == 0`, `lit == i32::MIN`) are
    exactly `ValidLit` (same derivation as `clause_has_invalid_literal_spec`). -/
theorem validLit_of_checks (lit : Std.I32) (h0 : ¬ lit = 0#i32)
    (hM : ¬ lit = core.num.I32.MIN) : ValidLit lit := by
  refine ⟨fun h => h0 (by grind), ?_⟩
  have hmm : core.num.I32.MIN.val = -Std.I32.max - 1 := by
    simp [core.num.I32.MIN, I32.rMin, I32.max_eq]
  have hb : core.num.I32.MIN.val ≤ lit.val := by rw [hmm]; scalar_tac
  rcases lt_or_eq_of_le hb with h | h
  · exact h
  · exact absurd (show lit = core.num.I32.MIN by grind) hM

/-- A valid literal's variable is at least 1 (so `var - 1` cannot underflow). -/
theorem litVar_pos (lit : Std.I32) (h : ValidLit lit) : 0 < litVar lit := by
  unfold litVar; exact Int.natAbs_pos.mpr h.1

/-- Reading the witness at a valid, in-range variable is reading the slot. -/
theorem asnOf_eq_getElem (a : List Bool) (v : Nat) (hpos : 0 < v)
    (hle : v ≤ a.length) : asnOf a v = a[v - 1]'(by omega) := by
  unfold asnOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

/-- `litHolds` decided from the slot value and the literal's sign. -/
theorem litHolds_decide (σ : Asn) (lit : Std.I32) (b : Bool) (hσ : σ (litVar lit) = b) :
    decide (litHolds σ lit) = (if 0 < lit.val then b else !b) := by
  have h1 : decide (litHolds σ lit) = decide (σ (litVar lit) = polarity lit) :=
    decide_eq_decide.mpr (litHolds_iff σ lit)
  rw [h1]
  simp only [hσ, polarity]
  by_cases hp : 0 < lit.val
  · cases b <;> simp [hp]
  · cases b <;> simp [hp]

/-- Bit `k` of a natural, as the kernel computes it: `(x >> k) & 1`, i.e.
    `(x >> k) % 2`. -/
theorem testBit_eq_shift_mod (x k : Nat) :
    x.testBit k = decide ((x >>> k) % 2 = 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]

/- ═════════════════════════ check_sat ═════════════════════════ -/

/-- The clause scan: on `Ok true` the clause is witnessed (a validated,
    in-range, true literal was read). Loop invariant: `sat = true` already
    carries a witness. `Ok false` and every `Err` certify nothing (`True`). -/
theorem clause_satisfied_spec (habs : UnsignedAbsSpec)
    (clause : Slice Std.I32) (assignment : Slice Bool) (ci : Std.Usize) :
    kernel.clause_satisfied clause assignment ci ⦃ r => match r with
      | .Ok b => b = true → witnessed (asnOf assignment.val) assignment.val.length clause.val
      | .Err _ => True ⦄ := by
  unfold kernel.clause_satisfied kernel.clause_satisfied_loop
  apply loop.spec_decr_nat
    (measure := fun (p : Bool × Std.Usize) => clause.val.length - p.2.val)
    (inv := fun (p : Bool × Std.Usize) => p.2.val ≤ clause.val.length ∧
      (p.1 = true → witnessed (asnOf assignment.val) assignment.val.length clause.val))
  · rintro ⟨sat, i⟩ ⟨hle, hsat⟩
    unfold kernel.clause_satisfied_loop.body
    dsimp only
    split
    · rename_i hs
      simp only [WP.spec_ok]
      first | exact hsat hs | exact fun _ => hsat hs
    · rename_i hs
      split
      · rename_i hlt
        step as ⟨lit, hlit⟩
        have hmem : lit ∈ clause.val := by rw [hlit]; exact List.getElem_mem _
        split
        · simp
        · split
          · simp
          · rename_i hne0 hneM
            have hvalid : ValidLit lit := validLit_of_checks lit hne0 hneM
            step with (habs lit) as ⟨u, hu⟩
            step with (UScalar.cast_inBounds_spec .Usize u (by scalar_tac)) as ⟨var, hvar⟩
            have hvv : var.val = litVar lit := by rw [hvar, hu]; rfl
            have hvpos : 0 < var.val := by rw [hvv]; exact litVar_pos lit hvalid
            split
            · simp
            · rename_i hinr
              have hvle : var.val ≤ assignment.val.length := by scalar_tac
              step as ⟨i4, hi4⟩
              step as ⟨value, hvalue⟩
              have hσ : asnOf assignment.val (litVar lit) = value := by
                rw [← hvv, asnOf_eq_getElem assignment.val var.val hvpos hvle, hvalue]
                simp only [hi4]
              have hwit : litHolds (asnOf assignment.val) lit →
                  witnessed (asnOf assignment.val) assignment.val.length clause.val :=
                fun hh => ⟨lit, hmem, hvalid, by rw [← hvv]; exact hvle, hh⟩
              have hi1 : i.val + 1 ≤ Std.Usize.max := by scalar_tac
              -- The four-way sign/value branch computing `sat1`.
              split
              · rename_i hpos
                split
                · rename_i hval
                  have hw := hwit (by unfold litHolds; rw [if_pos (by scalar_tac), hσ, hval])
                  step as ⟨i5, hi5⟩
                  and_intros <;> first | exact hw | exact fun _ => hw | scalar_tac
                · split
                  · -- `lit > 0 ∧ lit < 0`: contradictory.
                    exfalso; scalar_tac
                  · step as ⟨i5, hi5⟩
                    and_intros <;> first | scalar_tac
              · rename_i hnpos
                split
                · rename_i hneg
                  split
                  · step as ⟨i5, hi5⟩
                    and_intros <;> first | scalar_tac
                  · rename_i hval
                    have hw := hwit (by
                      unfold litHolds
                      rw [if_neg (by scalar_tac), hσ]
                      simpa using hval)
                    step as ⟨i5, hi5⟩
                    and_intros <;> first | exact hw | exact fun _ => hw | scalar_tac
                · step as ⟨i5, hi5⟩
                  and_intros <;> first | scalar_tac
      · simp
  · exact ⟨by simp, fun h => absurd h (by simp)⟩

/-- The clause loop from index `ci`: on `Ok ()`, every clause is witnessed.
    Invariant: all clauses before `ci` are witnessed. -/
theorem check_sat_loop_spec (habs : UnsignedAbsSpec)
    (cnf : Slice (alloc.vec.Vec Std.I32)) (assignment : Slice Bool) (ci : Std.Usize)
    (hci : ci.val ≤ cnf.val.length)
    (hpre : ∀ c ∈ cnf.val.take ci.val,
      witnessed (asnOf assignment.val) assignment.val.length c.val) :
    kernel.check_sat_loop cnf assignment ci ⦃ r => match r with
      | .Ok () => ∀ c ∈ cnf.val, witnessed (asnOf assignment.val) assignment.val.length c.val
      | .Err _ => True ⦄ := by
  unfold kernel.check_sat_loop
  apply loop.spec_decr_nat
    (measure := fun (i : Std.Usize) => cnf.val.length - i.val)
    (inv := fun (i : Std.Usize) => i.val ≤ cnf.val.length ∧
      ∀ c ∈ cnf.val.take i.val, witnessed (asnOf assignment.val) assignment.val.length c.val)
  · rintro i ⟨hle, hinv⟩
    unfold kernel.check_sat_loop.body
    dsimp only
    split
    · rename_i hlt
      have hil : i.val < cnf.val.length := by scalar_tac
      step as ⟨v, hv⟩
      step with (clause_satisfied_spec habs (alloc.vec.Vec.deref v) assignment i) as ⟨r, hr⟩
      cases r with
      | Ok b =>
        step as ⟨cf, hcf⟩
        simp only [hcf]
        split
        · rename_i hb
          have hwv : witnessed (asnOf assignment.val) assignment.val.length v.val := hr hb
          have hinv' : ∀ c ∈ cnf.val.take (i.val + 1),
              witnessed (asnOf assignment.val) assignment.val.length c.val := by
            rw [List.take_add_one, List.getElem?_eq_getElem hil, ← hv]
            intro c hc
            simp only [Option.toList_some, List.mem_append, List.mem_singleton] at hc
            rcases hc with hc | hc
            · exact hinv c hc
            · rw [hc]; exact hwv
          step as ⟨i3, hi3⟩
          and_intros <;> first | scalar_tac | exact hinv' | (rw [hi3]; exact hinv')
        · simp
      | Err e =>
        step as ⟨cf, hcf⟩
        simp only [hcf,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
        step*
    · rename_i hge
      have hik : i.val = cnf.val.length := by scalar_tac
      rw [hik, List.take_length] at hinv
      exact hinv
  · exact ⟨hci, hpre⟩

/-- Every clause the kernel accepts is witnessed by a literal it actually
    validated and read — the strong form behind `check_sat_sound`. -/
theorem check_sat_witnessed (habs : UnsignedAbsSpec)
    (cnf : Slice (alloc.vec.Vec Std.I32)) (assignment : Slice Bool)
    (h : kernel.check_sat cnf assignment = ok (core.result.Result.Ok ())) :
    ∀ c ∈ cnf.val, witnessed (asnOf assignment.val) assignment.val.length c.val := by
  have hspec := check_sat_loop_spec habs cnf assignment 0#usize (by simp) (by simp)
  unfold kernel.check_sat at h
  rw [h] at hspec
  simpa using hspec

/-- **SAT witness soundness** (TR-038 / TR-044): if the kernel accepts
    `assignment` against `cnf`, the assignment it denotes satisfies every
    clause of the ACTUAL cnf argument (the mathematical list under the slice —
    the parser stays untrusted). Conditional only on the specification of the
    opaque external `i32::unsigned_abs` (see the header). -/
theorem check_sat_sound (habs : UnsignedAbsSpec)
    (cnf : Slice (alloc.vec.Vec Std.I32)) (assignment : Slice Bool)
    (h : kernel.check_sat cnf assignment = ok (core.result.Result.Ok ())) :
    cnfHolds (asnOf assignment.val) (cnf.val.map (fun c => c.val)) := by
  intro c hc
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc
  exact witnessed_clauseHolds (check_sat_witnessed habs cnf assignment h v hv)

/-- Satisfiability by exhibition: an accepted witness refutes `unsat`. -/
theorem check_sat_satisfiable (habs : UnsignedAbsSpec)
    (cnf : Slice (alloc.vec.Vec Std.I32)) (assignment : Slice Bool)
    (h : kernel.check_sat cnf assignment = ok (core.result.Result.Ok ())) :
    ¬ unsat (cnf.val.map (fun c => c.val)) :=
  fun hu => hu (asnOf assignment.val) (check_sat_sound habs cnf assignment h)

/- ═════════════════════════ check_binding ═════════════════════════ -/

/-- The binding loop from bit `k`: on `Ok ()`, every bit `j < |bits|` of
    `value` is the truth value of the signed literal `bits[j]` under the
    witness. Invariant: bits before `k` already agree. `value` is a `u128`,
    so `|bits| ≤ 128` (the kernel's `BindingTooWide` guard) keeps the shift
    in range. -/
theorem check_binding_loop_spec
    (assignment : Slice Bool) (bits : Slice Std.I32) (value : Std.U128) (k : Std.Usize)
    (hw : bits.val.length ≤ 128) (hk : k.val ≤ bits.val.length)
    (hpre : ∀ j (hj : j < bits.val.length), j < k.val →
      value.val.testBit j = decide (litHolds (asnOf assignment.val) bits.val[j])) :
    kernel.check_binding_loop assignment bits value k ⦃ r => match r with
      | .Ok () => ∀ j (hj : j < bits.val.length),
          value.val.testBit j = decide (litHolds (asnOf assignment.val) bits.val[j])
      | .Err _ => True ⦄ := by
  unfold kernel.check_binding_loop
  apply loop.spec_decr_nat
    (measure := fun (i : Std.Usize) => bits.val.length - i.val)
    (inv := fun (i : Std.Usize) => i.val ≤ bits.val.length ∧
      ∀ j (hj : j < bits.val.length), j < i.val →
        value.val.testBit j = decide (litHolds (asnOf assignment.val) bits.val[j]))
  · rintro i ⟨hle, hinv⟩
    unfold kernel.check_binding_loop.body
    dsimp only
    split
    · rename_i hlt
      have hil : i.val < bits.val.length := by scalar_tac
      step as ⟨lit, hlit⟩
      split
      · simp
      · split
        · simp
        · rename_i hne0 hneM
          have hvalid : ValidLit lit := validLit_of_checks lit hne0 hneM
          step with (lit_var_spec lit hvalid) as ⟨var, hvar⟩
          have hvv : var.val = litVar lit := hvar
          have hvpos : 0 < var.val := by rw [hvv]; exact litVar_pos lit hvalid
          split
          · simp
          · rename_i hinr
            have hvle : var.val ≤ assignment.val.length := by scalar_tac
            step as ⟨i2, hi2⟩
            step as ⟨var_value, hvarv⟩
            have hσ : asnOf assignment.val (litVar lit) = var_value := by
              rw [← hvv, asnOf_eq_getElem assignment.val var.val hvpos hvle, hvarv]
              simp only [hi2]
            have hk128 : i.val < 128 := by omega
            step as ⟨i3, hi3, _⟩
            step as ⟨bit, hbit, _⟩
            have hbitv : bit.val = (value.val >>> i.val) % 2 := by
              rw [hbit, UScalar.val_and, hi3, ← Nat.and_one_is_mod]
              simp
            have htb : value.val.testBit i.val = decide (bit.val = 1) := by
              rw [testBit_eq_shift_mod, hbitv]
            have hdec := litHolds_decide (asnOf assignment.val) lit var_value hσ
            -- The invariant extended by the current bit, once it is known to match.
            -- (No `bits[i] = lit` hypothesis is kept in context: together with
            -- `hlit` it would form a rewrite loop for scalar_tac's preprocessing.)
            have hext : value.val.testBit i.val = decide (litHolds (asnOf assignment.val) lit) →
                ∀ j (hj : j < bits.val.length), j < i.val + 1 →
                  value.val.testBit j = decide (litHolds (asnOf assignment.val) bits.val[j]) := by
              intro hm j hj hji
              rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hji) with hlt' | heq
              · exact hinv j hj hlt'
              · subst heq; rw [← hlit]; exact hm
            have hi1 : i.val + 1 ≤ Std.Usize.max := by scalar_tac
            -- The four-way sign/value branch.
            split
            · rename_i hpos
              have hp : (0 : Int) < lit.val := by scalar_tac
              split
              · rename_i hval
                split
                · simp
                · rename_i hb
                  simp only [bne_iff_ne, ne_eq, not_not] at hb
                  have hb1 : bit.val = 1 := by subst hb; rfl
                  have hm : value.val.testBit i.val
                      = decide (litHolds (asnOf assignment.val) lit) := by
                    rw [hdec, if_pos hp, htb, hb1, hval]; decide
                  step as ⟨i4, hi4⟩
                  and_intros <;> first | omega | exact hext hm | (rw [hi4]; exact hext hm)
              · rename_i hval
                split
                · simp
                · rename_i hb
                  simp only [bne_iff_ne, ne_eq, not_not] at hb
                  simp only [Bool.not_eq_true] at hval
                  have hb0 : bit.val = 0 := by subst hb; rfl
                  have hm : value.val.testBit i.val
                      = decide (litHolds (asnOf assignment.val) lit) := by
                    rw [hdec, if_pos hp, htb, hb0, hval]; decide
                  step as ⟨i4, hi4⟩
                  and_intros <;> first | omega | exact hext hm | (rw [hi4]; exact hext hm)
            · rename_i hnpos
              have hp : ¬ (0 : Int) < lit.val := by scalar_tac
              split
              · rename_i hval
                split
                · simp
                · rename_i hb
                  simp only [bne_iff_ne, ne_eq, not_not] at hb
                  have hb0 : bit.val = 0 := by subst hb; rfl
                  have hm : value.val.testBit i.val
                      = decide (litHolds (asnOf assignment.val) lit) := by
                    rw [hdec, if_neg hp, htb, hb0, hval]; decide
                  step as ⟨i4, hi4⟩
                  and_intros <;> first | omega | exact hext hm | (rw [hi4]; exact hext hm)
              · rename_i hval
                split
                · simp
                · rename_i hb
                  simp only [bne_iff_ne, ne_eq, not_not] at hb
                  simp only [Bool.not_eq_true] at hval
                  have hb1 : bit.val = 1 := by subst hb; rfl
                  have hm : value.val.testBit i.val
                      = decide (litHolds (asnOf assignment.val) lit) := by
                    rw [hdec, if_neg hp, htb, hb1, hval]; decide
                  step as ⟨i4, hi4⟩
                  and_intros <;> first | omega | exact hext hm | (rw [hi4]; exact hext hm)
    · rename_i hge
      have hik : i.val = bits.val.length := by scalar_tac
      intro j hj
      exact hinv j hj (by omega)
  · exact ⟨hk, hpre⟩

/-- **Binding soundness** (TR-038 / TR-044): an accepted binding means bit `k`
    of `value` (LSB-first) IS the truth value of the signed literal `bits[k]`
    under the witness — the advertised model is part of the evidence, not
    decoration. No hypothesis on externals: `check_binding` goes through the
    fully-modelled `lit_var`. -/
theorem check_binding_sound
    (assignment : Slice Bool) (bits : Slice Std.I32) (value : Std.U128)
    (h : kernel.check_binding assignment bits value = ok (core.result.Result.Ok ())) :
    ∀ k, (hk : k < bits.val.length) →
      value.val.testBit k = decide (litHolds (asnOf assignment.val) bits.val[k]) := by
  unfold kernel.check_binding at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hw
    have hw' : bits.val.length ≤ 128 := by scalar_tac
    have hspec := check_binding_loop_spec assignment bits value 0#usize hw' (by simp)
      (fun j hj hj0 => absurd hj0 (by simp))
    rw [h] at hspec
    simpa using hspec

/- ═════════════════════ THE TWO VERDICTS ARE EXCLUSIVE ═════════════════════ -/

/-- The two verdict directions are mutually exclusive on the same CNF: no
    `cnf` can have both an accepted LRAT refutation (`lrat_check_sound`) and
    an accepted witness (`check_sat_satisfiable`). `hfit` is the LRAT
    theorem's address-space side condition; `habs` the witness theorem's
    external specification. -/
theorem verdicts_exclusive (habs : UnsignedAbsSpec)
    (cnf : Slice (alloc.vec.Vec Std.I32)) (steps : Slice Step) (assignment : Slice Bool)
    (hfit : cnf.val.length + steps.val.length ≤ Std.Usize.max)
    (hu : kernel.check_steps cnf steps = ok (core.result.Result.Ok ()))
    (hs : kernel.check_sat cnf assignment = ok (core.result.Result.Ok ())) : False :=
  check_sat_satisfiable habs cnf assignment hs (lrat_check_sound cnf steps hfit hu)

end kernel.spec
