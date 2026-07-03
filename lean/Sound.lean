/- Specification and soundness proof for the ordeal-lrat kernel.

   This file is HAND-WRITTEN (unlike Kernel.lean, which regen.sh generates).
   It states what "the checker is sound" means — the semantics of CNF
   satisfiability — and proves the mathematical content of issue #12:
   a PURE restatement of the checker is sound (COMPLETE proof below), and
   the top-level theorem `lrat_check_sound` reduces to the single remaining
   obligation `kernel_refines_pure` (the Aeneas-model-to-pure simulation).

   Spec-review notes (the property must be the RIGHT one, not just provable):
   * The assignment quantifies over ALL total maps from DIMACS variables to
     booleans — no finiteness assumption, no dependence on the kernel's own
     `Assignment` type.
   * Literal semantics follow DIMACS: literal `l` with variable `|l|` holds
     under σ iff σ(|l|) equals the sign of `l`. Literals 0 and i32::MIN are
     rejected KERNEL-SIDE for both the CNF (`load_cnf`) and every
     certificate clause (`apply_add`); at the PURE level literals are
     abstracted to (variable, polarity) and no integer negation occurs, so
     neither needs a special case in the math — they only matter in the
     simulation, where the kernel's validation excludes MIN before `-lit`.
   * The theorem's CNF is the ACTUAL argument to `check_steps` (`cnf.val`,
     the mathematical list underlying the slice) — not anything derived from
     the certificate. This is what makes the parser untrusted.
   * Acceptance is the exact success value: outer Aeneas `Result.ok` (no
     panic/divergence) wrapping the inner Rust `Ok ()`.
-/
import Kernel

open Aeneas Aeneas.Std Result

namespace kernel.spec

/- ══════════════════════════ SEMANTICS ══════════════════════════ -/

/-- A total assignment of DIMACS variables to booleans. -/
abbrev Asn := Nat → Bool

/-- The DIMACS variable of a literal: its absolute value. -/
def litVar (lit : Std.I32) : Nat := lit.val.natAbs

/-- Literal semantics: a positive literal holds when its variable is true,
    a negative one when its variable is false. -/
def litHolds (σ : Asn) (lit : Std.I32) : Prop :=
  if 0 < lit.val then σ (litVar lit) = true else σ (litVar lit) = false

/-- Clause semantics: a disjunction — some literal holds. (The empty clause
    holds under no assignment.) -/
def clauseHolds (σ : Asn) (c : List Std.I32) : Prop :=
  ∃ lit ∈ c, litHolds σ lit

/-- CNF semantics: a conjunction — every clause holds. -/
def cnfHolds (σ : Asn) (cnf : List (List Std.I32)) : Prop :=
  ∀ c ∈ cnf, clauseHolds σ c

/-- Unsatisfiability: no assignment satisfies the CNF. -/
def unsat (cnf : List (List Std.I32)) : Prop :=
  ∀ σ : Asn, ¬ cnfHolds σ cnf

/-- One clause is semantically implied by a CNF. -/
def implies (cnf : List (List Std.I32)) (c : List Std.I32) : Prop :=
  ∀ σ : Asn, cnfHolds σ cnf → clauseHolds σ c

/- ═════════════════════ THE PURE CHECKER ═════════════════════════
   A string-free, monad-free restatement of the kernel over plain lists.
   Literals are handled through (variable, polarity) only — no integer
   negation — and the pure checker REJECTS wherever the kernel errors,
   panics, or asserts. Its soundness is proved COMPLETELY below; the
   Aeneas model is then connected by one simulation lemma. -/

/-- The polarity of a literal: `true` for positive. -/
def polarity (lit : Std.I32) : Bool := decide (0 < lit.val)

/-- `litHolds`, in variable/polarity form. -/
theorem litHolds_iff (σ : Asn) (lit : Std.I32) :
    litHolds σ lit ↔ σ (litVar lit) = polarity lit := by
  unfold litHolds polarity
  split <;> rename_i h
  · simp [h]
  · simp [h]

/-- Literals with the same underlying value have the same semantics. -/
theorem litHolds_val_congr (σ : Asn) {a b : Std.I32} (h : a.val = b.val) :
    litHolds σ a ↔ litHolds σ b := by
  unfold litHolds litVar
  rw [h]

/-- A partial assignment of variables. -/
abbrev PAsn := Nat → Option Bool

/-- The empty partial assignment. -/
def pEmpty : PAsn := fun _ => none

/-- The (partial) truth value of a literal. -/
def pvalue (A : PAsn) (lit : Std.I32) : Option Bool :=
  (A (litVar lit)).map (fun b => b == polarity lit)

/-- Make `lit` true; `none` = conflict (it was already false). -/
def pAssignLit (A : PAsn) (lit : Std.I32) : Option PAsn :=
  match A (litVar lit) with
  | some b => if b == polarity lit then some A else none
  | none => some (fun v => if v = litVar lit then some (polarity lit) else A v)

/-- Make `lit` false (assume its negation); `none` = conflict. -/
def pAssumeFalse (A : PAsn) (lit : Std.I32) : Option PAsn :=
  match A (litVar lit) with
  | some b => if b == !polarity lit then some A else none
  | none =>
    some (fun v => if v = litVar lit then some (!polarity lit) else A v)

/-- Assume the negation of every literal of a clause; `none` = conflict
    while assuming (the clause is a tautology). -/
def pAssumeNeg (A : PAsn) : List Std.I32 → Option PAsn
  | [] => some A
  | lit :: rest =>
    match pAssumeFalse A lit with
    | none => none
    | some A' => pAssumeNeg A' rest

/-- Distinct-unassigned-literal collection (deduped by value), or `none`
    if some literal is already true (a satisfied hint). -/
def pUnassigned (A : PAsn) (acc : List Std.I32) :
    List Std.I32 → Option (List Std.I32)
  | [] => some acc
  | lit :: rest =>
    match pvalue A lit with
    | some true => none
    | some false => pUnassigned A acc rest
    | none =>
      if acc.any (fun l => l.val == lit.val) then pUnassigned A acc rest
      else pUnassigned A (acc ++ [lit]) rest

/-- One RUP propagation pass; `true` = a hint falsified (step verified). -/
def pRupGo (clauses : List (Option (List Std.I32))) (A : PAsn) :
    List Nat → Bool
  | [] => false
  | h :: rest =>
    match (if h = 0 then none else clauses[h - 1]?).join with
    | none => false -- unknown or dead id
    | some cl =>
      match pUnassigned A [] cl with
      | none => false -- satisfied hint
      | some [] => true -- falsified: conflict reached, step verified
      | some [u] =>
        match pAssignLit A u with
        | some A' => pRupGo clauses A' rest
        | none => false -- unreachable (u unassigned); reject anyway
      | some _ => false -- two or more unassigned literals

/-- Pure `check_rup`. -/
def pCheckRup (clauses : List (Option (List Std.I32)))
    (c : List Std.I32) (hints : List Nat) : Bool :=
  match pAssumeNeg pEmpty c with
  | none => true -- tautology: trivially implied
  | some A => pRupGo clauses A hints

/-- Pure deletion; `none` = reject (unknown or dead id). -/
def pDelete (clauses : List (Option (List Std.I32))) :
    List Nat → Option (List (Option (List Std.I32)))
  | [] => some clauses
  | h :: rest =>
    match (if h = 0 then none else clauses[h - 1]?).join with
    | none => none
    | some _ => pDelete (clauses.set (h - 1) none) rest

/-- A parsed certificate step, pure form. -/
inductive PStep where
  | add (id : Nat) (clause : List Std.I32) (hints : List Nat)
  | del (ids : List Nat)

/-- Pure `check_steps` over a loaded clause list: `true` iff a RUP-verified
    addition of the empty clause is reached. -/
def pChecks (clauses : List (Option (List Std.I32))) : List PStep → Bool
  | [] => false
  | .del ids :: rest =>
    match pDelete clauses ids with
    | none => false
    | some clauses' => pChecks clauses' rest
  | .add id c hints :: rest =>
    if id = clauses.length + 1 ∧ pCheckRup clauses c hints then
      if c.isEmpty then true else pChecks (clauses ++ [some c]) rest
    else false

/-- The pure checker, end to end. -/
def pCheckSteps (cnf : List (List Std.I32)) (steps : List PStep) : Bool :=
  pChecks (cnf.map some) steps

/- ═════════════════════ SOUNDNESS OF THE PURE CHECKER ═══════════════════ -/

/-- σ agrees with everything the partial assignment has decided. -/
def agrees (σ : Asn) (A : PAsn) : Prop :=
  ∀ v b, A v = some b → σ v = b

theorem agrees_empty (σ : Asn) : agrees σ pEmpty := by
  intro v b h; simp [pEmpty] at h

theorem pvalue_true (σ : Asn) (A : PAsn) (lit : Std.I32)
    (hA : agrees σ A) (h : pvalue A lit = some true) : litHolds σ lit := by
  rw [litHolds_iff]
  unfold pvalue at h
  cases hv : A (litVar lit) with
  | none => rw [hv] at h; simp at h
  | some b =>
    rw [hv] at h
    simp only [Option.map_some, Option.some_inj] at h
    rw [hA _ _ hv]
    exact eq_of_beq h

theorem pvalue_false (σ : Asn) (A : PAsn) (lit : Std.I32)
    (hA : agrees σ A) (h : pvalue A lit = some false) : ¬ litHolds σ lit := by
  rw [litHolds_iff]
  unfold pvalue at h
  cases hv : A (litVar lit) with
  | none => rw [hv] at h; simp at h
  | some b =>
    rw [hv] at h
    simp only [Option.map_some, Option.some_inj] at h
    rw [hA _ _ hv]
    intro hc
    rw [hc, beq_self_eq_true] at h
    cases h

theorem agrees_pAssignLit (σ : Asn) {A A' : PAsn} (lit : Std.I32)
    (hA : agrees σ A) (hlit : litHolds σ lit)
    (h : pAssignLit A lit = some A') : agrees σ A' := by
  unfold pAssignLit at h
  cases hv : A (litVar lit) with
  | some b =>
    simp only [hv] at h
    split at h
    · cases h; exact hA
    · cases h
  | none =>
    simp only [hv, Option.some.injEq] at h
    subst h
    intro v b hb
    by_cases hveq : v = litVar lit
    · subst hveq
      simp at hb
      subst hb
      exact (litHolds_iff σ lit).mp hlit
    · simp only [if_neg hveq] at hb
      exact hA v b hb

theorem agrees_pAssumeFalse (σ : Asn) {A A' : PAsn} (lit : Std.I32)
    (hA : agrees σ A) (hlit : ¬ litHolds σ lit)
    (h : pAssumeFalse A lit = some A') : agrees σ A' := by
  unfold pAssumeFalse at h
  cases hv : A (litVar lit) with
  | some b =>
    simp only [hv] at h
    split at h
    · cases h; exact hA
    · cases h
  | none =>
    simp only [hv, Option.some.injEq] at h
    subst h
    intro v b hb
    by_cases hveq : v = litVar lit
    · subst hveq
      simp at hb
      rw [litHolds_iff] at hlit
      cases hσ : σ (litVar lit) <;> cases hp : polarity lit <;>
        simp_all
    · simp only [if_neg hveq] at hb
      exact hA v b hb

theorem agrees_pAssumeNeg (σ : Asn) {A A' : PAsn} {c : List Std.I32}
    (hA : agrees σ A) (hc : ¬ clauseHolds σ c)
    (h : pAssumeNeg A c = some A') : agrees σ A' := by
  induction c generalizing A with
  | nil => cases h; exact hA
  | cons lit rest ih =>
    unfold pAssumeNeg at h
    cases hf : pAssumeFalse A lit with
    | none => rw [hf] at h; cases h
    | some A1 =>
      rw [hf] at h
      have hnl : ¬ litHolds σ lit := fun hl =>
        hc ⟨lit, List.mem_cons_self .., hl⟩
      have hA1 := agrees_pAssumeFalse σ lit hA hnl hf
      exact ih hA1 (fun ⟨l, hl, hh⟩ =>
        hc ⟨l, List.mem_cons_of_mem _ hl, hh⟩) h

/-- A conflict while assuming a clause's negation refutes any σ that does
    not already satisfy the clause: the clause is a tautology. -/
theorem pAssumeNeg_none (σ : Asn) {A : PAsn} {c : List Std.I32}
    (hA : agrees σ A) (h : pAssumeNeg A c = none)
    (hc : ¬ clauseHolds σ c) : False := by
  induction c generalizing A with
  | nil => cases h
  | cons lit rest ih =>
    unfold pAssumeNeg at h
    cases hf : pAssumeFalse A lit with
    | none =>
      -- Conflict: the variable is already assigned to `polarity lit`,
      -- so (by agreement) σ makes `lit` hold — contradiction.
      unfold pAssumeFalse at hf
      cases hv : A (litVar lit) with
      | none => simp only [hv] at hf; cases hf
      | some b =>
        simp only [hv] at hf
        split at hf
        · cases hf
        · rename_i hb
          have hbpol : b = polarity lit := by
            cases hbb : b <;> cases hp : polarity lit <;> simp_all
          exact hc ⟨lit, List.mem_cons_self ..,
            (litHolds_iff σ lit).mpr ((hA _ _ hv).trans hbpol)⟩
    | some A1 =>
      rw [hf] at h
      have hnl : ¬ litHolds σ lit := fun hl =>
        hc ⟨lit, List.mem_cons_self .., hl⟩
      have hA1 := agrees_pAssumeFalse σ lit hA hnl hf
      exact ih hA1 h (fun ⟨l, hl, hh⟩ =>
        hc ⟨l, List.mem_cons_of_mem _ hl, hh⟩)

/-- Every live clause of the working list is implied by the CNF. -/
def livesImplied (cnf : List (List Std.I32))
    (clauses : List (Option (List Std.I32))) : Prop :=
  ∀ cl, some cl ∈ clauses → implies cnf cl

/-- The full accumulator spec for `pUnassigned`: on success, the output's
    literals are unassigned, the accumulator embeds into the output, and
    every clause literal is definitely false or value-equal to an output
    literal. -/
theorem pUnassigned_spec (A : PAsn) (cl : List Std.I32) :
    ∀ (acc out : List Std.I32),
    (∀ x ∈ acc, pvalue A x = none) →
    pUnassigned A acc cl = some out →
    (∀ x ∈ out, pvalue A x = none)
    ∧ (∀ x ∈ acc, x ∈ out)
    ∧ (∀ l ∈ cl, pvalue A l = some false ∨ ∃ x ∈ out, l.val = x.val) := by
  induction cl with
  | nil =>
    intro acc out hacc h
    cases h
    exact ⟨hacc, fun x hx => hx, by simp⟩
  | cons lit rest ih =>
    intro acc out hacc h
    unfold pUnassigned at h
    cases hv : pvalue A lit with
    | some b =>
      cases b with
      | true => simp only [hv] at h; cases h
      | false =>
        simp only [hv] at h
        obtain ⟨hout, hemb, hall⟩ := ih acc out hacc h
        refine ⟨hout, hemb, fun l hl => ?_⟩
        rcases List.mem_cons.mp hl with rfl | hl'
        · exact Or.inl hv
        · exact hall l hl'
    | none =>
      simp only [hv] at h
      split at h
      · rename_i hdup
        obtain ⟨hout, hemb, hall⟩ := ih acc out hacc h
        refine ⟨hout, hemb, fun l hl => ?_⟩
        rcases List.mem_cons.mp hl with rfl | hl'
        · simp only [List.any_eq_true, beq_iff_eq] at hdup
          obtain ⟨x, hx, hxv⟩ := hdup
          exact Or.inr ⟨x, hemb x hx, hxv.symm⟩
        · exact hall l hl'
      · have hacc' : ∀ x ∈ acc ++ [lit], pvalue A x = none := by
          intro x hx
          rcases List.mem_append.mp hx with hx' | hx'
          · exact hacc x hx'
          · simp only [List.mem_singleton] at hx'
            subst hx'; exact hv
        obtain ⟨hout, hemb, hall⟩ := ih (acc ++ [lit]) out hacc' h
        refine ⟨hout,
          fun x hx => hemb x (List.mem_append.mpr (Or.inl hx)),
          fun l hl => ?_⟩
        rcases List.mem_cons.mp hl with rfl | hl'
        · exact Or.inr ⟨l, hemb l (by simp), rfl⟩
        · exact hall l hl'

/-- The RUP propagation loop cannot report a conflict when a satisfying
    assignment agrees with the partial assignment. -/
theorem pRupGo_no_conflict (cnf : List (List Std.I32))
    (clauses : List (Option (List Std.I32))) (σ : Asn)
    (hlive : livesImplied cnf clauses) (hσ : cnfHolds σ cnf) :
    ∀ (hints : List Nat) (A : PAsn), agrees σ A →
    pRupGo clauses A hints = true → False := by
  intro hints
  induction hints with
  | nil => intro A _ h; cases h
  | cons hd rest ih =>
    intro A hA h
    unfold pRupGo at h
    cases hget : (if hd = 0 then none else clauses[hd - 1]?).join with
    | none => simp only [hget] at h; cases h
    | some cl =>
      simp only [hget] at h
      -- The hint clause is a live member, hence implied, hence σ-satisfied.
      have hmem : some cl ∈ clauses := by
        by_cases h0 : hd = 0
        · simp [h0] at hget
        · rw [if_neg h0] at hget
          cases ho : clauses[hd - 1]? with
          | none => simp [ho] at hget
          | some oc =>
            simp [ho] at hget
            rw [hget] at ho
            exact List.mem_of_getElem? ho
      have hclσ : clauseHolds σ cl := hlive cl hmem σ hσ
      cases hun : pUnassigned A [] cl with
      | none => simp only [hun] at h; cases h
      | some out =>
        simp only [hun] at h
        obtain ⟨hout, _, hall⟩ :=
          pUnassigned_spec A cl [] out (by simp) hun
        obtain ⟨l, hl, hh⟩ := hclσ
        cases out with
        | nil =>
          -- Falsified hint: every literal fails under σ — contradiction.
          rcases hall l hl with hfalse | ⟨x, hx, _⟩
          · exact pvalue_false σ A l hA hfalse hh
          · cases hx
        | cons u tl =>
          cases tl with
          | cons u2 rest => simp at h  -- 2+ unassigned ⇒ false = true
          | nil =>
            -- Unit: the σ-true literal must be value-equal to u.
            simp only at h
            cases hassign : pAssignLit A u with
            | none => simp only [hassign] at h; cases h
            | some A' =>
              simp only [hassign] at h
              have hu : litHolds σ u := by
                rcases hall l hl with hfalse | ⟨x, hx, hval⟩
                · exact absurd hh (pvalue_false σ A l hA hfalse)
                · simp only [List.mem_singleton] at hx
                  subst hx
                  exact (litHolds_val_congr σ hval).mp hh
              exact ih A' (agrees_pAssignLit σ u hA hu hassign) h

/-- Soundness of the pure RUP check: an accepted addition is implied. -/
theorem pCheckRup_sound (cnf : List (List Std.I32))
    (clauses : List (Option (List Std.I32)))
    (c : List Std.I32) (hints : List Nat)
    (hlive : livesImplied cnf clauses)
    (h : pCheckRup clauses c hints = true) : implies cnf c := by
  intro σ hσ
  by_contra hc
  unfold pCheckRup at h
  cases hneg : pAssumeNeg pEmpty c with
  | none => exact pAssumeNeg_none σ (agrees_empty σ) hneg hc
  | some A =>
    rw [hneg] at h
    exact pRupGo_no_conflict cnf clauses σ hlive hσ hints A
      (agrees_pAssumeNeg σ (agrees_empty σ) hc hneg) h

/-- Deletion only shrinks the live set. -/
theorem livesImplied_pDelete (cnf : List (List Std.I32)) :
    ∀ (ids : List Nat) (clauses clauses' : List (Option (List Std.I32))),
    livesImplied cnf clauses → pDelete clauses ids = some clauses' →
    livesImplied cnf clauses' := by
  intro ids
  induction ids with
  | nil => intro clauses clauses' hlive h; cases h; exact hlive
  | cons hd rest ih =>
    intro clauses clauses' hlive h
    unfold pDelete at h
    cases hget : (if hd = 0 then none else clauses[hd - 1]?).join with
    | none => simp only [hget] at h; cases h
    | some _ =>
      simp only [hget] at h
      refine ih _ _ (fun cl hcl => ?_) h
      rcases List.mem_or_eq_of_mem_set hcl with hcl' | hcl'
      · exact hlive cl hcl'
      · cases hcl'

/-- The main induction: an accepting run over implied live clauses refutes
    every assignment. -/
theorem pChecks_sound (cnf : List (List Std.I32)) :
    ∀ (steps : List PStep) (clauses : List (Option (List Std.I32))),
    livesImplied cnf clauses → pChecks clauses steps = true →
    unsat cnf := by
  intro steps
  induction steps with
  | nil => intro clauses _ h; cases h
  | cons st rest ih =>
    intro clauses hlive h
    cases st with
    | del ids =>
      unfold pChecks at h
      cases hdel : pDelete clauses ids with
      | none => rw [hdel] at h; cases h
      | some clauses' =>
        rw [hdel] at h
        exact ih clauses' (livesImplied_pDelete cnf ids clauses clauses'
          hlive hdel) h
    | add id c hints =>
      unfold pChecks at h
      split at h
      · rename_i hcond
        have himpl : implies cnf c :=
          pCheckRup_sound cnf clauses c hints hlive hcond.2
        split at h
        · -- The verified addition is the EMPTY clause: unsat.
          rename_i hempty
          intro σ hσ
          obtain ⟨l, hl, _⟩ := himpl σ hσ
          rw [List.isEmpty_iff.mp hempty] at hl
          cases hl
        · refine ih (clauses ++ [some c]) (fun cl hcl => ?_) h
          rcases List.mem_append.mp hcl with hcl' | hcl'
          · exact hlive cl hcl'
          · simp only [List.mem_singleton, Option.some_inj] at hcl'
            subst hcl'; exact himpl
      · cases h

/-- **Soundness of the pure checker** — the mathematical content of #12,
    fully machine-checked. -/
theorem pure_check_sound (cnf : List (List Std.I32)) (steps : List PStep)
    (h : pCheckSteps cnf steps = true) : unsat cnf := by
  refine pChecks_sound cnf steps (cnf.map some) (fun cl hcl => ?_) h
  have : cl ∈ cnf := by
    rcases List.mem_map.mp hcl with ⟨c, hc, hceq⟩
    cases hceq; exact hc
  exact fun σ hσ => hσ cl this

/- ═════════════════════ THE BRIDGE TO THE AENEAS MODEL ═══════════════════ -/

/- The simulation is proved bottom-up over the generated monadic code with
   the Aeneas WP idiom, established and verified here on the first leaf:

     apply loop.spec_decr_nat (measure := …) (inv := …)
     · intro <state> <hinv>; unfold <body>; dsimp only
       step / step as ⟨…⟩ / split      -- one per monadic op / branch
       … <;> scalar_tac                 -- discharge Usize/index side-goals
     · <initial invariant>

   `chil_total` below is the first `sorry`-free building block — the
   totality of the certificate/CNF literal check, needed by both the
   `load_cnf` and `apply_add` refinements. The remaining functions
   (`load_cnf`, `apply_delete`, `check_rup` [with the `Vec`-Assignment ↔
   `PAsn` relation], `apply_add`, `check_steps_loop`) follow the same
   template and compose into `kernel_refines_pure`; see issue #12 for the
   decomposition. -/

/-- First verified simulation leaf: `clause_has_invalid_literal` always
    returns (never fails / diverges). Used to `step` past the literal check
    in `load_cnf` / `apply_add` on the accepting path. -/
theorem chil_total (clause : Slice Std.I32) :
    kernel.clause_has_invalid_literal clause ⦃ _ => True ⦄ := by
  unfold kernel.clause_has_invalid_literal kernel.clause_has_invalid_literal_loop
  apply loop.spec_decr_nat
    (measure := fun i => clause.length - i.val)
    (inv := fun i => i.val ≤ clause.length)
  · intro i hi
    unfold kernel.clause_has_invalid_literal_loop.body
    dsimp only
    split
    · rename_i hlt
      step as ⟨lit, hlit⟩
      split
      · simp
      · split
        · simp
        · step as ⟨i3, hi3⟩
          refine ⟨?_, ?_⟩ <;> scalar_tac
    · simp
  · simp

/-- The scalar clone of an `I32` is the identity. -/
theorem clonei32_id (x : Std.I32) : core.clone.CloneI32.clone x = ok x := by
  simp [core.clone.CloneI32]

/-- Cloning a `Vec I32` returns an equal vector. -/
theorem clonevec_id (v : alloc.vec.Vec Std.I32) :
    alloc.vec.CloneVec.clone core.clone.CloneI32 v ⦃ v' => v = v' ⦄ := by
  unfold alloc.vec.CloneVec.clone
  exact Slice.clone_spec (fun x _ => clonei32_id x)

/-- Second full simulation leaf: `load_cnf` produces the CNF mapped to
    `some` (Vec vs List bridged by mapping `.val`). The loop invariant
    carries `clauses.length = i` so the `push` bound and the take-prefix
    map-close are both immediate. -/
theorem load_cnf_refines (cnf : Slice (alloc.vec.Vec Std.I32)) :
    kernel.load_cnf cnf ⦃ r => match r with
      | .Ok cls => cls.val.map (Option.map (·.val)) = (cnf.val.map (·.val)).map some
      | .Err _ => True ⦄ := by
  unfold kernel.load_cnf kernel.load_cnf_loop
  apply loop.spec_decr_nat
    (measure := fun (p : alloc.vec.Vec (Option (alloc.vec.Vec Std.I32)) × Std.Usize) =>
      cnf.length - p.2.val)
    (inv := fun (p : alloc.vec.Vec (Option (alloc.vec.Vec Std.I32)) × Std.Usize) =>
      p.2.val ≤ cnf.length ∧ p.1.val.length = p.2.val ∧
      p.1.val.map (Option.map (·.val)) = ((cnf.val.take p.2.val).map (·.val)).map some)
  · rintro ⟨clauses, i⟩ ⟨hle, hlen, hmap⟩
    unfold kernel.load_cnf_loop.body
    dsimp only
    split
    · rename_i hlt
      step as ⟨v, hv⟩
      step with chil_total
      split
      · simp
      · step with clonevec_id as ⟨vc, hvc⟩
        step as ⟨cls1, hcls1⟩
        step as ⟨i3, hi3⟩
        refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
        · rw [hcls1]; simp only [List.length_append, List.length_singleton, hlen]
          scalar_tac
        · rw [show i3.val = i.val + 1 by scalar_tac, hcls1]
          simp only [List.map_append, hmap, ← hvc, hv]
          simp_lists [List.take_add_one]
          have hb : i.val < cnf.val.length := by scalar_tac
          rw [List.getElem?_eq_getElem hb]
          simp only [Option.toList_some, List.map_cons, List.map_nil,
            List.map_append, Option.map_some, Function.comp_apply]
    · rename_i hge
      have hik : i.val = cnf.val.length := by
        simp only [Slice.length] at *; scalar_tac
      simp [hmap, hik]
  · exact ⟨by simp, by simp, by simp⟩

/-- The pure image of a kernel step. -/
def stepToPure : Step → PStep
  | .Add id clause hints => .add id.val clause.val (hints.val.map (·.val))
  | .Delete ids => .del (ids.val.map (·.val))

/-- THE remaining obligation of issue #12: an accepting run of the Aeneas
    model is an accepting run of the pure checker on the same data. This
    is a simulation argument over the generated monadic code (Aeneas
    `progress` tactic + its loop lemmas) — mechanical in character, with
    no further mathematical content.

    OPEN OBLIGATION: the `sorry` below is the tracked, deliberate gap —
    this library is NOT a default build target, and nothing in CI claims
    the theorem is discharged while it remains. -/
theorem kernel_refines_pure
    (cnf : Slice (alloc.vec.Vec Std.I32)) (steps : Slice Step)
    (h : kernel.check_steps cnf steps = ok (core.result.Result.Ok ())) :
    pCheckSteps (cnf.val.map (fun c => c.val))
      (steps.val.map stepToPure) = true := by
  sorry

/-- **The soundness theorem** (issue #12, TR-013/FEAT-002): if the kernel
    accepts a step list against `cnf`, then `cnf` is unsatisfiable.
    Proved from the fully-verified pure soundness plus the simulation
    obligation above. -/
theorem lrat_check_sound
    (cnf : Slice (alloc.vec.Vec Std.I32)) (steps : Slice Step)
    (h : kernel.check_steps cnf steps = ok (core.result.Result.Ok ())) :
    unsat (cnf.val.map (fun c => c.val)) :=
  pure_check_sound _ _ (kernel_refines_pure cnf steps h)

end kernel.spec
