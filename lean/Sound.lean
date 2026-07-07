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

/-- Project the Aeneas clause store (a slice/vector of optional clause
    vectors) to the pure checker's clause list (optional literal lists). A
    deleted slot (`none`) maps to `none`; a live clause maps to its literals. -/
def projClauses (s : List (Option (alloc.vec.Vec Std.I32))) :
    List (Option (List Std.I32)) :=
  s.map (Option.map (·.val))

/-- `get_live` accepts exactly the live-slot condition the pure guard uses:
    on `.Ok`, `id` is a valid 1-based index whose slot is a present clause,
    i.e. `projClauses`'s `(if id=0 …)[id-1]?.join` is `some`. -/
theorem get_live_spec
    (clauses : Slice (Option (alloc.vec.Vec Std.I32))) (id step : Std.Usize) :
    kernel.get_live clauses id step ⦃ r => match r with
      | .Ok _ => 0 < id.val ∧ id.val ≤ clauses.val.length ∧
          (projClauses clauses.val)[id.val - 1]?.join.isSome
      | .Err _ => True ⦄ := by
  unfold kernel.get_live
  split
  · simp
  · rename_i hid0
    dsimp only
    split
    · simp
    · rename_i hle
      step as ⟨i1, hi1⟩
      step as ⟨o, ho⟩
      cases o with
      | none => simp
      | some clause =>
        have hid : 0 < id.val := by scalar_tac
        have hlen : id.val ≤ clauses.val.length := by scalar_tac
        refine ⟨hid, hlen, ?_⟩
        rw [show id.val - 1 = i1.val from hi1.symm]
        have hbi : i1.val < (projClauses clauses.val).length := by
          simp only [projClauses, List.length_map]; scalar_tac
        rw [List.getElem?_eq_getElem hbi]
        simp [Option.join, projClauses, List.getElem_map, ← ho]

/-- `pDelete` over a list ending in one more id folds through the prefix. -/
theorem pDelete_append (l : List (Option (List Std.I32))) (xs : List Nat)
    (x : Nat) :
    pDelete l (xs ++ [x]) = (pDelete l xs).bind (fun l' => pDelete l' [x]) := by
  induction xs generalizing l with
  | nil => simp [pDelete]
  | cons h t ih =>
    rw [List.cons_append]
    simp only [pDelete]
    split
    · rfl
    · exact ih _

/-- Projecting after a slot deletion commutes with deleting in the projection
    (a deleted slot maps to `none` either way). -/
theorem projClauses_set (l : List (Option (alloc.vec.Vec Std.I32))) (n : Nat) :
    projClauses (l.set n none) = (projClauses l).set n none := by
  simp only [projClauses, List.map_set, Option.map_none]

/-- Third simulation leaf: `apply_delete` refines `pDelete`. On the accepting
    path (inner `Ok ()`), the returned store's projection is exactly what
    `pDelete` computes from the original store and the id list. -/
theorem apply_delete_refines
    (clauses : Slice (Option (alloc.vec.Vec Std.I32))) (ids : Slice Std.Usize)
    (step : Std.Usize) :
    kernel.apply_delete clauses ids step ⦃ r => match r.1 with
      | .Ok () =>
          pDelete (projClauses clauses.val) (ids.val.map (·.val))
            = some (projClauses r.2.val)
      | .Err _ => True ⦄ := by
  unfold kernel.apply_delete kernel.apply_delete_loop
  apply loop.spec_decr_nat
    (measure := fun (p : Slice (Option (alloc.vec.Vec Std.I32)) × Std.Usize) =>
      ids.length - p.2.val)
    (inv := fun (p : Slice (Option (alloc.vec.Vec Std.I32)) × Std.Usize) =>
      p.2.val ≤ ids.length ∧ p.1.val.length = clauses.val.length ∧
      pDelete (projClauses clauses.val) ((ids.val.take p.2.val).map (·.val))
        = some (projClauses p.1.val))
  · rintro ⟨cls, i⟩ ⟨hle, hlen, hdel⟩
    unfold kernel.apply_delete_loop.body
    dsimp only
    split
    · rename_i hlt
      step as ⟨id, hid⟩
      step with get_live_spec as ⟨r, hr⟩
      cases r with
      | Ok s =>
        obtain ⟨hpos, hidlen, hjoin⟩ := hr
        step as ⟨cf, hcf⟩
        simp only [hcf]
        step as ⟨i2, hi2⟩
        step as ⟨o, back, hback, hbk⟩
        simp only [kernel.clear_slot]
        step as ⟨i3, hi3⟩
        have hil : i.val < ids.val.length := by scalar_tac
        refine ⟨by scalar_tac, ?_, ?_⟩
        · rw [hbk, Slice.set_val_eq, List.length_set]; exact hlen
        · have htake : (ids.val.take i3.val).map (fun x => x.val)
              = (ids.val.take i.val).map (fun x => x.val) ++ [id.val] := by
            rw [show i3.val = i.val + 1 by scalar_tac, List.take_add_one,
              List.getElem?_eq_getElem hil]
            simp [← hid]
          rw [htake, pDelete_append, hdel]
          obtain ⟨cl, hcl⟩ := Option.isSome_iff_exists.mp hjoin
          rw [hbk]
          simp only [Option.bind, pDelete, if_neg (show ¬ id.val = 0 by omega),
            hcl, Slice.set_val_eq, projClauses_set, hi2]
          exact ⟨trivial, by scalar_tac⟩
      | Err e =>
        step as ⟨cf, hcf⟩
        simp [hcf,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame]
    · rename_i hge
      have hik : i.val = ids.val.length := by scalar_tac
      simp only [hik, List.take_length] at hdel
      simp [hdel]
  · exact ⟨by simp, by rfl, by simp [pDelete]⟩

/- ═══════════════ THE check_rup STACK: Assignment ↔ PAsn ══════════════ -/

/-- The pure image of a kernel `Assignment`: a variable's partial value is its
    in-range slot, `none` past the end of the value vector. -/
def RelAsn (Ak : kernel.Assignment) (Ap : PAsn) : Prop :=
  ∀ v : Nat, Ap v = (Ak.values.val[v]?).join

/-- A literal the kernel accepts: nonzero and not `INT_MIN`, so `-lit` is safe
    and `natAbs` round-trips. Guaranteed by `clause_has_invalid_literal`. -/
def ValidLit (lit : Std.I32) : Prop :=
  lit.val ≠ 0 ∧ core.num.I32.MIN.val < lit.val

/-- `lit_var` computes the DIMACS variable `|lit|` for a valid literal. -/
theorem lit_var_spec (lit : Std.I32) (h : ValidLit lit) :
    kernel.lit_var lit ⦃ (var : Std.Usize) => var.val = lit.val.natAbs ⦄ := by
  unfold kernel.lit_var
  split
  · rename_i hpos
    have hb : 0 ≤ lit.val ∧ lit.val ≤ UScalar.max .Usize := ⟨by scalar_tac, by scalar_tac⟩
    have hc := IScalar.hcast_inBounds_spec .Usize lit hb
    simp only [lift, WP.spec_ok] at hc ⊢
    scalar_tac
  · rename_i hneg
    step as ⟨i, hi⟩
    have hb : 0 ≤ i.val ∧ i.val ≤ UScalar.max .Usize := ⟨by scalar_tac, by scalar_tac⟩
    have hc := IScalar.hcast_inBounds_spec .Usize i hb
    simp only [lift, WP.spec_ok] at hc ⊢
    scalar_tac

/-- `Assignment.value` computes the partial truth value of a literal, matching
    the pure `pvalue`. -/
theorem value_refines (Ak : kernel.Assignment) (Ap : PAsn) (lit : Std.I32)
    (hrel : RelAsn Ak Ap) (hvalid : ValidLit lit) :
    Ak.value lit ⦃ (o : Option Bool) => o = pvalue Ap lit ⦄ := by
  unfold kernel.Assignment.value
  step with (lit_var_spec lit hvalid) as ⟨var, hvar⟩
  have hvv : litVar lit = var.val := hvar.symm
  have hr := hrel (litVar lit)
  split
  · rename_i hge
    have hn : Ap (litVar lit) = none := by
      rw [hr, List.getElem?_eq_none (by rw [hvv]; scalar_tac)]; rfl
    simp [pvalue, hn]
  · rename_i hlt
    step as ⟨o, ho⟩
    have hidx : Ak.values.val[var.val]? = some o := by
      rw [List.getElem?_eq_getElem (show var.val < Ak.values.val.length by scalar_tac)]
      exact congrArg some ho.symm
    have hs : Ap (litVar lit) = o := by rw [hr, hvv, hidx]; rfl
    cases o with
    | none => simp [pvalue, hs]
    | some b =>
      dsimp only
      by_cases hp : lit > 0#i32
      · rw [if_pos hp]
        have hpol : polarity lit = true := by
          simp only [polarity, decide_eq_true_eq]; scalar_tac
        simp [pvalue, hs, hpol]
      · rw [if_neg hp]
        have hpol : polarity lit = false := by
          simp only [polarity, decide_eq_false_iff_not]; scalar_tac
        simp [pvalue, hs, hpol]

/-- `assign_true_loop` pads the value vector with `none` until `var` is in
    range, preserving every existing slot and leaving the padding empty. -/
theorem assign_true_loop_spec (self : kernel.Assignment) (var : Std.Usize)
    (hvb : var.val + 1 ≤ Std.Usize.max) :
    kernel.Assignment.assign_true_loop self var ⦃
      (v : alloc.vec.Vec (Option Bool)) =>
        var.val < v.val.length ∧
        ∀ w, (v.val[w]?).join
          = if w < self.values.val.length then (self.values.val[w]?).join
            else none ⦄ := by
  unfold kernel.Assignment.assign_true_loop
  apply loop.spec_decr_nat
    (measure := fun (s : kernel.Assignment) => var.val + 1 - s.values.val.length)
    (inv := fun (s : kernel.Assignment) =>
      self.values.val.length ≤ s.values.val.length ∧
      ∀ w, (s.values.val[w]?).join
        = if w < self.values.val.length then (self.values.val[w]?).join
          else none)
  · rintro s ⟨hmono, hinv⟩
    unfold kernel.Assignment.assign_true_loop.body
    dsimp only
    split
    · rename_i hle
      step as ⟨v, hv⟩
      have hvlen : v.val.length = s.values.val.length + 1 := by simp [hv]
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      intro w
      rw [hv]
      by_cases hw : w < s.values.val.length
      · rw [List.getElem?_append_left hw]; exact hinv w
      · rw [List.getElem?_append_right (by omega),
          if_neg (show ¬ w < self.values.val.length by omega)]
        rcases (w - s.values.val.length) with _ | n <;> simp
    · rename_i hgt
      exact ⟨by scalar_tac, hinv⟩
  · refine ⟨le_refl _, fun w => ?_⟩
    split
    · rfl
    · rename_i hge; rw [List.getElem?_eq_none (by omega)]; rfl

/-- `assign_true` refines `pAssignLit`: the returned conflict flag and updated
    assignment track the pure partial-assignment update. -/
theorem assign_true_refines (Ak : kernel.Assignment) (Ap : PAsn) (lit : Std.I32)
    (hrel : RelAsn Ak Ap) (hvalid : ValidLit lit) :
    Ak.assign_true lit ⦃ (p : Bool × kernel.Assignment) =>
      match pAssignLit Ap lit with
      | none => p.1 = true
      | some Ap' => p.1 = false ∧ RelAsn p.2 Ap' ⦄ := by
  unfold kernel.Assignment.assign_true
  step with (value_refines Ak Ap lit hrel hvalid) as ⟨o, ho⟩
  have hpv : o = (Ap (litVar lit)).map (fun b => b == polarity lit) := ho
  cases hA : Ap (litVar lit) with
  | none =>
    rw [hA] at hpv; simp only [Option.map_none] at hpv
    subst hpv
    dsimp only
    simp only [pAssignLit, hA]
    step with (lit_var_spec lit hvalid) as ⟨var, hvar⟩
    have hvb : var.val + 1 ≤ Std.Usize.max := by rw [hvar]; scalar_tac
    step with (assign_true_loop_spec Ak var hvb) as ⟨v, hvlt, hvr⟩
    step as ⟨pr, imb, hpr, himb⟩
    intro w
    rw [himb]
    have hlv : litVar lit = var.val := hvar.symm
    simp only [alloc.vec.Vec.set_val_eq]
    by_cases hwv : w = var.val
    · subst hwv
      rw [if_pos hlv.symm, List.getElem?_set_self (by scalar_tac), Option.join_some]
      simp only [polarity]
      congr 1
    · rw [if_neg (by rw [hlv]; exact hwv), List.getElem?_set_ne (Ne.symm hwv),
        hvr w, hrel w]
      split
      · rfl
      · rename_i hge; rw [List.getElem?_eq_none (by omega)]; rfl
  | some b' =>
    rw [hA] at hpv; simp only [Option.map_some] at hpv
    subst hpv
    dsimp only
    simp only [pAssignLit, hA]
    by_cases hb : (b' == polarity lit) = true
    · simp only [hb]; exact ⟨rfl, hrel⟩
    · simp only [Bool.not_eq_true] at hb; simp [hb]

/-- Negating a valid literal keeps it valid (`-lit` cannot be `0` or overflow
    to `INT_MIN`). -/
theorem valid_neg (lit neg : Std.I32) (h : ValidLit lit) (hn : neg.val = -lit.val) :
    ValidLit neg := by
  obtain ⟨h0, hmin⟩ := h
  refine ⟨by rw [hn]; omega, ?_⟩
  have hb : lit.val ≤ Std.I32.max := by scalar_tac
  have hmm : core.num.I32.MIN.val = -Std.I32.max - 1 := by native_decide
  rw [hn]; omega

/-- Assigning the negation of a literal true is the pure "assume false". -/
theorem pAssignLit_neg (A : PAsn) (lit neg : Std.I32) (h0 : lit.val ≠ 0)
    (hn : neg.val = -lit.val) : pAssignLit A neg = pAssumeFalse A lit := by
  have hlv : litVar neg = litVar lit := by
    unfold litVar; rw [hn, Int.natAbs_neg]
  have hpol : polarity neg = !polarity lit := by
    unfold polarity; rw [hn]
    rcases lt_or_gt_of_ne h0 with h | h
    · rw [decide_eq_true (show (0:Int) < -lit.val by omega),
          decide_eq_false (show ¬(0:Int) < lit.val by omega)]; rfl
    · rw [decide_eq_false (show ¬(0:Int) < -lit.val by omega),
          decide_eq_true (show (0:Int) < lit.val by omega)]; rfl
  unfold pAssignLit pAssumeFalse
  rw [hlv, hpol]

/-- `pAssumeNeg` folds left-to-right with short-circuit, so it splits over
    concatenation. -/
theorem pAssumeNeg_append (A : PAsn) (xs ys : List Std.I32) :
    pAssumeNeg A (xs ++ ys) = (pAssumeNeg A xs).bind (fun A' => pAssumeNeg A' ys) := by
  induction xs generalizing A with
  | nil => simp [pAssumeNeg]
  | cons h t ih =>
    simp only [List.cons_append, pAssumeNeg]
    cases pAssumeFalse A h with
    | none => rfl
    | some A' => exact ih A'

/-- Fourth simulation leaf: `assume_negation` refines `pAssumeNeg`. It assumes
    every clause literal false (assigns its negation true); the returned flag
    is the tautology/conflict signal. -/
theorem assume_negation_refines (Ak : kernel.Assignment) (Ap : PAsn)
    (clause : Slice Std.I32) (hrel : RelAsn Ak Ap)
    (hvalid : ∀ lit ∈ clause.val, ValidLit lit) :
    kernel.assume_negation Ak clause ⦃ (p : Bool × kernel.Assignment) =>
      match pAssumeNeg Ap clause.val with
      | none => p.1 = true
      | some Ap' => p.1 = false ∧ RelAsn p.2 Ap' ⦄ := by
  unfold kernel.assume_negation kernel.assume_negation_loop
  apply loop.spec_decr_nat
    (measure := fun (s : kernel.Assignment × Std.Usize) =>
      clause.val.length - s.2.val)
    (inv := fun (s : kernel.Assignment × Std.Usize) =>
      s.2.val ≤ clause.val.length ∧
      ∃ Api, pAssumeNeg Ap (clause.val.take s.2.val) = some Api ∧ RelAsn s.1 Api)
  · rintro ⟨asg, i⟩ ⟨hle, Api, hpn, hrelI⟩
    unfold kernel.assume_negation_loop.body
    dsimp only
    split
    · rename_i hlt
      step as ⟨lit, hlit⟩
      have hmem : lit ∈ clause.val := by rw [hlit]; exact List.getElem_mem _
      have hvlit : ValidLit lit := hvalid lit hmem
      step as ⟨negl, hnegl⟩
      have hvneg : ValidLit negl := valid_neg lit negl hvlit hnegl
      have htake : clause.val.take (i.val + 1) = clause.val.take i.val ++ [lit] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by scalar_tac), ← hlit]
        simp
      have hkey : (some Api).bind (fun A' => pAssumeNeg A' [lit]) = pAssumeFalse Api lit := by
        show pAssumeNeg Api [lit] = pAssumeFalse Api lit
        simp only [pAssumeNeg]; cases pAssumeFalse Api lit <;> rfl
      have hpsplit : pAssumeNeg Ap clause.val
          = (pAssumeFalse Api lit).bind (fun A' => pAssumeNeg A' (clause.val.drop (i.val + 1))) := by
        conv_lhs => rw [← List.take_append_drop (i.val + 1) clause.val, pAssumeNeg_append,
          htake, pAssumeNeg_append, hpn, hkey]
      step with (assign_true_refines asg Api negl hrelI hvneg) as ⟨b2, asg2, hp2⟩
      rw [pAssignLit_neg Api lit negl hvlit.1 hnegl] at hp2
      split
      · rename_i hb
        cases hpf : pAssumeFalse Api lit with
        | none => simp [hpsplit, hpf]
        | some Ap' => rw [hpf] at hp2; simp_all
      · rename_i hb
        cases hpf : pAssumeFalse Api lit with
        | none => rw [hpf] at hp2; simp_all
        | some Ap' =>
          rw [hpf] at hp2
          obtain ⟨_, hrel'⟩ := hp2
          step as ⟨i4, hi4⟩
          refine ⟨by scalar_tac, ⟨Ap', ?_, hrel'⟩, by scalar_tac⟩
          rw [hi4, htake, pAssumeNeg_append, hpn]
          simp [pAssumeNeg, hpf]
    · rename_i hge
      have hik : i.val = clause.val.length := by scalar_tac
      rw [hik, List.take_length] at hpn
      rw [hpn]; exact ⟨rfl, hrelI⟩
  · exact ⟨by simp, Ap, by simp [pAssumeNeg], hrel⟩

/-- `pUnassigned` folds left-to-right (threading the dedup accumulator) with a
    short-circuit to `none`, so it splits over concatenation. -/
theorem pUnassigned_append (A : PAsn) (acc xs ys : List Std.I32) :
    pUnassigned A acc (xs ++ ys)
      = (pUnassigned A acc xs).bind (fun acc' => pUnassigned A acc' ys) := by
  induction xs generalizing acc with
  | nil => simp [pUnassigned]
  | cons h t ih =>
    simp only [List.cons_append, pUnassigned]
    cases pvalue A h with
    | none =>
      by_cases hd : acc.any (fun l => l.val == h.val) = true
      · simp only [hd, if_true]; exact ih acc
      · simp only [hd, if_false, Bool.not_eq_true]; exact ih (acc ++ [h])
    | some b => cases b with
      | true => rfl
      | false => exact ih acc

/-- `pUnassigned` collects at most `|acc| + |input|` literals (it only ever
    appends, one per input element). Bounds the kernel's `unassigned` vector so
    its `push` stays within `Usize`. -/
theorem pUnassigned_length (A : PAsn) (acc l r : List Std.I32)
    (h : pUnassigned A acc l = some r) : r.length ≤ acc.length + l.length := by
  induction l generalizing acc with
  | nil =>
    simp only [pUnassigned, Option.some.injEq] at h; subst h; simp
  | cons x t ih =>
    simp only [pUnassigned] at h
    split at h
    · simp at h
    · have := ih acc h; simp only [List.length_cons]; omega
    · split at h
      · have := ih acc h; simp only [List.length_cons]; omega
      · have := ih (acc ++ [x]) h
        simp only [List.length_append, List.length_cons, List.length_singleton,
          List.length_nil] at this ⊢
        omega

/-- `contains_lit` decides membership by underlying value. -/
theorem contains_lit_spec (lits : Slice Std.I32) (lit : Std.I32) :
    kernel.contains_lit lits lit ⦃ (b : Bool) =>
      b = lits.val.any (fun l => l.val == lit.val) ⦄ := by
  unfold kernel.contains_lit kernel.contains_lit_loop
  apply loop.spec_decr_nat
    (measure := fun (i : Std.Usize) => lits.val.length - i.val)
    (inv := fun (i : Std.Usize) => i.val ≤ lits.val.length ∧
      (lits.val.take i.val).any (fun l => l.val == lit.val) = false)
  · rintro i ⟨hle, hnone⟩
    unfold kernel.contains_lit_loop.body
    dsimp only
    split
    · rename_i hlt
      step as ⟨lv, hlv⟩
      split
      · rename_i heq
        have hmem : lv ∈ lits.val := by rw [hlv]; exact List.getElem_mem _
        have : lits.val.any (fun l => l.val == lit.val) = true := by
          rw [List.any_eq_true]
          exact ⟨lv, hmem, by rw [heq]; simp⟩
        simp [this]
      · rename_i hne
        step as ⟨i3, hi3⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i3.val = i.val + 1 by scalar_tac, List.take_add_one,
          List.getElem?_eq_getElem (by scalar_tac), ← hlv]
        simp only [Option.toList_some, List.any_append, List.any_cons,
          List.any_nil, Bool.or_false, hnone, Bool.false_or]
        rw [Bool.eq_false_iff, ne_eq, beq_iff_eq]
        intro hc; exact hne (by scalar_tac)
    · rename_i hge
      have hik : i.val = lits.val.length := by scalar_tac
      rw [hik, List.take_length] at hnone
      simp [hnone]
  · exact ⟨by simp, by simp⟩

/-- Fifth simulation leaf: `classify_hint` refines `pUnassigned` + the length
    classification (Satisfied/Falsified/Unit/Multi ↔ none/[]/[u]/2+). -/
theorem classify_hint_refines (Ak : kernel.Assignment) (Ap : PAsn)
    (clause : Slice Std.I32) (hrel : RelAsn Ak Ap)
    (hvalid : ∀ lit ∈ clause.val, ValidLit lit) :
    kernel.classify_hint Ak clause ⦃ (hc : kernel.HintClass) =>
      match pUnassigned Ap [] clause.val with
      | none => hc = kernel.HintClass.Satisfied
      | some [] => hc = kernel.HintClass.Falsified
      | some [u] => hc = kernel.HintClass.Unit u
      | some (_ :: _ :: _) => hc = kernel.HintClass.Multi ⦄ := by
  unfold kernel.classify_hint kernel.classify_hint_loop
  apply loop.spec_decr_nat
    (measure := fun (s : alloc.vec.Vec Std.I32 × Std.Usize) =>
      clause.val.length - s.2.val)
    (inv := fun (s : alloc.vec.Vec Std.I32 × Std.Usize) =>
      s.2.val ≤ clause.val.length ∧
      pUnassigned Ap [] (clause.val.take s.2.val) = some s.1.val)
  · rintro ⟨unas, i⟩ ⟨hle, hpu⟩
    unfold kernel.classify_hint_loop.body
    dsimp only
    split
    · rename_i hlt
      step as ⟨lit, hlit⟩
      have hmem : lit ∈ clause.val := by rw [hlit]; exact List.getElem_mem _
      have hvlit : ValidLit lit := hvalid lit hmem
      step with (value_refines Ak Ap lit hrel hvlit) as ⟨o, ho⟩
      have htake : clause.val.take (i.val + 1) = clause.val.take i.val ++ [lit] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by scalar_tac), ← hlit]; simp
      have hstep : pUnassigned Ap [] (clause.val.take (i.val + 1))
          = pUnassigned Ap unas.val [lit] := by
        rw [htake, pUnassigned_append, hpu]; rfl
      have hfull : pUnassigned Ap [] clause.val
          = (pUnassigned Ap unas.val [lit]).bind
              (fun acc' => pUnassigned Ap acc' (clause.val.drop (i.val + 1))) := by
        conv_lhs => rw [← List.take_append_drop (i.val + 1) clause.val,
          pUnassigned_append, htake, pUnassigned_append, hpu]
        rfl
      cases o with
      | some b => cases b with
        | true =>
          have hpv : pvalue Ap lit = some true := ho.symm
          rw [hfull]; simp [pUnassigned, hpv]
        | false =>
          have hpv : pvalue Ap lit = some false := ho.symm
          dsimp only
          rw [if_neg (by decide : ¬ (false = true))]
          step as ⟨i4, hi4⟩
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          rw [hi4, hstep]; simp [pUnassigned, hpv]
      | none =>
        have hpv : pvalue Ap lit = none := ho.symm
        dsimp only
        step with (contains_lit_spec (alloc.vec.Vec.deref unas) lit) as ⟨bc, hbc⟩
        simp only [alloc.vec.Vec.deref] at hbc
        split
        · rename_i hd
          step as ⟨i4, hi4⟩
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          rw [hi4, hstep]
          rw [hbc] at hd
          simp only [pUnassigned, hpv, hd, if_true]
        · rename_i hd
          have hbound : unas.val.length < Usize.max := by
            have hl := pUnassigned_length Ap [] (clause.val.take i.val) unas.val hpu
            simp only [List.length_nil, List.length_take, Nat.zero_add] at hl
            scalar_tac
          step with (alloc.vec.Vec.push_spec unas lit hbound) as ⟨un1, hun1⟩
          step as ⟨i4, hi4⟩
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          rw [hi4, hstep, hun1]
          simp only [pUnassigned, hpv]
          rw [hbc] at hd
          simp [hd]
    · rename_i hge
      have hik : i.val = clause.val.length := by scalar_tac
      rw [hik, List.take_length] at hpu
      split
      · rename_i hz
        have h0 : unas.val = [] := by
          apply List.length_eq_zero_iff.mp; scalar_tac
        simp [hpu, h0]
      · rename_i h1
        obtain ⟨u, hu⟩ := List.length_eq_one_iff.mp (show unas.val.length = 1 by scalar_tac)
        step as ⟨u0, hu0⟩
        simp only [hu, List.getElem_cons_zero] at hu0
        simp [hpu, hu, hu0]
      · rename_i hm
        obtain ⟨a, b, rest, hab⟩ : ∃ a b rest, unas.val = a :: b :: rest := by
          match hh : unas.val, (show 2 ≤ unas.val.length by scalar_tac) with
          | a :: b :: rest, _ => exact ⟨a, b, rest, rfl⟩
        simp [hpu, hab]
  · exact ⟨by simp, by simp [pUnassigned]⟩

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
