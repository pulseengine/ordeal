/-
  BlasterCompact.lean — the folding + hashing pass (issue #192 phase 3).

  `compact` rebuilds an append-only AIG into a fresh arena node by node:
  inputs keep their numbering, every AND gate is folded (`x&0`, `x&!x`,
  `1&y`, `x&1`, `x&x`), operand-normalised (`lit_le`) and then either shared
  with an existing gate of the new arena — when an UNTRUSTED hint, checked
  by `hint_matches`, names one with exactly the same operands — or pushed
  fresh. `compact_sound` proves that, whatever the hints say, every source
  literal and its image (`pMapLit`) simulate to the same value under every
  input assignment, and that the new arena is well-formed and no larger
  than the source.
-/
import BlasterTseitin
import BlasterRotr
import BlasterFrame
open Aeneas Aeneas.Std Result
set_option maxHeartbeats 1000000
namespace kernel.blast_kernel.spec

/- ══════════════════════════ THE PURE MAP ══════════════════════════ -/

/-- The literal of the compacted arena that a source literal maps to:
    `map[l.node]`, negated if `l` is. -/
def pMapLit (map : List Lit) (l : Lit) : Lit :=
  let m := map.getD l.node.val dLit
  if l.neg then { m with neg := !m.neg } else m

theorem pMapLit_node (map : List Lit) (l : Lit) :
    (pMapLit map l).node = (map.getD l.node.val dLit).node := by
  unfold pMapLit
  split <;> rfl

/-- The value of a mapped literal is the value of the source literal, given
    that every map entry carries its source node's value. -/
theorem pEvalLit_pMapLit {vals' vals : List Bool} {map : List Lit}
    (hmap : ∀ (j : Nat) (hj : j < map.length),
      pEvalLit vals' map[j] = vals.getD j false)
    (l : Lit) (hl : l.node.val < map.length) :
    pEvalLit vals' (pMapLit map l) = pEvalLit vals l := by
  have hm : pEvalLit vals' (map.getD l.node.val dLit) = vals.getD l.node.val false := by
    rw [getD_eq_getElem_of_lt hl]
    exact hmap l.node.val hl
  unfold pMapLit
  cases hneg : l.neg
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hm]
    simp [pEvalLit, hneg]
  · simp only [↓reduceIte]
    rw [pEvalLit_not, hm]
    simp [pEvalLit, hneg]

/-- A mapped literal points into the compacted arena whenever every map
    entry does. -/
theorem pMapLit_node_lt {map : List Lit} {B : Nat}
    (hmap : ∀ l ∈ map, l.node.val < B) (l : Lit) (hl : l.node.val < map.length) :
    (pMapLit map l).node.val < B := by
  rw [pMapLit_node, getD_eq_getElem_of_lt hl]
  exact hmap _ (List.getElem_mem hl)

/- ══════════════════ LEAF SPECS ══════════════════ -/

theorem lit_eq_spec (a b : Lit) :
    lit_eq a b ⦃ r => r = true ↔ a = b ⦄ := by
  obtain ⟨an, aneg⟩ := a
  obtain ⟨bn, bneg⟩ := b
  unfold lit_eq
  split
  · rename_i h
    simp only at h
    simp [WP.spec_ok, h]
  · rename_i h
    simp only at h
    simp [WP.spec_ok, h]

theorem lit_le_spec (a b : Lit) :
    lit_le a b ⦃ _ => True ⦄ := by
  unfold lit_le
  split
  · simp
  · split
    · split <;> simp
    · simp

theorem aig_new_spec :
    aig_new ⦃ a => a.nodes.val = [Node.False] ⦄ := by
  unfold aig_new
  step as ⟨v, hv⟩
  simp [hv]

theorem map_lit_spec (map : Slice Lit) (l : Lit)
    (h : l.node.val < map.val.length) :
    map_lit map l ⦃ r => r = pMapLit map.val l ⦄ := by
  unfold map_lit
  step as ⟨m, hm⟩
  unfold pMapLit
  rw [getD_eq_getElem_of_lt h]
  split
  · rename_i hneg
    step with (lit_not_spec m) as ⟨m', hm'⟩
    simp [hm', hm]
  · rename_i hneg
    simp only [Bool.not_eq_true] at hneg
    simp [hm]

theorem map_word_spec (map : Slice Lit) (word : Slice Lit)
    (h : ∀ l ∈ word.val, l.node.val < map.val.length) :
    map_word map word ⦃ out => out.val = word.val.map (pMapLit map.val) ⦄ := by
  unfold map_word map_word_loop
  apply loop.spec_decr_nat
    (measure := fun (s : alloc.vec.Vec Lit × Std.Usize) =>
      word.val.length - s.2.val)
    (inv := fun (s : alloc.vec.Vec Lit × Std.Usize) =>
      s.2.val ≤ word.val.length ∧
      s.1.val = (word.val.take s.2.val).map (pMapLit map.val))
  · rintro ⟨out, i⟩ ⟨hle, hout⟩
    dsimp only at hle hout
    unfold map_word_loop.body
    dsimp only
    split
    · rename_i hlt
      have hilt : i.val < word.val.length := by scalar_tac
      step as ⟨l, hl⟩
      have hlb : l.node.val < map.val.length := by
        rw [hl]; exact h _ (List.getElem_mem hilt)
      step with (map_lit_spec map l hlb) as ⟨l1, hl1⟩
      have hcap : out.val.length < Usize.max := by
        rw [hout, List.length_map, List.length_take]
        have := word.property
        omega
      step as ⟨out1, hout1⟩
      step as ⟨i1, hi1⟩
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hout1, hout, hi1, hl1, hl, List.take_add_one, List.getElem?_eq_getElem hilt,
        Option.toList_some, List.map_append, List.map_singleton]
    · rename_i hge
      have hieq : i.val = word.val.length := by scalar_tac
      simp only [WP.spec_ok]
      rw [hout, hieq, List.take_length]
  · exact ⟨by simp, by simp⟩

/-- `hint_matches = true` certifies the candidate: a positive literal of an
    AND gate of `out` whose stored operands are exactly `(p, q)`. -/
theorem hint_matches_spec (out : Aig) (cand p q : Lit) :
    hint_matches out cand p q ⦃ r => r = true →
      cand.neg = false ∧
      ∃ (h : cand.node.val < out.nodes.val.length),
        out.nodes.val[cand.node.val]'h = Node.And p q ⦄ := by
  unfold hint_matches
  split
  · simp
  · rename_i hneg
    simp only [Bool.not_eq_true] at hneg
    dsimp only
    split
    · simp
    · rename_i hge
      have hlt : cand.node.val < out.nodes.val.length := by scalar_tac
      step as ⟨n, hn⟩
      cases n with
      | False => simp
      | Input k => simp
      | And cx cy =>
        step with (lit_eq_spec cx p) as ⟨b, hb⟩
        split
        · rename_i hbt
          have hcx : cx = p := hb.mp hbt
          apply WP.spec_mono (lit_eq_spec cy q)
          intro r hr hrt
          have hcy : cy = q := hr.mp hrt
          refine ⟨hneg, hlt, ?_⟩
          rw [← hn, hcx, hcy]
        · simp

/- ══════════════════ ONE AND OF THE COMPACTION ══════════════════ -/

/-- The postcondition of `compact_and`: the arena only grows (by at most one
    node), stays well-formed, and the returned literal — in range — carries
    `rx && ry` as read under the ORIGINAL arena. -/
def CAPost (out : Aig) (rx ry : Lit) (L : Nat) (p : Lit × Aig) : Prop :=
  out.nodes.val <+: p.2.nodes.val ∧
  p.2.nodes.val.length ≤ out.nodes.val.length + 1 ∧
  AigWF p.2.nodes.val L ∧
  p.1.node.val < p.2.nodes.val.length ∧
  ∀ inp : List Bool,
    pEvalLit (pSim inp p.2.nodes.val) p.1
      = (pEvalLit (pSim inp out.nodes.val) rx
         && pEvalLit (pSim inp out.nodes.val) ry)

/-- A fold branch: the arena is untouched and an in-range literal with the
    right value is returned. -/
theorem CAPost_same (out : Aig) (rx ry l : Lit) (L : Nat)
    (hwf : AigWF out.nodes.val L)
    (hl : l.node.val < out.nodes.val.length)
    (hval : ∀ inp : List Bool,
      pEvalLit (pSim inp out.nodes.val) l
        = (pEvalLit (pSim inp out.nodes.val) rx
           && pEvalLit (pSim inp out.nodes.val) ry)) :
    CAPost out rx ry L (l, out) :=
  ⟨List.prefix_refl _, by dsimp only; omega, hwf, hl, hval⟩

/-- The hashing branch: a checked candidate — a positive literal of an
    existing gate with operands `(p, q)`, which are `rx`/`ry` in some
    order — already carries the conjunction. -/
theorem CAPost_reuse (out : Aig) (cand p q rx ry : Lit) (L : Nat)
    (hwf : AigWF out.nodes.val L)
    (hneg : cand.neg = false)
    (hlt : cand.node.val < out.nodes.val.length)
    (hnd : out.nodes.val[cand.node.val]'hlt = Node.And p q)
    (hpq : (p = rx ∧ q = ry) ∨ (p = ry ∧ q = rx)) :
    CAPost out rx ry L (cand, out) := by
  apply CAPost_same out rx ry cand L hwf hlt
  intro inp
  have hNW := hwf cand.node.val hlt
  rw [hnd] at hNW
  simp only [NodeWF] at hNW
  obtain ⟨hpw, hqw⟩ := hNW
  have hv := pSim_getD_and inp out.nodes.val cand.node.val hlt p q hnd hpw hqw
  simp only [pEvalLit, hneg, Bool.false_eq_true, ↓reduceIte] at hv ⊢
  rw [hv]
  rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact Bool.and_comm _ _

/-- The fresh-gate branch. -/
theorem compact_and_push (out : Aig) (p q rx ry : Lit) (L : Nat)
    (hwf : AigWF out.nodes.val L)
    (hcap : out.nodes.val.length < Usize.max)
    (hp : p.node.val < out.nodes.val.length)
    (hq : q.node.val < out.nodes.val.length)
    (hpq : (p = rx ∧ q = ry) ∨ (p = ry ∧ q = rx)) :
    push_and out p q ⦃ r => CAPost out rx ry L r ⦄ := by
  apply WP.spec_mono (push_and_gadget out p q (by omega) hp hq)
  rintro ⟨g, out'⟩ ⟨h1, h2, h3, h4, h5⟩
  dsimp only at h1 h2 h3 h4 h5
  refine ⟨h2, by dsimp only; omega, h4 L hwf, h3, ?_⟩
  intro inp
  rw [h5 inp]
  rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact Bool.and_comm _ _

/-- The tail of `compact_and` after folding and operand normalisation: the
    checked hint, else a fresh gate. -/
theorem compact_and_tail (out : Aig) (map : Slice Lit) (p q rx ry : Lit)
    (hint : Std.Usize) (L : Nat)
    (hwf : AigWF out.nodes.val L)
    (hcap : out.nodes.val.length < Usize.max)
    (hp : p.node.val < out.nodes.val.length)
    (hq : q.node.val < out.nodes.val.length)
    (hpq : (p = rx ∧ q = ry) ∨ (p = ry ∧ q = rx)) :
    (if hint < Slice.len map then do
        let l3 ← Slice.index_usize map hint
        let b7 ← hint_matches out l3 p q
        if b7 = true then ok (l3, out) else push_and out p q
      else push_and out p q) ⦃ r => CAPost out rx ry L r ⦄ := by
  split
  · rename_i hlt
    have hhint : hint.val < map.val.length := by scalar_tac
    step as ⟨l3, hl3⟩
    step with (hint_matches_spec out l3 p q) as ⟨b7, hb7⟩
    split
    · rename_i hbt
      obtain ⟨hneg, hlt3, hnd⟩ := hb7 hbt
      simp only [WP.spec_ok]
      exact CAPost_reuse out l3 p q rx ry L hwf hneg hlt3 hnd hpq
    · exact compact_and_push out p q rx ry L hwf hcap hp hq hpq
  · exact compact_and_push out p q rx ry L hwf hcap hp hq hpq

theorem compact_and_spec (out : Aig) (map : Slice Lit) (rx ry : Lit)
    (hint : Std.Usize) (L : Nat)
    (hwf : AigWF out.nodes.val L)
    (hne : 0 < out.nodes.val.length)
    (h0 : out.nodes.val[0]'hne = Node.False)
    (hcap : out.nodes.val.length < Usize.max)
    (hx : rx.node.val < out.nodes.val.length)
    (hy : ry.node.val < out.nodes.val.length) :
    compact_and out map rx ry hint ⦃ p =>
      out.nodes.val <+: p.2.nodes.val ∧
      p.2.nodes.val.length ≤ out.nodes.val.length + 1 ∧
      AigWF p.2.nodes.val L ∧
      p.1.node.val < p.2.nodes.val.length ∧
      ∀ inp : List Bool,
        pEvalLit (pSim inp p.2.nodes.val) p.1
          = (pEvalLit (pSim inp out.nodes.val) rx
             && pEvalLit (pSim inp out.nodes.val) ry) ⦄ := by
  show compact_and out map rx ry hint ⦃ p => CAPost out rx ry L p ⦄
  have hl0 : ({ node := 0#usize, neg := false } : Lit).node.val
      < out.nodes.val.length := by simpa using hne
  unfold compact_and
  step with lit_false_spec as ⟨l, hl⟩
  step with (lit_eq_spec rx l) as ⟨b, hb⟩
  split
  · rename_i hbt
    have hrx : rx = l := hb.mp hbt
    simp only [WP.spec_ok]
    refine CAPost_same out rx ry l L hwf (by rw [hl]; exact hl0) ?_
    intro inp
    rw [hrx, hl, pEvalLit_node_zero hne h0 inp false]
    simp
  step with (lit_eq_spec ry l) as ⟨b1, hb1⟩
  split
  · rename_i hbt
    have hry : ry = l := hb1.mp hbt
    simp only [WP.spec_ok]
    refine CAPost_same out rx ry l L hwf (by rw [hl]; exact hl0) ?_
    intro inp
    rw [hry, hl, pEvalLit_node_zero hne h0 inp false]
    simp
  step with (lit_not_spec ry) as ⟨l1, hl1⟩
  step with (lit_eq_spec rx l1) as ⟨b2, hb2⟩
  split
  · rename_i hbt
    have hrx : rx = l1 := hb2.mp hbt
    simp only [WP.spec_ok]
    refine CAPost_same out rx ry l L hwf (by rw [hl]; exact hl0) ?_
    intro inp
    rw [hrx, hl1, hl, pEvalLit_node_zero hne h0 inp false, pEvalLit_not]
    simp
  step with lit_true_spec as ⟨l2, hl2⟩
  step with (lit_eq_spec rx l2) as ⟨b3, hb3⟩
  split
  · rename_i hbt
    have hrx : rx = l2 := hb3.mp hbt
    simp only [WP.spec_ok]
    refine CAPost_same out rx ry ry L hwf hy ?_
    intro inp
    rw [hrx, hl2, pEvalLit_node_zero hne h0 inp true]
    simp
  step with (lit_eq_spec ry l2) as ⟨b4, hb4⟩
  split
  · rename_i hbt
    have hry : ry = l2 := hb4.mp hbt
    simp only [WP.spec_ok]
    refine CAPost_same out rx ry rx L hwf hx ?_
    intro inp
    rw [hry, hl2, pEvalLit_node_zero hne h0 inp true]
    simp
  step with (lit_eq_spec rx ry) as ⟨b5, hb5⟩
  split
  · rename_i hbt
    have hrx : rx = ry := hb5.mp hbt
    simp only [WP.spec_ok]
    refine CAPost_same out rx ry rx L hwf hx ?_
    intro inp
    rw [hrx]
    simp
  step with (lit_le_spec rx ry) as ⟨b6⟩
  -- The operand order: `(p, q)` is `(rx, ry)` or `(ry, rx)`.
  by_cases hb6 : b6 = true
  · simp only [hb6, ↓reduceIte, bind_tc_ok]
    exact compact_and_tail out map rx ry rx ry hint L hwf hcap hx hy (Or.inl ⟨rfl, rfl⟩)
  · simp only [hb6]
    exact compact_and_tail out map ry rx rx ry hint L hwf hcap hy hx (Or.inr ⟨rfl, rfl⟩)

/- ══════════════════ THE COMPACTION LOOP ══════════════════ -/

/-- Node 0 stays the constant-FALSE node along any extension. -/
theorem getElem?_zero_false_of_prefix {ns ns' : List Node} (hpre : ns <+: ns')
    (h : ns[0]? = some Node.False) : ns'[0]? = some Node.False := by
  obtain ⟨t, rfl⟩ := hpre
  cases ns with
  | nil => simp at h
  | cons hd tl =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    simp [h]

theorem node0_of_getElem? {ns : List Node} (h : ns[0]? = some Node.False) :
    ∃ hne : 0 < ns.length, ns[0]'hne = Node.False := by
  cases ns with
  | nil => simp at h
  | cons hd tl =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    exact ⟨by simp, h⟩

/-- The hint selection: any value is fine, the check is downstream. -/
theorem hint_sel_spec (hints : Slice Std.Usize) (i : Std.Usize) :
    (if i < Slice.len hints then Slice.index_usize hints i else ok i) ⦃ _ => True ⦄ := by
  split
  · rename_i hlt
    have hb : i.val < hints.val.length := by scalar_tac
    apply WP.spec_mono (Slice.index_usize_spec hints i hb)
    intros
    trivial
  · simp [WP.spec_ok]

/-- Loop invariant of `compact` after `i` source nodes: one map entry per
    processed node, the new arena well-formed with node 0 = FALSE and no
    larger than `i` (plus the initial node while `i = 0`), every map entry
    in range and carrying its source node's simulated value. -/
def CompactInv (src : List Node) (L : Nat)
    (s : Aig × alloc.vec.Vec Lit × Std.Usize) : Prop :=
  s.2.2.val ≤ src.length ∧
  s.2.1.val.length = s.2.2.val ∧
  AigWF s.1.nodes.val L ∧
  s.1.nodes.val[0]? = some Node.False ∧
  s.1.nodes.val.length ≤ s.2.2.val + 1 ∧
  (0 < s.2.2.val → s.1.nodes.val.length ≤ s.2.2.val) ∧
  (∀ l ∈ s.2.1.val, l.node.val < s.1.nodes.val.length) ∧
  ∀ (inp : List Bool) (j : Nat) (hj : j < s.2.1.val.length),
    pEvalLit (pSim inp s.1.nodes.val) s.2.1.val[j] = (pSim inp src).getD j false

/-- One step of the invariant: the arena grew by at most one node (none
    while `i = 0`), and the new entry `l` carries node `i`'s value. -/
theorem CompactInv_step {src : List Node} {L : Nat} {out out' : Aig}
    {map map1 : alloc.vec.Vec Lit} {i i2 : Std.Usize} {l : Lit}
    (hinv : CompactInv src L (out, map, i))
    (hilt : i.val < src.length)
    (hpre : out.nodes.val <+: out'.nodes.val)
    (hlen : out'.nodes.val.length ≤ out.nodes.val.length + 1)
    (hlen0 : i.val = 0 → out'.nodes.val.length ≤ 1)
    (hwf' : AigWF out'.nodes.val L)
    (hl : l.node.val < out'.nodes.val.length)
    (hval : ∀ inp : List Bool,
      pEvalLit (pSim inp out'.nodes.val) l = (pSim inp src).getD i.val false)
    (hmap1 : map1.val = map.val ++ [l])
    (hi2 : i2.val = i.val + 1) :
    CompactInv src L (out', map1, i2) := by
  obtain ⟨hile, hmlen, hwfo, h0o, hcap1, hcap2, hrange, hsem⟩ := hinv
  dsimp only at hile hmlen hwfo h0o hcap1 hcap2 hrange hsem
  have hplen := hpre.length_le
  refine ⟨by dsimp only; omega, by dsimp only; rw [hmap1]; simp [hmlen, hi2], hwf',
    getElem?_zero_false_of_prefix hpre h0o, by dsimp only; omega, ?_, ?_, ?_⟩
  · dsimp only
    intro hpos
    by_cases hi0 : i.val = 0
    · have := hlen0 hi0
      omega
    · have := hcap2 (by omega)
      omega
  · dsimp only
    intro l' hl'
    rw [hmap1, List.mem_append, List.mem_singleton] at hl'
    rcases hl' with hl' | rfl
    · have := hrange l' hl'
      omega
    · exact hl
  · dsimp only
    intro inp j hj
    have key : ∀ (ms : List Lit) (_ : ms = map.val ++ [l]) (hj : j < ms.length),
        pEvalLit (pSim inp out'.nodes.val) ms[j] = (pSim inp src).getD j false := by
      rintro _ rfl hj
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hjlt : j < map.val.length
      · rw [List.getElem_append_left hjlt]
        rw [pEvalLit_stable hpre _ (hrange _ (List.getElem_mem hjlt)) inp]
        exact hsem inp j hjlt
      · have hjeq : j = map.val.length := by omega
        have hget : (map.val ++ [l])[j] = l := List.getElem_concat_length hjeq _
        rw [hget, hjeq, hmlen]
        exact hval inp
    exact key _ hmap1 hj

theorem compact_loop_spec (v : alloc.vec.Vec Node) (hints : Slice Std.Usize)
    (n : Std.Usize) (out : Aig) (map : alloc.vec.Vec Lit) (i : Std.Usize) (L : Nat)
    (hwf : AigWF v.val L) (hn : n.val = v.val.length)
    (h0 : v.val[0]? = some Node.False)
    (hinv : CompactInv v.val L (out, map, i)) :
    compact_loop v hints out map n i ⦃ p =>
      p.2.val.length = v.val.length ∧
      AigWF p.1.nodes.val L ∧
      0 < p.1.nodes.val.length ∧
      p.1.nodes.val[0]? = some Node.False ∧
      p.1.nodes.val.length ≤ v.val.length ∧
      (∀ l ∈ p.2.val, l.node.val < p.1.nodes.val.length) ∧
      ∀ (inp : List Bool) (j : Nat) (hj : j < p.2.val.length),
        pEvalLit (pSim inp p.1.nodes.val) p.2.val[j]
          = (pSim inp v.val).getD j false ⦄ := by
  unfold compact_loop
  apply loop.spec_decr_nat
    (measure := fun (s : Aig × alloc.vec.Vec Lit × Std.Usize) =>
      v.val.length - s.2.2.val)
    (inv := CompactInv v.val L)
  · rintro ⟨out, map, i⟩ hinv
    have hinv' := hinv
    obtain ⟨hile, hmlen, hwfo, h0o, hcap1, hcap2, hrange, hsem⟩ := hinv'
    dsimp only at hile hmlen hwfo h0o hcap1 hcap2 hrange hsem
    obtain ⟨hne0, h00⟩ := node0_of_getElem? h0o
    unfold compact_loop.body
    dsimp only
    split
    · rename_i hlt
      have hilt : i.val < v.val.length := by scalar_tac
      have hvmax := v.len_ineq
      have hmcap : map.val.length < Usize.max := by omega
      have h1max : 1 < Usize.max := by scalar_tac
      step as ⟨node, hnode⟩
      have hnode? : v.val[i.val]? = some node := by
        rw [List.getElem?_eq_getElem hilt, hnode]
      step with (hint_sel_spec hints i) as ⟨hint⟩
      have hNW := hwf i.val hilt
      rw [← hnode] at hNW
      cases node with
      | False =>
        dsimp only
        step with lit_false_spec as ⟨l1, hl1⟩
        step as ⟨map1, hmap1⟩
        step as ⟨i2, hi2⟩
        refine ⟨CompactInv_step hinv hilt (List.prefix_refl _) (by omega)
          (fun _ => by omega) hwfo (by rw [hl1]; exact hne0) ?_ hmap1 hi2, by scalar_tac⟩
        intro inp
        rw [hl1, pEvalLit_node_zero hne0 h00 inp false, pSim_getD_eq inp v.val i.val hilt,
          ← hnode]
        rfl
      | Input k =>
        dsimp only
        simp only [NodeWF] at hNW
        have hi0 : i.val ≠ 0 := by
          intro hi0
          rw [hi0, h0] at hnode?
          exact Node.noConfusion (Option.some.inj hnode?)
        have hcapo : out.nodes.val.length < Usize.max := by
          have := hcap2 (by omega)
          omega
        step with (push_input_spec out k hcapo) as ⟨r, h1, h2, h3⟩
        obtain ⟨l1, out2⟩ := r
        dsimp only at h1 h2 h3 ⊢
        step as ⟨map1, hmap1⟩
        step as ⟨i2, hi2⟩
        refine ⟨CompactInv_step hinv hilt (by rw [h1]; exact List.prefix_append _ _)
          (by rw [h1]; simp) (fun hi0' => absurd hi0' hi0)
          (by rw [h1]; exact AigWF_append_input hwfo hNW)
          (by rw [h1]; simp [h2]) ?_ hmap1 hi2, by scalar_tac⟩
        intro inp
        rw [h1, pEvalLit_fresh inp _ _ l1 h2, h3, pSim_getD_eq inp v.val i.val hilt, ← hnode]
        simp [pNodeVal]
      | And x y =>
        dsimp only
        simp only [NodeWF] at hNW
        obtain ⟨hxw, hyw⟩ := hNW
        have hi0 : i.val ≠ 0 := by
          intro hi0
          rw [hi0, h0] at hnode?
          exact Node.noConfusion (Option.some.inj hnode?)
        have hcapo : out.nodes.val.length < Usize.max := by
          have := hcap2 (by omega)
          omega
        have hderef : (alloc.vec.Vec.deref map).val = map.val := rfl
        have hxb : x.node.val < (alloc.vec.Vec.deref map).val.length := by
          rw [hderef]; omega
        have hyb : y.node.val < (alloc.vec.Vec.deref map).val.length := by
          rw [hderef]; omega
        step with (map_lit_spec (alloc.vec.Vec.deref map) x hxb) as ⟨rx, hrx⟩
        step with (map_lit_spec (alloc.vec.Vec.deref map) y hyb) as ⟨ry, hry⟩
        rw [hderef] at hrx hry
        have hrxb : rx.node.val < out.nodes.val.length := by
          rw [hrx]; exact pMapLit_node_lt hrange x (by omega)
        have hryb : ry.node.val < out.nodes.val.length := by
          rw [hry]; exact pMapLit_node_lt hrange y (by omega)
        step with (compact_and_spec out (alloc.vec.Vec.deref map) rx ry hint L hwfo hne0 h00
          hcapo hrxb hryb) as ⟨r, hpre, hlen, hwf2, hl1, hval⟩
        obtain ⟨l1, out2⟩ := r
        dsimp only at hpre hlen hwf2 hl1 hval ⊢
        step as ⟨map1, hmap1⟩
        step as ⟨i2, hi2⟩
        refine ⟨CompactInv_step hinv hilt hpre hlen (fun hi0' => absurd hi0' hi0) hwf2 hl1
          ?_ hmap1 hi2, by scalar_tac⟩
        intro inp
        rw [hval inp, hrx, hry, pEvalLit_pMapLit (hsem inp) x (by omega),
          pEvalLit_pMapLit (hsem inp) y (by omega),
          pSim_getD_and inp v.val i.val hilt x y hnode.symm hxw hyw]
    · rename_i hge
      have hieq : i.val = v.val.length := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨by omega, hwfo, hne0, h0o, ?_, hrange, hsem⟩
      have hvne : 0 < v.val.length := by
        cases hv : v.val with
        | nil => rw [hv] at h0; simp at h0
        | cons _ _ => simp
      have := hcap2 (by omega)
      omega
  · exact hinv

/- ══════════════════ THE PASS ══════════════════ -/

theorem compact_sound (aig : Aig) (hints : Slice Std.Usize) (L : Nat)
    (hwf : AigWF aig.nodes.val L)
    (hne : 0 < aig.nodes.val.length)
    (h0 : aig.nodes.val[0]'hne = Node.False) :
    compact aig hints ⦃ p =>
      p.2.val.length = aig.nodes.val.length ∧
      AigWF p.1.nodes.val L ∧
      0 < p.1.nodes.val.length ∧
      p.1.nodes.val[0]? = some Node.False ∧
      p.1.nodes.val.length ≤ aig.nodes.val.length ∧
      (∀ l ∈ p.2.val, l.node.val < p.1.nodes.val.length) ∧
      ∀ (inp : List Bool) (j : Nat) (hj : j < p.2.val.length),
        pEvalLit (pSim inp p.1.nodes.val) p.2.val[j]
          = (pSim inp aig.nodes.val).getD j false ⦄ := by
  unfold compact
  step with aig_new_spec as ⟨out, hout⟩
  have h0? : aig.nodes.val[0]? = some Node.False := by
    rw [List.getElem?_eq_getElem hne, h0]
  have hwf1 : AigWF [Node.False] L := by
    intro i hi
    simp only [List.length_singleton] at hi
    have : i = 0 := by omega
    subst this
    simp [NodeWF]
  apply compact_loop_spec aig.nodes hints _ out (alloc.vec.Vec.new Lit) 0#usize L hwf
    (by simp) h0?
  refine ⟨by simp, by simp, by rw [hout]; exact hwf1, by rw [hout]; rfl,
    by rw [hout]; simp, by simp, by simp, by simp⟩

/-- Corollary in literal form: every source literal and its image agree. -/
theorem compact_sound_lit (aig : Aig) (hints : Slice Std.Usize) (L : Nat)
    (hwf : AigWF aig.nodes.val L)
    (hne : 0 < aig.nodes.val.length)
    (h0 : aig.nodes.val[0]'hne = Node.False) :
    compact aig hints ⦃ p =>
      p.2.val.length = aig.nodes.val.length ∧
      AigWF p.1.nodes.val L ∧
      0 < p.1.nodes.val.length ∧
      p.1.nodes.val[0]? = some Node.False ∧
      p.1.nodes.val.length ≤ aig.nodes.val.length ∧
      (∀ l : Lit, l.node.val < aig.nodes.val.length →
        (pMapLit p.2.val l).node.val < p.1.nodes.val.length) ∧
      ∀ (inp : List Bool) (l : Lit), l.node.val < aig.nodes.val.length →
        pEvalLit (pSim inp p.1.nodes.val) (pMapLit p.2.val l)
          = pEvalLit (pSim inp aig.nodes.val) l ⦄ := by
  apply WP.spec_mono (compact_sound aig hints L hwf hne h0)
  rintro ⟨out, map⟩ ⟨h1, h2, h3, h4, h5, h6, h7⟩
  dsimp only at h1 h2 h3 h4 h5 h6 h7 ⊢
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_⟩
  · intro l hl
    exact pMapLit_node_lt h6 l (by omega)
  · intro inp l hl
    exact pEvalLit_pMapLit (h7 inp) l (by omega)

end kernel.blast_kernel.spec
