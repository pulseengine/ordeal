/-
TR-035: adversarial dual-mechanisation differential (issue #47).

Cross-checks ordeal's own formally-verified LRAT checker (`ordeal-lrat`,
Aeneas → Lean proven, `Sound.lean`) against Lean core's INDEPENDENTLY
verified LRAT checker (`Std.Tactic.BVDecide.LRAT.check`, the absorbed
leansat checker, soundness theorem `LRAT.check_sound`) on the shared
certificate corpus written by `cargo run -p ordeal --example
dump_lrat_corpus`. The corpus manifest carries ordeal's ground-truth verdict
per pair (`accept` for pristine solver-emitted certificates, `reject` for
structurally corrupted ones — the dumper asserts the ordeal verdict before
writing). Any verdict disagreement here localizes either an Aeneas
translation-faithfulness gap or a spec ambiguity between the two
mechanisations, and exits nonzero.

CONVENTION TRANSLATIONS (deliberately minimal — this adapter is itself
spec-ambiguity territory, so every rule is spelled out):

1. Variable numbering. DIMACS numbers variables 1..n; `Std.Sat.CNF Nat`
   numbers them from 0. Lean core's `CNF.convertLRAT` increments every
   variable by one again (via `relabelFin`, which is the identity mapping
   `i ↦ i` for in-range variables, then `+1` into `PosFin`), restoring
   DIMACS numbering — which is exactly the numbering the LRAT proof
   literals use. So: DIMACS literal ±d parses to `(d - 1, d > 0)` here and
   round-trips to internal variable `d`. No other renumbering happens.

2. Clause ids / the sequential-id dialect gate. Both checkers give original
   clause `i` (0-based) the id `i + 1`. Ordeal's dialect additionally
   REQUIRES every addition step to use the next sequential id (sparse ids
   are rejected — documented in `ordeal-lrat`). Lean core's checker never
   even looks at the declared id (`CompactLRATChecker` discards it): hint
   ids resolve POSITIONALLY, as indices into `#[none] ++ cnf ++ inserted`
   in insertion order. A certificate whose declared ids are not sequential
   therefore cannot be faithfully represented to Lean core at all — its
   declared id space and Lean's positional id space disagree, and later
   hints would silently be resolved against different clauses than the
   certificate names. The adapter rejects such certificates at the gate
   below (a rejection is always sound: it never claims "satisfiable", only
   "not proven unsat by this certificate in the shared dialect"). For
   transparency the per-file output still reports what Lean core alone
   would have said, so the divergence stays visible instead of papered
   over: Lean core ACCEPTS a renumbered-id certificate that ordeal rejects
   (`NonSequentialId`) — a genuine strictness difference between the two
   mechanisations, not a soundness gap in either.

3. Text format. Lean core's textual LRAT parser is byte-strict: single
   spaces between tokens, every action line terminated by a newline, no
   trailing blank lines. Ordeal's emitter (`lrat::emit_lrat*`) produces
   exactly that shape; the corpus is written verbatim, unre-encoded.

4. Tautologies. `CNF.convertLRAT` silently DROPS tautological input clauses
   (its `filterMap` yields `none` for them), which would shift every later
   positional id. The corpus dumper asserts no tautological clause is ever
   written, so the two id spaces cannot desynchronize on this corpus.

5. Eager unit preloading (FOUND BY THIS DIFFERENTIAL, kept out of the
   corpus by construction). Lean core's `DefaultFormula.ofArray` preloads
   every original UNIT clause into its assignment vector at formula-load
   time. On a CNF containing a contradictory unit pair `[l]` / `[-l]`, the
   first RUP hint touching that variable reduces to `encounteredBoth` and
   the step counts as verified (`derivedEmpty`) even when its own hint
   chain never reaches a conflict — so Lean core ACCEPTS hint-weakened
   certificates over such CNFs that ordeal rejects (`HintsExhausted`;
   ordeal propagates only through each step's hints). Both stances are
   sound (the CNF genuinely is unsat; acceptance implies unsat in both
   soundness theorems) — what differs is the SPEC of "this hint chain
   justifies this step". The corpus dumper therefore never emits
   hint-weakening mutants over contradictory-unit CNFs (see
   `has_contradictory_units` in dump_lrat_corpus.rs); this note is the
   record of the divergence.
-/
import Std.Tactic.BVDecide.LRAT

open Std.Sat
open Std.Tactic.BVDecide

namespace DiffCheck

/-- The Lean-side verdict on one (CNF, LRAT) pair, with a diagnosis. -/
structure Verdict where
  accept : Bool
  reason : String

/-- Parse DIMACS text into `Std.Sat.CNF Nat` (convention translation 1:
DIMACS literal ±d becomes `(d - 1, d > 0)`). Comment (`c`) and problem
(`p`) lines are skipped; clauses may span lines and end at each `0`. -/
def parseDimacs (txt : String) : Except String (CNF Nat) := do
  let mut clauses : Array (CNF.Clause Nat) := #[]
  let mut cur : List (Literal Nat) := []
  for line in txt.splitOn "\n" do
    if line.isEmpty || line.startsWith "c" || line.startsWith "p" then
      continue
    for tok in line.splitOn " " do
      if tok.isEmpty then
        continue
      match tok.toInt? with
      | none => throw s!"invalid DIMACS token {tok}"
      | some i =>
        if i == 0 then
          clauses := clauses.push cur.reverse
          cur := []
        else if i.natAbs == 0 then
          throw "unreachable: nonzero Int with zero natAbs"
        else
          cur := (i.natAbs - 1, decide (0 < i)) :: cur
  unless cur.isEmpty do
    throw "trailing literals without a terminating 0"
  return ⟨clauses⟩

/-- The sequential-id dialect gate (convention translation 2): original
clauses occupy ids `1..nOrig`, and every addition step must declare id
`nOrig + k` for the `k`-th addition. Deletions carry no meaningful id in
either dialect. -/
def addIdsSequential (nOrig : Nat) (proof : Array LRAT.IntAction) : Bool := Id.run do
  let mut expected := nOrig + 1
  for action in proof do
    match action with
    | .addEmpty id _ | .addRup id _ _ | .addRat id _ _ _ _ =>
      if id != expected then
        return false
      expected := expected + 1
    | .del _ => pure ()
  return true

/-- Run Lean core's verified checker over one corpus pair. A parse failure
is a rejection (both dialects agree rejection is the sound default for a
certificate that cannot even be read). -/
def leanVerdict (cnf : CNF Nat) (proofBytes : ByteArray) : Verdict :=
  match LRAT.parseLRATProof proofBytes with
  | .error e => ⟨false, s!"Lean LRAT parser rejected: {e}"⟩
  | .ok proof =>
    if addIdsSequential cnf.clauses.size proof then
      if LRAT.check proof cnf then
        ⟨true, "Lean core checker accepted"⟩
      else
        ⟨false, "Lean core checker rejected"⟩
    else
      -- Out of the shared dialect: reject, but surface what Lean core alone
      -- says so the strictness divergence stays visible (see header, 2).
      let core := if LRAT.check proof cnf then "ACCEPTS" else "rejects"
      ⟨false, s!"dialect gate: non-sequential addition id \
                 (Lean core alone, positionally, {core} this certificate)"⟩

end DiffCheck

open DiffCheck in
def main (args : List String) : IO UInt32 := do
  match args with
  | [dir] =>
    let root : System.FilePath := ⟨dir⟩
    let manifest ← IO.FS.readFile (root / "manifest.txt")
    let mut checked := 0
    let mut accepted := 0
    let mut rejected := 0
    let mut disagreements := 0
    for line in manifest.splitOn "\n" do
      if line.isEmpty then
        continue
      match line.splitOn " " |>.filter (· ≠ "") with
      | [stem, expectation] =>
        let expectAccept ←
          match expectation with
          | "accept" => pure true
          | "reject" => pure false
          | other =>
            throw <| IO.userError s!"manifest expectation must be accept|reject, got {other}"
        let cnfTxt ← IO.FS.readFile (root / s!"{stem}.cnf")
        let cnf ←
          match parseDimacs cnfTxt with
          | .ok cnf => pure cnf
          | .error e => throw <| IO.userError s!"{stem}.cnf: {e}"
        let proofBytes ← IO.FS.readBinFile (root / s!"{stem}.lrat")
        let verdict := leanVerdict cnf proofBytes
        checked := checked + 1
        if verdict.accept then accepted := accepted + 1 else rejected := rejected + 1
        let ordeal := if expectAccept then "accept" else "reject"
        let lean := if verdict.accept then "accept" else "reject"
        if verdict.accept == expectAccept then
          IO.println s!"AGREE    {stem}: ordeal={ordeal} lean={lean} ({verdict.reason})"
        else
          disagreements := disagreements + 1
          IO.println s!"DISAGREE {stem}: ordeal={ordeal} lean={lean} ({verdict.reason})"
      | _ =>
        throw <| IO.userError s!"malformed manifest line: {line}"
    IO.println s!"diffcheck: {checked} pairs, lean accepted {accepted} / rejected {rejected}, \
                  {disagreements} disagreement(s)"
    if checked == 0 then
      IO.eprintln "diffcheck: empty corpus is a failure (nothing was differenced)"
      return 1
    if disagreements == 0 then
      IO.println "diffcheck: the two independently verified checkers agree on every pair"
      return 0
    else
      IO.println "diffcheck: VERDICT DISAGREEMENT — Aeneas translation gap or spec ambiguity"
      return 1
  | _ =>
    IO.eprintln "usage: diffcheck <corpus-dir>  (as written by dump_lrat_corpus)"
    return 2
