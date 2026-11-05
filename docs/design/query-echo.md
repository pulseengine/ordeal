# Design: the certified query echo — the front end's output, made checkable

**Issue:** #281 (parent #192) · **Milestone:** v0.37.0 · **rivet:** TR-079
(named on the issue, not yet in `artifacts/`) · **Status:** design,
2026-11-05; decision requested (the open questions at the end).
**Scope:** the SMT-LIB and Verus front ends, the last trusted query-side
Rust, and an echo of the certified query in the bundle that lets someone
other than ordeal check them. Nothing here is implemented.

## The claim being protected

Since v0.34.0 (TR-073) every answer rests on proven checks from the
caller's trees down: `flatten_tree` (`crates/ordeal-lrat/src/term_kernel.rs:794`)
→ `check_term_dag` → `check_query` → LRAT, and for the sliver
`check_sliver_lowering`. The canonical trusted-base sentence
(`docs/formal-verification.md:663`, gated by `claims.yaml:26`) still lists
"the SMT-LIB / Verus front ends, the 1:1 copy of the trees into the
kernel's mirror type (`mirror.rs`) … and the toolchain". For a text user
(gale through Verus, anyone with a `.smt2` file), *what was certified*
is whatever `smtlib.rs` made of the text. Nothing outside ordeal can see
that tree today. This note is about making it visible, and about saying
exactly how much trust that moves.

## 1. What is trusted today, text → proven flattener

| # | step | where | what it decides |
|---|---|---|---|
| Q1 | Verus slicing: the **last** `tactic.default_tactic sat` line through the next `(check-sat)`, minus `set-option` / `get-info` lines | `verus.rs:111-152` (121, 141) | which assertions are kept. Dropping assertions is sound for `unsat` (`verus.rs:39-48`); *changing* a line is not, and nothing checks for that |
| Q2 | Tokenizer: whitespace, `;` comments, `(` `)`, `\|…\|` **with the bars kept** in the atom | `smtlib.rs:111-158` (131-142) | symbol identity |
| Q3 | Declarations: `declare-const` / nullary `declare-fun`, `(_ BitVec N)` or `Bool` (as width 1), redeclaration at a second width refused | `smtlib.rs:810-868`, `parse_sort` 698-717 | names and widths |
| Q4 | `Bool` constants become BV1 variables, read as `name = #b1` in boolean position (`declare-const` only) | `smtlib.rs:203-219`, 476-482, 834 | the sort of a boolean leaf |
| Q5 | Desugaring: `true`/`false` → `#b0 = #b0` / `#b0 = #b1`; n-ary `bvadd`… and `concat` left-folded; `=` chained; `distinct` as pairwise `Ne`; `=>` right-associated as `Or(Not p, q)`; `=` over booleans as `iff` (`And` of two `Or`s), decided **structurally** by `is_bool_sexp` | `smtlib.rs:465-472`, 611-626, 561-573, 575-594, 519-532, 496-517, 235-258, 908-921 | the tree's shape |
| Q6 | Indexed rotates: `((_ rotate_right k) x)` → `Rotr(x, Const(k mod w, w))`, likewise `rotate_left` | `smtlib.rs:431-454` | the rotate amount |
| Q7 | Literals: `#x`/`#b` width from digit count, `(_ bvN W)` with the raw `N` | `smtlib.rs:281-300`, 677-696 | constant values and widths |
| Q8 | The copy into the kernel tree, `String` → bytes | `mirror.rs:26-77`, 129-171 | the names the kernel sees |
| Q9 | The CLI glue: which `check-sat` counts (the last), which assertions are live | `smtlib.rs:785-891` | the question asked |

Only Q8 is on the Rust API path (loom, synth). Q1–Q9 are on the text path.
Today's evidence is unit tests, the 60 s fuzz smoke with its evaluator
oracle (`fuzz/fuzz_targets/smtlib_parse.rs`), and the Z3 oracle. **The Z3
oracle never reads text.** `oracle::to_z3` translates ordeal's own
`BoolTerm` into Z3 ASTs (`oracle.rs:79`, 127-143), so it checks the engine,
not the reader. No test in the repository hands an SMT-LIB file to Z3's
parser (searched: no `from_string`, no `z3` subprocess).

### Four front-end deviations found while writing this

These were reproduced on this tree (release build) against Z3 5.1.0
(`/opt/homebrew/bin/z3`). The inputs are in the session scratchpad and
are three lines each:

| input | ordeal | Z3 | class |
|---|---|---|---|
| `(declare-const b Bool) (assert (= (bvadd b #b1) #b0))` | `sat`, `b = #b1` | sort error | accepts an ill-sorted script (Q4: a `Bool` name is in `decls` at width 1, so `parse_bv_atom` takes it as BV1, `smtlib.rs:300-306`) |
| `(declare-fun b () Bool) (assert b)` | `unsupported: boolean atom 'b'` | `sat` | incompleteness (`declare-fun` never inserts into `bool_decls`, only `declare-const` does at 834) |
| `(declare-const \|x\| (_ BitVec 8)) (assert (= x #x01))` | `unknown symbol 'x'` | `sat` | incompleteness: SMT-LIB 2.6 §3.1 makes `\|x\|` and `x` the same symbol, but Q2 keeps the bars |
| `(declare-const x …) (declare-const \|x\| …) (assert (distinct x \|x\|))` | `sat`, two variables | redeclaration error | accepts an invalid script |

None of them is a wrong `unsat`: splitting one symbol into two only
weakens the query, and the others refuse a valid script or accept an
invalid one. They do show the reader and SMT-LIB disagree today, with no
gate that would notice. §6 is built to find this class.

## 2. What an echo removes, and what it does not

An echo is the certified query, printed back as SMT-LIB by the trusted
crate and bound to the certificate. **On its own it removes nothing.**
It moves the question from "is the parser right?", which nobody outside
ordeal can answer, to "is the echo implied by my input?", which a
consumer can decide with a tool they already trust. With `I` the
consumer's script and `E` the echo: the proven chain plus the printer
theorem (§5) gives **`E` unsatisfiable** under the Lean model of
SMT-LIB meaning. For `unsat` the consumer needs only **`I ⊨ E`**
(`I ∧ ¬E` unsat), not equivalence; that one direction also covers
Verus, where `I` is a sliced tail (Q1). For `sat` no echo is needed: the
model is reported by name (`check_tree_model`, `term_kernel.rs:857`),
and checking it against `I` already takes the front end off the `sat`
path today, for anyone who runs that check.

**Who compares, and how.** The consumer does, with their own solver
(Z3, cvc5, Bitwuzla), over a script derived mechanically from `I` and
`E`: (1) rename `E`'s names by the byte substitution `|n|` → `|e.n|` on
every opening bar, which is exact without a parser because every name
in `E` is quoted, no operator is, and no name contains `|` (§3); the
tool checks that the prefix does not occur in `I`. (2) Link the
namespaces: `(= x |e.x|)` for a bitvector, `(= b (= |e.b| #b1))` for a
`Bool`, which is Q4 made explicit. (3) Assert `I`, the links and
`(not (and E₁ … Eₙ))`; `unsat` means `I ⊨ E`. The tool is untrusted and
small, ships behind `oracle` (E3), and its output script is auditable.
For Verus the reference solver is not a new trust: the obligation *is*
what Z3 read from `I`.

**For a consumer who runs the check,** Q1–Q9 leave the trust base,
`mirror.rs` included, because the echo is printed from the kernel's
node list after Q8 (§3). What enters: their solver and its parser, for
one implication; the comparison tool; and the Lean model of SMT-LIB
meaning (§5), a spec validated against Z3, not proven equal to the
standard. **For everyone else nothing changes**, and the trust sentence
has to say so conditionally (E3). **API callers (loom, synth) gain
little:** comparing the echo with their tree means printing their tree,
another trusted copy; `mirror.rs` leaves their base only via (A2) of
`docs/design/flattener-proof.md`, still gated on a `String` model in
Aeneas.

## 3. What is printed

### Which tree: the node list in the bundle, not the `TBool` tree

| | (T1) print the `TBool` tree in the solver | **(T2) print `term` / `ext` from the bundle** |
|---|---|---|
| input | `of_bools(assertions)` (`query.rs:238`) | the core `term` block (`ordeal-term/v1`, `flatten_tree` ∘ `project_core`); for the sliver, the `ext` block (`ordeal-ext/v1`, `cert_bundle.rs:1412`) |
| recheck can re-derive it | no: the bundle has no tree, so the recheck would have to parse the echo (untrusted parse, then `print(parse(E)) == E`) | **yes**: print the blocks it already decodes and compare bytes. No parser anywhere |
| theorem composes with | `flatten_tree_sound`, then the term capstones | `check_term_unsat_sound` (`lean/TermCheck.lean:2444`) / `check_sliver_unsat_sound` (`lean/SliverCheck.lean:6567`) **directly** |
| relation to the caller's tree | exact | exact up to constant masking: `flatten_tree` keeps every operator as its own node and shares only `Var` / `Const` leaves (`term_kernel.rs:28-41`), so unfolding the list gives the tree back, with each constant as its low `w` bits (the same value, `treeBv`'s `Const` arm) |

**(T2).** The printer walks the node list from each root, and it
**refuses a list in which an operator node is the operand of two
nodes**. `flatten_tree` output never has one. A hash-consed list
(`ordeal-term/v2`, the sliver's lowered core) is never printed, and a
crafted bundle cannot blow the echo up exponentially.

### The script

```
(set-logic QF_BV)                    ; QF_ABV / QF_AUFBV when arrays / UFs occur
(declare-const |x| (_ BitVec 8))     ; the var table, in table order
(declare-const |m| (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun |f| ((_ BitVec 8) (_ BitVec 32)) (_ BitVec 16))
(assert <root 0>)                    ; one assert per root, in root order
(check-sat)
```

One space separates tokens and one newline ends each command. There are
no comments, `let`s or `define-fun`s. The output is a pure function of
the block, so its sha256 is too.

**Names.** A name is always printed quoted, as `|bytes|`, and refused
unless every byte is in 0x20–0x7E other than `|` and `\`. It is also
refused if it is empty, if it collides with another name in **any**
namespace (ordeal keeps variables, arrays and functions apart, while
SMT-LIB has one namespace), or if it equals a symbol of the printed
vocabulary or an SMT-LIB 2.6 reserved word (a fixed byte table in the
kernel). Always quoting avoids the digit-start and reserved-word rules
for simple symbols, and it is what makes the §2 rename exact. Verus
names (`%%location_label%%0`, `cpu_id!`) pass. Under Q2's current
bar-keeping, the reader would read `|x|` back as the name `"|x|"`, so
E0 (§7) fixes Q2 to follow the standard first.

**Constants, sorts, operators.** A constant is `#b` and exactly `w`
digits, MSB first, from the `bits` table: the digit count carries the
width, and no decimal `u128` conversion is needed. Widths (`1..=128`),
`extract` / `zero_extend` / `sign_extend` indices and rotate amounts are
decimal numerals from one proven `usize` → digits loop. There is one
symbol per `DagNode` arm (`bvadd … bvsrem`, `bvnot`, `bvneg`, `concat`,
`ite`, `=`, binary `distinct` for `Ne`, `bvult … bvsge`, `not`, `and`,
`or`). The Q5 desugarings show up as what they became (`(= #b0 #b0)`,
nested `and`s), which is the point.

**Rotates.** SMT-LIB has only the indexed `rotate_left` /
`rotate_right`. The kernel's `Rotr` / `Rotl` rotate by a term amount
mod `w` (`lean/BlasterDag.lean:126-130`). When the amount node is a
`Const`, the printer emits the indexed form with `k = bits mod w`, which
covers every rotate the reader makes (`smtlib.rs:441`, 453). A
non-constant amount happens only on the API path: phase 1 refuses it,
and fixed `define-fun` macros could come later (question 7). Z3's
non-standard `ext_rotate_*` (`oracle.rs:101`) is not used.

**Arrays and UF (the sliver, `ExtNode`).** `Select(aid, idx, s, n)`
prints as `(select (store (store … |m| i₁ v₁) …) idx)`. The side table
lists the chain outermost store first (`sliver_kernel.rs:79-83`), so
the printer nests in reverse. `Call(fid, w, s, n)` prints as
`(|f| a₁ … aₙ)`. `declare-fun` needs one signature per function, but
the kernel's flattener checks only the result width
(`flat_func_id`, `term_kernel.rs:398`); arity and argument widths are
checked only by the untrusted lowering (`sliver.rs:167`, 679). So the
printer checks signature consistency itself and refuses otherwise.

**Refusal is not a verdict.** The printer is not on the verdict path. A
refused echo means the bundle is written as v3/v4 without an echo, and
the verdict is unchanged.

## 4. Bundle format `ordeal-cert/v5`

```json
"echo": { "encoding": "ordeal-echo/v1", "logic": "QF_BV",
          "text": "(set-logic QF_BV)\n…(check-sat)\n", "sha256": "…" }
```

- **Shape.** The v3 envelope (`UnsatEnvelopeV3`, `cert_bundle.rs:1057`)
  plus `echo` for a core query, or the v4 envelope (`UnsatEnvelopeV4`,
  1629) plus `echo` for a sliver query, told apart by `ext` (question 2);
  SAT likewise.
- **Hashes.** `echo.sha256 = sha256(echo.text)`. Every other block is
  byte-identical to the v3/v4 bundle of the same query. The text is a
  function of `term` / `ext`, so the hash adds no freedom; it lets a
  consumer match an echo by hash.
- **A new format, not an optional field.** An old reader would accept a
  v4 bundle with an unchecked `echo` beside it, and a consumer would
  read text nothing checked. Refuse by `format`, as every earlier bump
  does (`cert_bundle.rs:1103-1107`).
- **Compatibility.** `from_/to_cert_v1..v4` are unchanged. v5 is
  opt-in: `to_cert_v5` on the cert-bundle path, and a hand-rolled
  `echo` block under a CLI flag (the CLI writes JSON by hand,
  `main.rs:303-330`; the default build has no serde). `ordeal verus`
  writes only the raw `.lrat` today (`main.rs:713-725`), so the echo is
  that path's first bundle-like output (question 8).
- **What `ordeal-recheck` checks for v5** (new rows beside
  `main.rs:177-218`, no SMT-LIB parser): (1) `format`, `verdict`, every
  hash including `echo.sha256`, and `encoding == "ordeal-echo/v1"`;
  (2) the full v3 or v4 recheck, unchanged; (3)
  `ordeal_lrat::echo_term(term…)` (or `echo_ext(ext…)`) returns
  `Ok(bytes)` with `bytes == echo.text` byte for byte, and `logic`
  equal to what it printed. Step 3 is the issue's "re-derives the same
  term" check, run in the cheap direction: print and compare. The
  closure gate (`scripts/recheck_closure.sh`) is unaffected, because
  the printer is in `ordeal-lrat`. `recheck.cmd` extends
  `V3_UNSAT_CMD` (`cert_bundle.rs:1094`) with `&& echo_term(term.nodes,
  term.bits, term.roots, term.vars) == Ok(echo.text)`.

## 5. The Lean obligation

**Round trip `parse (print t) = t`: not recommended.** It needs a Lean
SMT-LIB *parser* as the reference. A parser written in Lean is not SMT-LIB
either; it only moves the spec. It also proves the wrong thing: that the
text determines `t`, not what the text *means*. A round trip is worth
keeping at the lexical layer only, where it is cheap.

**Recommended: a semantic theorem over a small, explicit model.** The
spec is three hand-written Lean definitions, reviewed against SMT-LIB 2.6
(Core, FixedSizeBitVectors, ArraysEx) and kept in a new
`lean/EchoSpec.lean`:

```lean
inductive SExp | sym (b : List U8) | qsym (b : List U8) | num (n : Nat)
               | bin (bs : List Bool) | list (xs : List SExp)
def render : SExp → List U8            -- '(' … ')', one space, '|'-quoting, '#b', digits
def lex    : List U8 → Option (List SExp)  -- §3.1's lexicon restricted to render's image
structure Interp where                  -- an SMT-LIB model of the script's signature
  cst : List U8 → (w : Nat) → BitVec w
  arr : List U8 → BitVec 32 → BitVec 8
  fn  : List U8 → List DVal → DVal
def denBv  (I : Interp) : SExp → Option DVal   -- one arm per symbol: bvudiv ↦ smtUDiv, bvsdiv ↦ smtSDiv,
def denBool (I : Interp) : SExp → Option Bool  -- bvsrem ↦ srem, bvurem ↦ %, rotate_* ↦ rotate* (k % w), …
def ScriptSat (I : Interp) (cs : List SExp) : Prop -- declarations well-sorted; every assert ↦ some true
```

The operator arms are the right-hand sides `dagNodeVal` already uses
(`lean/BlasterDag.lean:95-175`), so the spec reads as "SMT-LIB symbol ↦
the `BitVec` operation Lean's own `bv_decide` maps it to". The theorems:

```lean
theorem lex_render (cs) (h : Printable cs) : lex (renderScript cs) = some cs

theorem echo_term_sound (t tbits troots names nstart nlen vnode vwidth out)
    (h : kernel.echo_kernel.echo_term t tbits troots names nstart nlen vnode vwidth = ok (Ok out)) :
    ∃ cs, out.val = renderScript cs ∧ Printable cs ∧
      ∀ I, ScriptSat I cs ↔ ∀ k (hk : k < troots.val.length),
        dagBool (layoutOf I names nstart nlen vnode vwidth) tbits.val t.val (troots.val[k]).val = true

theorem echo_unsat_sound … (he : echo_term … = ok (Ok out))
    (ht : check_term_dag … = ok (Ok ())) (hq : check_query … = ok (Ok cnf)) :
    ∃ cs, out.val = renderScript cs ∧ ∀ I, ¬ ScriptSat I cs
```

The proof of `echo_unsat_sound` is `echo_term_sound` (→) composed with
`check_term_unsat_sound`. The `ext` twins compose with
`check_sliver_unsat_sound`, with `Interp.arr` / `fn` read through the
`ext` block's array and function tables by name, as `narrsOf` /
`nufsOf` do in `lean/TreeFlatten.lean`. The (←) direction carries the
SAT side. All the capstones are pinned in `AxiomCheck.lean` with
`[propext, Classical.choice, Quot.sound]`.

**The no-axiom gate.** Every `String` / `str` operation becomes an
`axiom` under the pinned Aeneas (`docs/design/flattener-proof.md:510-529`,
spike B2), so the printer has no `String`, `format!` or `fmt`. It
`push`es into a `Vec<u8>`. Names come from `&[u8]` arenas (the
`Flat.names` / `name_start` / `name_len` layout, `term_kernel.rs:182-228`;
on the recheck side the bundle's `vars[].name` bytes). Digits are
`b'0' + n % 10`, the vocabulary and reserved words are `&[u8]`
constants, and every loop is its own function, in `term_kernel.rs`'s
house style. The walk from a root recurses on node indices; the printer
checks that operands are earlier nodes, as `dag_wf` does, so it is
`partial_fixpoint` with partial-correctness proofs by strong induction
(TreeFlatten's precedent). The file is `#[path]`-included into
`kernel.rs`, keeping the one translation unit `regen.sh` assumes.
**What the model is not:** `denBv` and `lex` transcribe the standard,
validated by the echo leg (§6), not proven; `docs/formal-verification.md`
must say so in one sentence.

## 6. The Z3 parser differential

Three legs per script `S`, all in one test module behind `oracle`:

- **Front leg (tests Q2–Q9).** Z3 reads `S` with its own parser
  (`Solver::from_string`; seen in z3-rs 0.21.1 `src/solver.rs:55`, not
  checked in the pinned 0.22.0). Separately, `oracle::to_z3` translates
  ordeal's tree from `smtlib::assertions_at_check_sat`. For each
  assertion `k`, Z3 decides `A_Z3[k] xor A_ord[k]`, with `Bool`-declared
  names linked as in §2. Comparing per assertion is stronger than
  comparing whole queries, and it localises the bug.
- **Echo leg (validates §5's model and the quoting).** Z3 parses the
  echo `E`, and `E[k] xor A_ord[k]` must be unsat. Any disagreement
  means the Lean model and Z3 read the printer's language differently.
- **End-to-end leg (what a consumer runs).** The §2 comparison script,
  `S ∧ links ∧ ¬E`, must be unsat.

**Outcome classes.** `agree`; `disagree`, with Z3's model as the
witness, which fails the job; `ordeal refuses / Z3 accepts`
(incompleteness, counted and listed); `Z3 refuses / ordeal accepts`,
which fails the job unless the script is on a reviewed allow-list (rows
1 and 4 of the §1 table land here until E0 fixes them). Z3 keeps going
after `(error …)`, so the harness treats any error line as "Z3
refuses". A tally of the classes is printed on every run, so an
all-skip run cannot pass silently.

**Sources.** The 27 `.smt2` files in the repository (10
`tests/fixtures/differential`, 3 Verus fixtures via `verus::extract`, 2
`evidence/certs`, 12 `fuzz/seeds/smtlib`). A new seeded **text**
generator (`oracle::gen_smtlib_text`) that emits exactly the syntax the
reader desugars: n-ary operators, chained `=`, n-ary `distinct`, `=>`,
`Bool` constants, `true` / `false`, `rotate_*` with `k ≥ w`, all three
literal forms with values ≥ 2^W, quoted symbols and comments. The tree
generator `gen_corpus` is not enough, because printed trees only reach
canonical syntax. The fuzz-smoke corpus is not persisted, so only its
seeds count. External QF_BV benchmarks are optional (question 9).

**Job.** `Z3 Oracle (optional)` (`.github/workflows/ci.yml:563-595`, the
test step at 586), which already installs `z3 libz3-dev`. That job is
`continue-on-error: true` (566), **so a red differential fails no
merge** (see the Kani and gate-potency precedents). Two options:
split a blocking step that tolerates only the install failing, or make
a green run a recorded rivet verdict that the release gate requires
(question 6). The long text-generator run (10⁵ scripts) belongs in
`nightly-exhaustive.yml`.

**Negative controls.** Each is a test-only mutation hook, armed, shown
to turn its leg red, then disarmed, as `tamper` does. Front: `bvslt`
read as `Ult`, `rotate_left` without `mod w`, `chain_eq` dropping the
last pair, `=>` left-associated. Echo: the `bvsle` arm printing
`bvslt` (Lean catches it too; the differential must catch it alone),
constants printed LSB first. End-to-end: a hand-built `S` / `E` pair
that differs must come out `disagree`. Harness: one fixture per outcome
class.

## 7. Phases, acceptance, cost

Each phase ships on its own and changes no existing bundle byte.

- **E0: front-end hygiene and the front leg** (untrusted side only).
  Strip `|…|` to its content (SMT-LIB 2.6 §3.1; no repository `.smt2`
  quotes a symbol, checked); refuse a `Bool` name in bitvector position;
  read a nullary `Bool` `declare-fun` like `declare-const`; add the
  front leg, the text generator and the outcome classes. *Accept:* §1's
  rows behave like Z3; 0 `disagree` over the 27 files and 10⁴ generated
  scripts; each front control goes red; the CLI byte comparison against
  v0.36.0 shows only the intended changes. *Cost:* ~600 lines.
- **E1: printer and proof.** `crates/ordeal-lrat/src/echo_kernel.rs`
  (`echo_term`, `echo_ext`, `EchoError`), `lean/EchoSpec.lean`,
  `lean/Echo.lean`. *Accept:* capstones pinned axiom-clean; 0 `^axiom`
  in `Kernel.lean`; four kernel mutations (quote dropped, `bvsle`↔`bvslt`,
  `#b` LSB-first, collision check skipped) each break a named theorem,
  and the restored source regenerates byte-identically; 0 `disagree` on
  the echo leg; size and time measured on the latency corpus. *Cost:*
  Rust ~500–700 lines; Lean ~2500–4000 (spec ~500, the rest at
  `TreeFlatten.lean`'s scale of 4031). The expensive phase.
- **E2: `ordeal-cert/v5` and recheck.** `to_/from_cert_v5`, two
  `ordeal-recheck` rows, a CLI flag, an echo on the `verus` path.
  *Accept:* a one-byte flip in `echo.text` is rejected by hash; with the
  hash recomputed, by re-derivation; so is a one-node change in `term`
  with every hash recomputed; every v1–v4 fixture is still accepted
  byte for byte; the wasm differential of `ordeal-recheck` covers v5.
- **E3: consumer tool, docs, claims.** `ordeal echo-check I.smt2
  bundle.json` (behind `oracle`; writes and runs the §2 script), the
  end-to-end leg, and the trust sentence with every gated copy
  (`claims.yaml`), roughly: "*the SMT-LIB / Verus front ends, unless
  the consumer checks the bundle's certified echo against its input,
  in which case that check (its solver and parser) and the Lean model
  of SMT-LIB meaning are trusted instead; …*". *Accept:*
  `claim_check.py` passes; the gale Verus fixtures go end to end.
- **E4 (later, optional):** `define-fun` macros for term-amount
  rotates; the echo on by default.

## 8. What this design does NOT claim

That the front ends are proven: they stay unproven Rust, made
checkable and sampled. That a bundle with an echo shrinks the trust
base of a consumer who does not run the §2 comparison. That the echo
equals the input text: it is the desugared query, and matching is
semantic, one direction for `unsat`. That `mirror.rs` leaves the API
path: only (A2) does that. That the Lean model is the standard: it is a
reviewed transcription, validated against Z3. That Z3 agreement is
evidence of soundness: it is a differential (`oracle.rs:9-21`), and so
are these legs. That every query gets an echo: refusals (§3) are
allowed, and they are never a verdict.

## 9. Recommendation

**E0 first, now.** It is cheap, needs no format change, and is the first
evidence that reads text at all; four deviations already exist that no
gate sees. Then **E1 + E2 as (T2)**: print the `term` / `ext` blocks,
prove `echo_unsat_sound` against a small explicit SMT-LIB model on byte
vectors, and let `ordeal-recheck` re-derive the echo byte for byte, with
no parser anywhere in the trusted crate. Then **E3**, with the trust
sentence conditional on the consumer's comparison, the only honest
reading.

## Decisions (maintainer, 2026-11-05)

- **Q1 → T2.** The echo prints the bundle's `term` / `ext` node lists, and
  `ordeal-recheck` re-derives it byte for byte.
- **Q3 → on by default from v5.** Every bundle carries the echo from the
  release that ships `ordeal-cert/v5`; v5 becomes the default format there
  (v1..v4 stay readable). Consumers (rivet, gale) must accept v5 when they
  upgrade, so that release's notes and consuming-ordeal.md say so.
- **Q6 → blocking, its own job.** The parser differential moves out of the
  `continue-on-error` Z3 Oracle job into a job that fails CI, with a rivet
  verdict the release gate requires.
- **Q5 → ship `echo-check`** under the `oracle` feature, so the consumer's
  comparison is one command.
- **Q4 (quoted symbols)** follows SMT-LIB 2.6 without asking: fixed in E0
  (#294).

## 10. Open questions for the maintainer

1. Print the bundle's `term` / `ext` (T2, recommended) or the `TBool` tree (T1)?
2. One `ordeal-cert/v5` with optional `ext`, or separate core and sliver formats?
3. Echo opt-in first (CLI flag, `to_cert_v5`), or on by default from v5?
4. Accept E0's quoted-symbol change (model names change for quoting inputs; none in the repo)?
5. Ship `echo-check` (Z3 under `oracle`) or only document it? Will rivet / gale run it per bundle?
6. Differential blocking (split from the `continue-on-error` job), or a release-gating rivet verdict?
7. Term-amount rotates (API path only): refuse the echo, or fixed `define-fun` macros?
8. Verus: hand-rolled v5 JSON from the default-build CLI, or an echo `.smt2` beside the `.lrat`?
9. External SMT-LIB QF_BV benchmarks in the corpus (licence, size, runner time)?
