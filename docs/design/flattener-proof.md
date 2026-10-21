# Design: the proven flattener — the answer rests on the query as the caller built it

**Status:** design and feasibility, 2026-10-21; decision requested
(option (A1) below — (A2) is what the spike showed the pinned toolchain
refuses). **Scope:** the last trusted step inside ordeal
between a caller's `BoolTerm` / `ExtBoolTerm` trees and the proven chain
of #192 — the flattening of those trees into the node lists the trusted
checks are stated over, and the variable, array and function **names**
that step identifies — and how to put it under a Lean theorem, leaving
only the SMT-LIB / Verus text front ends trusted. Release v0.34.0, the
last item of #192 on the Rust API side.

## The claim being protected

Since v0.33.0 (TR-072) every answer rests on four proven checks in the
trusted crate `ordeal-lrat`, all stated over the node-list semantics
`dagSim` / `dagBool` (`lean/BlasterDag.lean`) and, for the sliver,
`extSim` / `ExtSat` (`lean/SliverCheck.lean`):

| check | theorem | relates |
|---|---|---|
| `kernel::check_term_dag` | `check_term_unsat_sound`, `check_term_model_sound` (`lean/TermCheck.lean`) | the term **D0** (a `DagNode` list, variables shared by name only) to the solver's canonicalized, hash-consed DAG **D1** |
| `kernel::check_query` / `check_query_model` | `check_query_sound` / `check_query_model_sound` (`lean/QueryCheck.lean`) | D1 to the CNF the LRAT proof refutes / to the model |
| `kernel::sliver_kernel::check_sliver_lowering` | `check_sliver_unsat_sound`, `check_sliver_model_sound` (`lean/SliverCheck.lean`) | the extended query **E** (an `ExtNode` list) to its lowered core D0 |
| `kernel::var_offset` + `check_input_value` | `check_input_value_sound` | a `Var` node's input block to a `u128` model value |

What the caller holds is not D0 and not E. It is a tree —
`crates/ordeal/src/term.rs`: `BvTerm` / `BoolTerm`, recursive `Box` enums
with `Var { name: String, sort: Sort }` leaves; and for the sliver
`sliver.rs`: `ExtBvTerm` / `ExtBoolTerm` / `ArrayTerm` with
`PureCall { name, args: Vec<ExtBvTerm>, sort }` and `Store` chains. The
step from the tree to the node list is untrusted Rust with no theorem
about it, and it is the step that decides **which tree variable is which
node**. Pinned to the code (v0.33.0 + #261):

| # | point | where | what it decides | status |
|---|---|---|---|---|
| N1 | **Variables are interned by name alone.** `DagBuilder::bv` keeps `var_index: HashMap<String, usize>`; the `Var` node's width is the width of the name's *first* occurrence, every later occurrence — at any width — returns that node. | `dag.rs` 103, 210–218 | one name = one variable: the sharing that makes `x ≠ x` unsat | **trusted; load-bearing** (F2 below) |
| N2 | **The width guard.** `Solver::validate` demands one width per name across the assertion set (`check_var_widths_bool`, fuzz-found #139); `lower_with` refuses the query otherwise (`Unknown`). This is what makes N1's identification *the caller's* identification. | `solver.rs` 543–553, 1096, 1598–1672 | without it N1 silently reads a wide variable as the narrow one | **trusted; load-bearing** — F2 shows a certified wrong `Unsat` one edit away |
| N3 | **Constants are interned by the raw `(u128, width)` pair**; the node's bits are the value's low `w` bits. Two values that agree below `w` and differ above are two D0 nodes with equal bits. | `dag.rs` 101, 198–209 | the bit table the proofs read | trusted; harmless in D0 (`term_map` keeps every equal-bits candidate, TR-070); **a completeness defect on the sliver path** (F1) |
| N4 | **Post-order, operands left to right, `Ite` condition first; every operator occurrence its own node; roots in assertion order** (`DagBuilder::new(false)`). | `dag.rs` 193–330, 409–415 | D0's structure | trusted; a consumer re-runs it and compares `term.sha256` (`docs/consuming-ordeal.md`) |
| N5 | **Sort checking** inside the walk (`eval::bv_sort`: widths `1..=128`, operand agreement, `extract` bounds); a failure is `Unknown`. | `eval.rs` 56–95; `dag.rs` 196 | nothing a proof needs: the kernel's `dag_wf` re-checks D0 and refuses an ill-sorted one | not load-bearing |
| N6 | **The `vars` table** `(name, width, node)` in creation order is what binds a model value to a node on `sat`: `term.vars → term.map → var_offset → check_input_value` (TR-069 7d). The model's names come from the solver's D1 `vars` (`blaster.var_order`), the same table built by the same builder over the canonicalized term. | `dag.rs` 51, 216; `query.rs` 530–552, 589–618; `solver.rs` 978–992 | which name a model value is reported under | trusted (the proven binding starts at the node, not the name) |
| N7 | **The extended flattening** `sliver::flatten_ext` / `lower_ext` (`ExtFlat`): N1, N3, N4 again over `ExtBoolTerm`, plus arrays and functions numbered by first appearance (`array_id`, `func_id`: by name, a function's width is its first site's), a `select`'s chain outermost store first in `side`, a call's arguments in `side`. One walk with the lowering so the ids agree. | `sliver.rs` 437–594, 656–778 | E's structure and the array / function ids | trusted; a consumer re-runs it (`docs/consuming-ordeal.md`) |
| N8 | **`ext_of_core`**: a later `Solver::assert` on a sliver solver embeds the closed `BoolTerm` into the extended query (13 arms). | `sliver.rs` 280–297; `solver.rs` 384–395 | part of the flattening path | trusted |
| N9 | **The mappers** `dag::term_map`, `QueryTerm::flatten_sliver` (map, read and call tables) | `dag.rs` 575–; `query.rs` 805–910 | advice | **not trusted** (checked; a wrong entry is `Unknown`) — but see F1 |

The Lean theorems therefore say: *the D0 / E the kernel was handed* is
unsatisfiable, or satisfied by the model at *these nodes*. That D0 is the
caller's trees, and that node `k` is the caller's `x`, is N1–N8. The
issue's own words (#192, 2026-10-21): "Still trusted on this issue: the
flattener (`dag::flatten` / `flatten_ext`, i.e. names and the tree→DAG
step) and the SMT-LIB / Verus front ends."

## Two findings in the shipped Rust

Both reproduced on this tree (v0.33.0 + #261, release and debug) with
`crates/ordeal/tests/probe_flattener.rs` in the session scratchpad; the
inputs are below so they can be re-run.

### F2 — the name identification is a soundness point held by one untrusted guard (confirmed by negative control)

Query, through the Rust API (`Ult` because canon does not reorder it, so
the narrow occurrence stays first):

```rust
let mut s = Solver::new();
s.assert(BoolTerm::Ult(
    Box::new(BvTerm::Var { name: "x".into(), sort: Sort::new(8) }),
    Box::new(BvTerm::Extract { hi: 7, lo: 0,
        arg: Box::new(BvTerm::Var { name: "x".into(), sort: Sort::new(32) }) }),
));
s.check()
```

As shipped: `Unknown` — `check_var_widths_bool` (N2) refuses the second
width. With that one loop in `Solver::validate` skipped (a scratch
mutation, restored): **`Unsat(Certificate { cnf: [[-1], [1]], lrat: "3 0
1 2 0" })`** — a valid certificate, accepted by `check_term_dag` *and*
`check_query`. The flattener made `x:32` the `Var(8)` node of `x:8`, so
D0 reads `x < x[7:0]` over one 8-bit variable, unsatisfiable; the caller
wrote two sorts for one name — satisfiable under a `(name, sort)` reading
(`x:8 = 0, x:32 = 1`) and ill-formed under the one-name reading, and a
certified `Unsat` is wrong under either. Every proven check passed,
because every one of them is stated over the node list the flattener
produced. This is not a shipped bug — the guard is there, and the SMT-LIB
reader refuses the redeclaration on its own (`smtlib.rs` 925–935) — it
is the gap this document is about, made concrete: **one untrusted
function, in `solver.rs`, is the whole difference between the proven
chain and a certified wrong answer**, and nothing in the trusted crate
or in Lean would notice its removal. Under every option below the kernel
refuses a second width for a name itself (`NameWidth`), and the theorem
is stated over an environment keyed by `(name, width)`, so the guard
stops being load-bearing.

### F1 — a constant with bits above its width degrades every sliver answer (confirmed)

```rust
let x = BvTerm::Var { name: "x".into(), sort: Sort::new(8) };
let c = BvTerm::Const { value: 0x1FF, sort: Sort::new(8) };   // bits: 0xFF
Solver::check_sliver(&[ExtBoolTerm::Eq(ExtBvTerm::Core(x), ExtBvTerm::Core(c))])
```

Release: **`Unknown`** (sat expected; the same `Eq` on the core path is
`Sat(x = 255)`). Debug: **panic** at `solver.rs:1037` — `trusted crate
rejected our model, term map or sliver block — ordeal bug` (and
`solver.rs:901` for the unsat shape `x = 0x1FF:8 ∧ x ≠ 0xFF:8`). Cause,
all on the untrusted side: `ExtFlat::konst` and `DagBuilder::bv` intern
the constant under the **raw** key `(0x1FF, 8)`, but
`QueryTerm::flatten_sliver` reconstructs the extended `Const`'s value
**from its bits** (`query.rs` 860–876: `0xFF`) and interns *that*, which
misses the memo: the lowered core gets a second `Const` node with the
same bits, the ext root's image is built over it (`intern_node` misses
too, all the way up), and `check_sliver_lowering` reports `RootMismatch`
— the sound branch, as designed, but a reachable `debug_assert!` that
says "ordeal bug" and is one, and a verdict loom's tests (debug builds)
would see as a panic. `eval::bv_sort` does not refuse an out-of-range
value and `canon` folds it correctly, so the API admits it. Two fixes,
either sufficient: intern by the *masked* value in both builders, or
refuse an out-of-range `Const` in `validate`. Worth its own issue; the
proven flattener of option (A) removes the second builder altogether.

### Not findings — checked and sound

- A name reused at the **same** width anywhere in the assertion set is
  one node on both sides (N1), the model is reported under that name
  (N6). The `vars` table cannot carry one name twice (`var_index`).
- The sliver's fresh names (`$sel:…`, `$uf:…`) cannot capture a query
  variable since #247 (`Lowering::fresh` over `taken`), and
  `check_sliver_lowering`'s variable classes re-establish it (S3 of
  `sliver-proof.md`). A query variable named like an *array* or a
  *function* is a different namespace (`array_index`, `func_index`) —
  no identification.
- `Const` values at width 128 and `width > 128`: `check_width` refuses
  `0` and `> 128`; the bit loop never shifts by 128 or more.
- A tree containing the same `Box` subterm twice (a clone) is two D0
  nodes; hash-consing is D1's business and is checked (TR-069).
- The canonical text of the `term` / `ext` blocks is an integrity hash
  only ("the verdict rests on the recheck"); a name with a space or a
  newline makes the text ambiguous but changes no verdict.

## The semantics (Lean), common to every option

The tree is a Lean inductive — either the Aeneas translation of the
kernel's own tree type (options A2, B) or a hand-written mirror of it
(A1) — and a variable is a **name at a width**. The first theorem of
#192 stated over the caller's structure needs a semantics of that
structure; it is `dagNodeVal`'s arms read over subtree values instead of
operand indices, nothing more:

```lean
/-- A tree assignment: a value for every name at every width. The
    flattener refuses a name at two widths (`NameWidth`), so on an
    accepted tree this is the same as "a value per name". -/
abbrev TEnv := Name → (w : Nat) → BitVec w          -- Name = String (A2) or List U8 (A1)

/-- `dagNodeVal`'s 37 arms, over the values of the children. -/
def treeBv (env : TEnv) : BvTerm → DVal
  | .Const value sort => ⟨sort.width.val, BitVec.ofNat _ value.val⟩          -- the low `w` bits
  | .Var name sort    => ⟨sort.width.val, env name sort.width.val⟩
  | .Add a b          => let x := treeBv env a; let y := treeBv env b; ⟨x.1, x.2 + toW x.1 y.2⟩
  | …                                                                        -- one arm per constructor, the RHS of dagNodeVal's arm
  | .Ite c t e        => if treeBool env c then treeBv env t else treeBv env e
def treeBool (env : TEnv) : BoolTerm → Bool
  | .Eq a b  => decide ((treeBv env a).2 = toW _ (treeBv env b).2)
  | …
  | .Not a   => !treeBool env a
  | .And a b => treeBool env a && treeBool env b
  | .Or a b  => treeBool env a || treeBool env b

/-- The caller's question: every asserted tree is true. -/
def TreeSat (env : TEnv) (ts : List BoolTerm) : Prop :=
  ∀ k (hk : k < ts.length), treeBool env ts[k] = true
```

`BvTerm` and `BoolTerm` are mutually inductive (`Ite` holds a `BoolTerm`),
so `treeBv` / `treeBool` are a `mutual` block and every lemma about them
is proved by the mutual structural induction Lean generates — no loop
specs, no `progress`, no fuel. The sliver adds `ArrayTerm` and
`ExtBvTerm` (`Select`, `PureCall` with `List ExtBvTerm` arguments — a
*nested* inductive, see the feasibility section) and the interpretations
`arrs : Name → BitVec 32 → BitVec 8`, `ufs : Name → List DVal → DVal`
keyed by **array and function names**, with `treeExtBv env arrs ufs`
reading `chainRead` (`SliverCheck.lean`) over the store chain and `ufs
name (args' values)` for a call.

Nothing in `BlasterDag.lean`, `TermCheck.lean`, `QueryCheck.lean` or
`SliverCheck.lean` changes; the new theorems compose with their
capstones through one lemma per option — "the flat term the kernel
produced (or accepted) denotes the tree under agreeing assignments".

## What "names are proven" means, precisely

The kernel's output (A) or input (B) carries, **as kernel data**, the
variable table: for variable `k` its name, its width and its `Var` node.
The two facts the proofs need about it are established *by the kernel's
own lookup*, not assumed:

- **Identification.** Two occurrences of one name (at the accepted
  width) flatten to one node: `lookup_var` finds the earlier entry by a
  byte-for-byte (A1) or `String` (A2) comparison, and only an absent name
  pushes a new `Var`.
- **Injectivity.** Two entries never carry equal names (a name is pushed
  only after the lookup failed), so a node is the image of exactly one
  name — which is what makes the pullback `inp → env` well defined, and
  what F2 is the absence of.

```lean
/-- The flat term's variable `k` reads `env (name k) (width k)` at its block. -/
def TreeVarsAgree (f : Flat) (env : TEnv) (inp : List Bool) : Prop :=
  ∀ k (hk : k < f.var_node.length), ∀ j < (f.var_width[k]).val,
    inp.getD (dagNin (f.nodes.take (f.var_node[k]).val) + j) false
      = (env (nameOf f k) (f.var_width[k]).val).getLsbD j
```

On `sat`, the model is bound **by name through the kernel's table**: a
new `kernel::check_tree_model(f, map, ns, inp, values)` runs
`var_offset` / `check_input_value` for every table entry `k` against
`values[k]`, and the untrusted side prints `(nameOf f k, values[k])` —
the model's names are the kernel's, not a table the solver assembled.
The one remaining untrusted step on a `sat` answer is the *printing* of
a name the kernel holds (a `String` clone in A2; `String::from_utf8` of
the kernel's bytes in A1).

## Option (A): a proven flattener in the kernel, run by the solver

`kernel::term_kernel::flatten_tree(ts: &[BoolTerm]) -> Result<Flat,
FlatError>` — the flattening re-implemented in the Aeneas fragment with
recursion over the tree (the one novelty; feasibility below) and flat
tables instead of `HashMap`s: `nodes`, `bits`, `roots`, and the variable
table `(name, width, node)` as parallel `Vec`s (names in a byte arena
`names` / `name_start` / `name_len` for A1, a `Vec<String>` for A2).
Constants interned by the raw `(value, width)` pair exactly as today
(N3; `u128` equality is modelled), variables looked up by name, every
operator pushed, `Extract` / `ZeroExt` / `SignExt` bounds and operand
widths checked as `bv_sort` does (a refusal is `FlatError`, `Unknown` at
the gate — `dag_wf` on the output stays as the second line). The output
is **byte-identical to `dag::flatten`'s** by construction (same order,
same interning), which the positive control pins over every corpus
before `dag::flatten` leaves the production path (phase 3's move:
`cnf.rs` / `aig.rs` stayed as differential twins).

The solver's gate becomes: `flatten_tree(&self.assertions)` (trusted) →
`term_map` (untrusted advice, unchanged) → `check_term_dag` →
`check_query` / `check_query_model` + `check_tree_model`. The
`QueryTerm` / `term` block is built *from* the kernel's `Flat`
(`ordeal-term/v1` bytes unchanged); a consumer with the trees re-runs
`flatten_tree` and compares.

**The theorem** (`lean/TreeFlatten.lean`, namespace `kernel.spec`):

```lean
/-- The flattening denotes the trees: under agreeing assignments every root of the
    flat term is the tree it came from — and both transports exist. -/
theorem flatten_tree_sound (ts : Slice BoolTerm) (f : Flat)
    (h : kernel.term_kernel.flatten_tree ts = ok (core.result.Result.Ok f)) :
    (∀ env inp, TreeVarsAgree f env inp →
        ∀ k (hk : k < ts.val.length), treeBool env ts.val[k] = dagBool inp f.bits f.nodes (f.roots[k]).val) ∧
    (∀ env, ∃ inp, TreeVarsAgree f env inp) ∧                 -- lay the blocks out (pushforward)
    (∀ inp, ∃ env, TreeVarsAgree f env inp)                   -- read them back (pullback; needs injectivity)

/-- THE UNSAT CAPSTONE: no assignment to the caller's named variables satisfies the trees. -/
theorem tree_unsat_sound … (hf : flatten_tree ts = ok (Ok f))
    (ht : kernel.check_term_dag f.nodes f.bits f.roots map ns bits roots = ok (Ok ()))
    (hq : kernel.check_query ns bits roots hints steps = ok (Ok cnf)) :
    ∀ env : TEnv, ¬ TreeSat env ts.val

/-- THE SAT CAPSTONE: an assignment that reads every advertised value under its
    NAME satisfies the trees. -/
theorem tree_model_sound … (hf) (ht) (hm : kernel.check_query_model ns bits roots inp1 = ok (Ok ()))
    (hb : kernel.term_kernel.check_tree_model f map ns inp1 values = ok true) :
    ∃ env : TEnv, TreeSat env ts.val ∧
      ∀ k (hk : k < f.var_node.length), env (nameOf f k) (f.var_width[k]).val = BitVec.ofNat _ (values[k]).val

theorem tree_verdicts_exclusive … : False
```

`tree_unsat_sound` is `check_term_unsat_sound` composed with the first
two conjuncts; `tree_model_sound` is `check_term_model_sound`'s `inp0`
pulled back through the third and `check_input_value_sound` per entry.
The proof of `flatten_tree_sound` is one mutual structural induction on
the tree with the invariant "every node pushed so far denotes the subtree
it came from under `TreeVarsAgree`, the tables are consistent (name
lookup is exact, no two entries share a name), and the output so far is
`dag_wf`" — the prefix lemmas it needs (`dagSim_prefix_of_prefix`,
`dagSim_snoc`, `dagWidths` of a snoc) exist since phase 3/4.

**Sliver.** `kernel::term_kernel::flatten_ext_tree(ts: &[ExtBoolTerm])
-> Result<ExtFlat, FlatError>` produces the `ordeal-ext/v1` data
(`nodes: Vec<ExtNode>`, `bits`, `side`, `roots`, the variable table, and
the array / function tables by first appearance), `lower_ext` keeps
producing the lowered core and `images` by its own walk (untrusted), and
`flatten_sliver` is built against the kernel's `ExtFlat`; a disagreement
between the two walks is a `check_sliver_lowering` rejection (`Unknown`).
`flatten_ext_tree_sound` is stated with `extBool` on the right and with
`arrs` / `ufs` keyed by name on the left, through the injective id
tables; composed with `check_sliver_unsat_sound` it reads: **the
extended trees are unsatisfiable under every assignment, every array
interpretation and every UF interpretation, by name.**

### (A1) a mirror tree in the kernel, the public types copied into it

`ordeal-lrat` defines `term_kernel::{BvTerm, BoolTerm}` with `name:
Vec<u8>`; `ordeal` keeps `term.rs` as is and copies at the gate
(`mirror::of_bool: &term::BoolTerm → term_kernel::BoolTerm`, 37 + 13
arms, `name.as_bytes().to_vec()`), and the reverse copy of names for the
model. **Stays trusted:** that copy — mechanical, constructor for
constructor, no interning, no ordering, and tested by round trip and by
equality of the kernel's output with `dag::flatten`'s over every corpus;
but trusted. The same shape for the sliver (`ExtBoolTerm` with
`PureCall { args: Vec<_> }` copied into a cons-list of arguments if the
nested inductive is a problem, see below).

### (A2) `term.rs` *is* the kernel's type — no copy

Move the two enums (and `Sort`) into `crates/ordeal-lrat/src/term_kernel.rs`
exactly as they are — `name: String`, named-field variants,
`#[derive(Clone, Debug)]`, `#[non_exhaustive]` — and re-export them from
`ordeal::term`, so a consumer's `BvTerm` *is* the value the proven
flattener consumes: nothing is copied, nothing is trusted between the
caller's constructor calls and the kernel. `Name = String` in Lean, and
the lookup compares `String`s. This is the only option after which
**nothing between the API and the proofs is trusted** — and the spike
(below) says the pinned toolchain refuses it as stated: `Sort` is a Lean
keyword (a kernel-side rename, re-exported under the old name, fixes
that), the derived `Clone` / `Debug` impls of mutually recursive types
are "mixed-recursive declaration groups" (the impls can be written by
hand in `lib.rs`, outside the unit), and **every `String` operation is
an axiom** — equality included, which a name table cannot do without.
Two further costs it would carry even then: moving the enums out of
`ordeal` flips `#[non_exhaustive]` against ordeal's *own* matches (the
"every in-crate site is forced to handle a new op" property of #104
would be lost, or the attribute dropped), and the `Clone` / `Debug`
impls leave the type's definition site. Recorded as the follow-up that a
pinned Aeneas with a `String` model (or a maintainer decision to supply
one) unlocks; not recommended now.

### Leaves the trust base

`dag::flatten` / `DagBuilder::new(false)` (N1, N3, N4, N5), the width
guard as a soundness point (N2 — it stays as a diagnostic), the `vars`
table and the model's names (N6), `flatten_ext` / `ExtFlat` (N7), and
`ext_of_core` (N8; the kernel takes the extended trees, and a closed
assertion on a sliver solver is embedded by a kernel function of the
same 13 arms, proven value-preserving). **Stays trusted:** the front
ends; in (A1) the copy; the pieces every phase lists (Charon/Aeneas
faithfulness, Lean's kernel, the three axioms).

## Option (B): a proven correspondence check tree → D0, phase-7 style

Keep `dag::flatten` as the producer and add `kernel::check_tree_term(ts,
f) -> Result<(), E>`: a recursive walk of the tree with a cursor into
`f.nodes` that demands, subtree by subtree, the node the flattener would
have produced — the same constructor over the children's indices for an
operator, the memo'd node for a constant, the table's node for a name
(same lookup as (A), so N1/N2 are re-established the same way). The
theorem is `flatten_tree_sound`'s statement with `check_tree_term ts f =
ok (Ok ())` for `flatten_tree ts = ok (Ok f)`.

This is the shape phases 7 and 8 chose, and for the same reason it was
right there — the untrusted side makes decisions (canon's order, the
sliver's memo) that cannot be recomputed in the fragment — it is the
wrong shape here: the flattening makes **no** decision a checker would
have to be told; it is a deterministic serialization. A checker is the
builder with a comparison in place of a push, needs the same tables, the
same recursion, the same theorem — plus a cursor invariant — and buys
only that the production D0 is not computed by the kernel, which (A)
makes a non-issue by byte identity. (B) is the fallback if the positive
control ever shows the kernel flattener cannot reproduce `dag::flatten`
(it cannot fail to: both are the same post-order over the same tables).

## Option (C): prove `dag::flatten` as it stands — not buildable

`DagBuilder` is `HashMap`s keyed by `String` and by `(u8, usize, usize,
usize)`, `eval::bv_sort` with `?`, `fn`-pointer helpers (`bin`, `cmp`),
`Result` early returns inside recursion over `Box` trees, and `hash_cons`
shared with the production D1 builder. The phase-7 design listed exactly
these as outside the fragment (`kernel.rs` header: "no `&str`, no
`String`"; phase 7 "hit the `String` and `HashMap` walls on 267 + ~200
lines of canon/dag and chose a check"). Rewriting it in the fragment is
option (A). Listed for completeness, as `sliver-proof.md`'s (B).

## Option (D): a canonical serialization, parsed by a proven reader — dominated

Let the caller print its tree in a canonical text (the `term` block's
`canonical_text` already is one, node-shaped; a tree-shaped S-expression
would be closer to the caller) and prove a kernel *parser* of that text
into D0. Trust moves from a 37-arm flattener to a 37-arm printer — in
ordeal or, worse, in the caller — and adds a parser to the kernel, which
every phase has kept out of the trust base (certificate text parsing is
"explicitly NOT proven"). Its one merit is that it is the shape of the
*front-end* item (a minimal proven SMT-LIB reader, the maintainer's
"possible next item" of 2026-10-15), which is out of this document's
scope and would sit on top of (A), not replace it. Dominated by (A):
(A1) trusts a copy but no printer and puts no parser in the kernel;
(A2) would trust nothing at all.

## Aeneas feasibility: the spike

Everything the kernel has needed so far was loops over slices; the tree
needs **recursive types** (mutually recursive `BvTerm` / `BoolTerm`, with
`Box` fields; `Vec<ExtBvTerm>` inside `PureCall` for the sliver — a
nested inductive), **recursive functions** over them (mutually recursive
`flat_bv` / `flat_bool`, a loop with a recursive call inside for the
call arguments), **`Result` early returns inside the recursion**, and
either **byte-string names** (`Vec<u8>` compared by a loop) or
**`String` names** compared by `==`. What the pinned revisions
(`lean/toolchain-pins.env`: Aeneas `9dd45ecf`, Charon `40ee060a`) do with
each was measured, not guessed, on two standalone spike files translated
with the same binaries `lean/regen.sh` builds (the Nix store paths of the
main checkout had been collected; both tools were rebuilt from the
pinned revisions for this), then once more inside the real translation
unit. Verbatim results:

**Spike A — a mirror tree with `Vec<u8>` names and a `Vec<TBv>` of call
arguments** (`spike_a.rs`: `TBv { Const(u128, usize), Var(Vec<u8>, usize),
Add(Box, Box), Extract(usize, usize, Box), Ite(Box<TBool>, Box, Box),
Call(usize, Vec<TBv>) }`, `TBool { Eq, Not, And }`, a `Flat` with the
name arena, `name_is` / `lookup_var` / `push_var` / `push_const` as
loops, `flat_bv` / `flat_bool` mutually recursive with `?`, a `while`
over the `Vec` of arguments with a recursive call inside,
`flatten_tree` looping over the roots). Charon exit 0, Aeneas exit 0,
`SpikeA.lean` 697 lines, **`^axiom` count 0**; the types as a `mutual`
block of inductives, every recursive function and every loop as a
`partial_fixpoint` definition. Elaboration (`lake env lean`, the
worktree's pinned Aeneas library):

```
SpikeA.lean:57:0: error: (kernel) arg #2 of 'spike_a.TBv.Call' contains a non valid occurrence of the datatypes being declared
```

`| Call : Std.Usize → alloc.vec.Vec TBv → TBv` is refused by Lean's
kernel: Aeneas's `Vec T` is a *subtype* of `List T`, not an inductive, so
a `Vec` of subtrees inside a tree is not a valid nested inductive. **A
hard limit of the fragment: no `Vec<Tree>` field in a kernel tree type.**
The sliver's `PureCall { args: Vec<ExtBvTerm> }` cannot be the kernel's
shape as it stands.

**Spike A2 — the same with the arguments as a cons-list** (`Call(usize,
Box<Args>)`, `Args { Nil, Cons(Box<TBv>, Box<Args>) }`, `flat_args`
recursive): Charon 0, Aeneas 0, 700 lines, **`^axiom` count 0**,
**elaborates** (`LEAN_EXIT=0`, 3 s). The generated shape:

```lean
mutual
inductive TBv where
| Const : Std.U128 → Std.Usize → TBv
| Var : alloc.vec.Vec Std.U8 → Std.Usize → TBv
| Add : TBv → TBv → TBv
| Extract : Std.Usize → Std.Usize → TBv → TBv
| Ite : TBool → TBv → TBv → TBv
| Call : Std.Usize → Args → TBv
inductive Args where
| Nil : Args
| Cons : TBv → Args → Args
inductive TBool where
| Eq : TBv → TBv → TBool
| Not : TBool → TBool
| And : TBool → TBool → TBool
end

mutual
def flat_bv (t : TBv) (f : Flat) : Result ((core.result.Result (Std.Usize × Std.Usize) FlatError) × Flat) := do
  match t with
  | TBv.Const value w => …
partial_fixpoint
def flat_args (a : Args) (f : Flat) : Result ((core.result.Result Std.Usize FlatError) × Flat) := do
  match a with
  | Args.Nil => ok (core.result.Result.Ok 0#usize, f)
  | Args.Cons t rest => let (r, f1) ← flat_bv t f … let (r1, f2) ← flat_args rest f1 …
partial_fixpoint
def flat_bool (t : TBool) (f : Flat) : … partial_fixpoint
end
```

Two details of the output that shape the real code: `?` inside the
recursion is translated through `core.result.Result.Insts.CoreOpsTry.branch`
and `ControlFlow` matches (valid, but every arm doubles), whereas the
kernel's house style `match r { Ok(x) => x, Err(e) => return Err(e) }`
translates to a plain `match` — the implementation spells it the house
way; and every `while` of the spike is a `_loop` function with
`partial_fixpoint` too, i.e. **the recursion over the tree is the same
Lean mechanism the kernel's loops already are** (see the in-unit run
below), so the loop-spec discipline of `QueryCheck.lean` /
`TermCheck.lean` is the proof discipline here, with structural induction
on the tree in place of induction on the loop index.

**Spike B — `term.rs` verbatim** (`BvTerm` / `BoolTerm` / `Sort` as
shipped: `String` names, named-field variants, `#[derive(Clone, Debug)]`,
`#[non_exhaustive]`, plus `name_eq(a, b) = a == b`, `a.len()`,
`a.as_bytes()[j]`, and a recursive `size_bv` / `size_bool`): Charon 0;
Aeneas **exit 1**, 24 errors, 7 unique:

```
[Error] Name clash detected: the following identifiers are bound to the same name "Sort" (the generated code will be incorrect):
- keyword
- type name: spike_b::Sort
[Error] Mixed-recursive declaration groups are not supported
[Error] Mixed-recursive declaration groups are not supported
```

and in the partial file, **7 `axiom`s**: `core.fmt.Formatter.debug_tuple_field2_finish`,
`Box.Insts.CoreFmtDebug.fmt`, `alloc.string.String.Insts.CoreCmpPartialEqString.eq`,
`alloc.string.String.as_bytes`, `alloc.string.String.len`,
`alloc.string.String.Insts.CoreCloneClone.clone`,
`alloc.string.String.Insts.CoreFmtDebug.fmt`. The "mixed-recursive
groups" are the derived `Clone` / `Debug` impls, which are mutually
recursive with each other across the two types; `Sort` is a Lean keyword.

**Spike B2 — `term.rs` with the accommodations** (`Sort` → `BvSort`; no
derives inside the unit; `#[non_exhaustive]` and `String` kept; the
three `String` operations and a `lookup` over `&[String]`): Charon 0,
Aeneas 0, 337 lines, the two enums as a `mutual` block with `| Var :
String → BvSort → BvTerm`, the recursion as `partial_fixpoint` — and
**4 `axiom`s**, one per string operation:

```
axiom core.str.Str.as_bytes : Str → Result (Slice Std.U8)
axiom alloc.string.String.Insts.CoreCmpPartialEqString.eq
axiom alloc.string.String.as_bytes : String → Result (Slice Std.U8)
axiom alloc.string.String.len : String → Result Std.Usize
```

The pinned Aeneas library models `&str` as bytes (`Aeneas/Std/StringDef.lean`:
`def Str := Slice U8`) but has no model of any `String` / `str`
operation; the only thing a name table needs — equality — is an axiom.
So **(A2) as stated is refused by the pinned toolchain**: a `String`
field translates, but nothing can be *done* with it without an axiom,
and the project's gate (*Generated models carry no axioms*) and its
precedent (TR-044: `unsigned_abs` was rewritten as `lit_var`, not
modelled) both say no. What would make (A2) possible: a one-line
hand-written model `String.eq a b = ok (a == b)` supplied through
Aeneas's `-split-files` externals (a *new kind* of trusted item — a
hand model of a std function — of the same class as Aeneas's own `Vec`
models, which the project already trusts, but one the project has so
far refused to add itself), or a future pinned Aeneas that ships the
model. Either is a maintainer decision, not a design one; this document
recommends against adding the model now and records (A2) as the
follow-up it unlocks.

**In the real translation unit** (branch `spike/flattener-aeneas`, one
commit: `crates/ordeal-lrat/src/term_kernel_spike.rs` = spike A2 over the
real `DagNode`, `#[path]`-included into `kernel.rs`; `lean/regen.sh all`
with the pinned tools rebuilt from the pins; then `lake build Kernel`):

```
=== cargo build -p ordeal-lrat
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.84s
=== lean/regen.sh all
[Info ] Generated: lean/Kernel.lean
regenerated lean/Kernel.lean
regen exit: 0 seconds=11
=== Kernel.lean:    11867 lines, ^axiom count: 0
11159:inductive term_kernel_spike.TBv where
11160:| Const : Std.U128 → Std.Usize → term_kernel_spike.TBv
11161:| Var : alloc.vec.Vec Std.U8 → Std.Usize → term_kernel_spike.TBv
partial_fixpoint occurrences in Kernel.lean: 3        (flat_bv, flat_args, flat_bool — the only ones in the model)
=== lake build Kernel
✔ [1692/1693] Built Kernel (34s)
Build completed successfully (1693 jobs).
lake exit: 0 seconds=39
```

So the whole unit — checker, lowering, sliver check and the tree
flattener — regenerates with **zero axioms and builds**. One precision on
mechanism: the kernel's `while` loops translate to Aeneas's `loop`
combinator (`Aeneas/Std/Primitives.lean` 280, a fixed recursive
definition proven about once in the library, with the body a separate
`_loop.body` function) — that is what every existing loop spec reasons
about — whereas a recursive Rust function becomes a *user-level*
`partial_fixpoint` definition. The three in the regenerated model are
the spike's; **`partial_fixpoint` on a kernel function is new to this
project's proofs** (the mechanism beneath `loop` is the same Lean
feature, but no `QueryCheck` / `TermCheck` / `SliverCheck` lemma has had
to unfold one). Aeneas's own `tests/lean/Avl/Properties.lean` proves
specs of such definitions by `unfold` under induction on the tree, which
is the shape every statement here has (`= ok (Ok f) → …`, partial
correctness; no termination argument is needed, the tree is finite).

The spike branch is not to be merged; its one commit is the record
(`spike/flattener-aeneas`: `crates/ordeal-lrat/src/term_kernel_spike.rs`,
the `#[path]` line in `kernel.rs`).

## Comparison

| | (A1) proven flattener, mirror + copy | (A2) proven flattener, `term.rs` in the kernel | (B) correspondence check | (C) Aeneas over `dag.rs` | (D) canonical text + proven reader |
|---|---|---|---|---|---|
| leaves the trust base | N1–N8 | N1–N8 | N1–N8 | — | N1–N8 |
| stays trusted (beyond the front ends) | the 50-arm copy, the name bytes → `String` for the model | **nothing** | as (A1) or (A2) | — | the printer, a parser in the kernel |
| theorem stated over | the mirror tree (`List U8` names) | **the caller's `BoolTerm`** (`String` names) | the mirror or the caller's tree | — | the text |
| new Lean | `treeBv` / `treeBool` (~37 arms over `dagNodeVal`'s RHS), builder invariant by structural induction, two layouts, name-table lemmas, capstones; sliver: `treeExtBv`, id tables | same | same + a cursor invariant | — | same + a grammar |
| Aeneas novelty | recursive types and functions (`partial_fixpoint`), `Vec<u8>` compare | + `String` field and `String ==`, derives, `#[non_exhaustive]` | as (A) | not in the fragment | + a byte parser |
| production path | `dag::flatten` → `flatten_tree` (byte-identical; `dag::flatten` kept as the differential twin) | same | unchanged | — | unchanged |
| certificate / bundle bytes | unchanged (`ordeal-term/v1`, `ordeal-ext/v1`, `ordeal-cert/v4`) | unchanged | unchanged | — | new text block |
| API | unchanged (`Solver::assert(BoolTerm)`) | unchanged in shape: `ordeal::term::*` become re-exports of `ordeal_lrat::term_kernel::*` (`#[non_exhaustive]`, `Clone`, `Debug` kept) | unchanged | — | unchanged |
| what loom certifies | "the trees I built are unsat / this model, by name, satisfies them" — modulo the copy | the same, **with no modulo** | as (A1)/(A2) | — | modulo the printer |
| Lean effort (core) | ~1300–1800 lines | same | ~1500–2000 | — | ~2000+ |
| Lean effort (sliver) | +900–1300 | same | same | — | same |
| **spike verdict** (pinned toolchain) | **0 axioms, regenerates and builds in the unit** (cons-list arguments; no `Vec` of subtrees) | **refused**: `Sort` keyword, derives, 4–7 `String` / `Debug` axioms | as (A1) | not in the fragment | untested (dominated) |

## Recommendation and plan

**(A1).** The flattening is a serialization with two semantic decisions
in it (name identification, N1/N2; constant identity, N3), and a
*builder* proven once is the right shape for a serialization — no hints,
no map, no "the check rejected our own flattening ⇒ `Unknown`" failure
mode, completeness by construction. The spike settles the variant: the
mirror with `Vec<u8>` names and cons-list call arguments regenerates in
the real unit with zero axioms and builds; the shipped `term.rs` does not
translate without `String` axioms. What (A1) leaves is one sentence in
`docs/formal-verification.md`: "**what stays trusted: the SMT-LIB / Verus
front ends, and the 1:1 copy of the trees into the kernel's mirror type
(`mirror.rs`, constructor for constructor, names as bytes, no
interning, no ordering)**" — strictly smaller than today's clause (the
flattener *and* the names *and* the width guard), and the copy is made
small and checkable: it is a bijection (`to_term(of_term(t)) == t`,
tested over every seeded corpus) and its image flattens to exactly what
`dag::flatten` produced (the byte-identity control). (A2) is the
follow-up that removes the sentence entirely, gated on a `String` model
in the pinned Aeneas. (B) is phase 7's answer to a question this step
does not pose. The byte-identity positive control (`flatten_tree ∘ of ==
dag::flatten` over the latency, bmc, `0x192`, `0xC0FFEE` and sliver
corpora, then the 29-file CLI comparison against the published v0.33.0
binary) is what lets the production path switch with no bundle change.

- **9a (this document):** design; decision requested. One issue to file
  now, independent of the decision: F1 (an out-of-range `Const` degrades
  every sliver answer; a `debug_assert` panic in debug builds).
- **9b (kernel + proof):** `crates/ordeal-lrat/src/term_kernel.rs`
  (`#[path]`-included into `kernel.rs`, one translation unit): the
  mirror types (`TBv` / `TBool`, names as `Vec<u8>`, `u32` widths as
  `Sort` has them; the sliver's `TExtBv` / `TArray` / `TArgs` cons-list),
  `Flat`, `flatten_tree`, `check_tree_model`, `ext_of_core`'s twin, and
  `flatten_ext_tree` — in the house style (explicit `match` on every
  `Result`, no `?`, every loop its own function). `lean/TreeFlatten.lean` (core) and the sliver half
  (same file or `TreeFlattenExt.lean`), the capstones pinned in
  `AxiomCheck.lean`; the negative controls (each a one-line kernel
  mutation, regenerated, the named proof fails, the source restored):
  `lookup_var` ignoring the width (`NameWidth` dropped →
  the pullback conjunct), `name_is` comparing lengths only (two names on
  one node → the pushforward's well-definedness, F2's shape), a `Const`
  arm pushing `value >> 1`, a `Sub` arm with swapped operands.
- **9c (untrusted side):** `crates/ordeal/src/mirror.rs` (the copy
  `of_bool` / `of_ext_bool` and the name bytes back to `String` for the
  model; the round-trip test), the gate on `flatten_tree` (`gate_unsat`
  / `gate_sat`, the sliver gates), `QueryTerm` built from `Flat`,
  `Model` names from the kernel table, `dag::flatten` demoted to the
  differential twin (`tests::flatten_tree_matches_dag_flatten` over
  every corpus — the positive control; `denotation_guard` and the Z3
  differential through the new gate), the `tamper` hook extended to the
  kernel table (potency: every entry point `Unknown` when the table is
  swapped before the binding), the F1 fix (masked interning), the 24
  fixtures and the digests unchanged, the 29-file CLI byte comparison.
- **9d (docs):** `docs/formal-verification.md`'s trust list,
  `docs/consuming-ordeal.md` ("re-run `ordeal_lrat::flatten_tree` and
  compare"), `lean/README.md`, `ARCHITECTURE.md`'s pipeline map.
- **Not in this phase:** the SMT-LIB / Verus readers (the front-end
  item; a proven reader would sit on (A2)'s tree type); loom's switch to
  `Solver::from_sliver` (loom#433); per-array widths.

### Rivet

Following TR-072's shape (`rivet trace TR-072`: a `sw-req` deriving from
SYS-002 / SYS-003 / SYS-007, tracing to the earlier #192 requirements,
allocated to ARC-002 / ARC-006 / ARC-011, verified by one
`sw-verification` with one `verification-execution` and its verdicts),
the next free ids on this tree (`rivet list`, 2026-10-21; `rivet
release status v0.34.0` has no artifact scoped yet) are:

| id | type | content |
|---|---|---|
| **TR-073** | sw-req | "The flattening is proven — `flatten_tree` / `flatten_ext_tree` relate the caller's trees, names included, to the term and extended node lists, so every answer rests on the query as the caller built it"; `release: v0.34.0`; derives-from SYS-002, SYS-003, SYS-007; traces-to TR-069, TR-070, TR-072; allocated-to ARC-002, ARC-006, ARC-011 |
| **VER-073** | sw-verification | the Lean capstones, the negative controls, the byte-identity positive control, the tamper potency control, the verdict scan, the CLI byte comparison, the cost table; verifies TR-073 |
| **VE-063** | verification-execution | the run record of VER-073 |
| **VV-132 …** | verification-verdict | one per VER-073 item (VV-131 is the last today) |
| DES-027 / UV-026 | sw-detail-design / unit-verification | only if a design element is wanted for `term_kernel` (refines ARC-006; TR-072 shipped without one) |

None is created by this phase; `rivet validate` after they are.

## Open risks

- **Recursion in the proof.** User-level `partial_fixpoint` definitions
  are new to this project's Lean (measured: the three in the regenerated
  model are the spike's). Every statement here is a partial-correctness
  statement (`= ok (Ok f) → …`), proved by structural induction on the
  *tree* with the definition's unfolding equation, so nothing about
  termination is needed and no fuel appears; Aeneas's own
  `tests/lean/Avl/Properties.lean` does exactly this (`unfold
  Node.insert` under induction). The risk is proof-engineering (the
  `mutual` induction principle over `TBv` / `TArgs` / `TBool`), not
  mathematics; the first week of 9b establishes the pattern on
  `treeBool` / `flat_bool` alone.
- **No `Vec` of subtrees** (measured: Lean's kernel refuses the nested
  occurrence through Aeneas's subtype `Vec`). The sliver mirror carries
  `PureCall`'s arguments as a cons-list (`TArgs::Cons(Box<TExtBv>,
  Box<TArgs>)`), which regenerates and builds; the copy from the public
  `Vec<ExtBvTerm>` is part of `mirror.rs`. Nothing else in the two term
  languages holds a `Vec` of terms.
- **`String` in the kernel.** Measured: refused without axioms
  (`String ==`, `as_bytes`, `len` are all axioms in the pinned Aeneas;
  `Str` is modelled as bytes but its operations are not). (A1)'s
  `Vec<u8>` is the fragment's native answer; (A2) waits on the
  toolchain or on a maintainer decision to supply a one-line hand model
  of `String::eq` through `-split-files` — against the TR-044 precedent,
  so not assumed here.
- **Performance.** The name lookup is a linear scan with byte compares
  (no `HashMap`): `O(nodes × variables × name length)` per flattening.
  At loom's shape (≤ 4096 nodes, tens of variables, short names) that is
  well under the 0.1 ms `term_map` already pays; if a corpus ever shows
  it, the lever is an untrusted per-occurrence hint (`reuse`'s
  discipline: "this `Var` is entry `k`", verified by one compare) — a
  change to the untrusted side and the hint only.
- **Byte identity across the switch.** Constant interning by the *raw*
  value (N3) must be kept in the kernel for the `term` block bytes to be
  unchanged; it is also the behaviour F1 wants fixed on the sliver's
  *mapper* side (reconstruct and intern consistently), not in D0. If the
  maintainer prefers masked interning everywhere, the `term` block of
  queries with out-of-range constants changes bytes (none in the
  repository's 29 query files; `ordeal-term/v1` keeps its tag because
  the semantics is unchanged).
