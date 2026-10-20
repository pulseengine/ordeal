# Design: the proven sliver — array/UF elimination under the trusted check

**Status:** design and feasibility, 2026-10-20; **option (A′) approved by
the maintainer the same day** (with `ordeal-cert/v4`, the hash-consed
lowered core, first-appearance ordering and the witness nodes) and
**delivered** (TR-072, v0.33.0 — the last section records what shipped
and where it departs from the design). **Scope:** the last trusted step
between loom's question and ordeal's answer — `sliver::lower` — and how
to put it under the proven chain of #192.

## The claim being protected

Since v0.32.0 (TR-070) every answer rests on three proven checks in the
trusted crate `ordeal-lrat`:

| check | theorem | what it relates |
|---|---|---|
| `kernel::check_term_dag` | `check_term_dag_sound`, `check_term_unsat_sound`, `check_term_model_sound` (`lean/TermCheck.lean`) | the query as asked, flattened 1:1 (**D0**), to the solver's canonicalized, hash-consed DAG (**D1**) |
| `kernel::check_query` | `check_query_sound` (`lean/QueryCheck.lean`) | D1 to the CNF the LRAT proof refutes |
| `kernel::check_query_model` | `check_query_model_sound` | D1 to the model |

The semantics on both sides of every theorem is `dagBool` / `dagSim` —
Lean `BitVec` (`lean/BlasterDag.lean`).

For a **sliver** query (`crates/ordeal/src/sliver.rs`: `ExtBoolTerm` /
`ExtBvTerm` / `ArrayTerm`, rivet DES-014/015/016, TR-008/028/066/067),
D0 is not the question. The question is the extended query **E** — with
`select`/`store` over `Array(BV32 → BV8)` and uninterpreted `pure_call`s
— and D0 is what `sliver::lower` made of it: eager read-over-write into
nested `ite`s, Ackermannization of the calls, pairwise congruence over
the reads and the call sites. The proven chain says "D0 is unsat" or
"this model satisfies D0". That D0 is equisatisfiable with E — and that
a model of D0 *is* a model of E under some array and UF interpretation —
is the trusted step. Pinned to the code:

| piece | what it decides | where | status |
|---|---|---|---|
| `Lowering::resolve_select` | read-over-write: `select(store(a,i,v),j)` ⇒ `ite(i = j, v, select(a,j))`, settled statically when both indices are top-level `Const` | `sliver.rs` 466–503 | trusted |
| `Lowering::read_at` | one fresh BV8 variable per `(array, lowered index term)`, memoized on `format!("{index:?}")` | 509–542 | trusted |
| `Lowering::ackermann` | one fresh variable per `(name, lowered args)`, memoized on `format!("{args:?}")`; signature consistency per name | 562–609 | trusted |
| `Lowering::array_congruence` | `idx_i = idx_j → read_i = read_j` for every pair of reads of one array, `(Const, Const)` pairs skipped | 627–647 | trusted (**the soundness core of symbolic indexing**, its own words) |
| `Lowering::congruence` | `args_i = args_j → res_i = res_j` for every pair of sites of one function | 654–683 | trusted |
| `lower_traced` | assertion order: the lowered originals, then array congruence, then UF congruence | 210–223 | trusted |
| `eval_const` | a ground extended term's constant value, by a dual-fill probe | 942–1074 | trusted, **and unsound** (below) |

This is also exactly what loom depends on. loom's tier-2 validator
(`loom-core/src/rule_solver.rs::lower_goal_ne`, as of origin/main
2026-10-20) calls `ordeal::sliver::lower(&[ExtBoolTerm::Ne(a, b)])`
**directly**, asserts the returned core into a fresh `Solver`, runs
`check_with_deadline`, and on `Unsat` calls `cert.recheck()`. So what
loom re-checks is a certificate about D0; the step from its memory
obligation to D0 is the untrusted Rust above, with no certificate and no
proof. loom's own memory/UF obligations (`verify_solver.rs`,
`memory_accesses`, `sliver_admits`) stand on it.

## What the current Rust relies on — and two holes

Every item below is a soundness point of `sliver::lower` as shipped. The
last column says what the trusted check of option (A′) must
**re-establish** (the check refuses a lowering that violates it, so the
Rust's correctness on that point stops being load-bearing) or what is
**out of the proof's scope**.

| # | point | where | why it matters | under (A′) |
|---|---|---|---|---|
| S1 | **Concrete fast path.** `select(store(a, i, v), j)` with `i`, `j` both top-level `Const` is settled without an `ite`: hit ⇒ `v`, miss ⇒ walk on. Only *top-level* `Const` counts (`as_const`); `Core(Add(Const, Const))` is symbolic. | `resolve_select` 484–500 | a wrong static equality is a wrong answer with a valid certificate (the CNF never sees the index) | **re-established**: the check compares the two `Const` nodes' bit strings itself (`bits_eq`, phase 7) and the Lean lemma "equal bits ⇒ equal value, unequal bits ⇒ unequal value" (`getLsbD_bvOfFn`) closes it; anything else must be an `Ite` over `Eq` |
| S2 | **Memo by `format!("{:?}")`.** Reads are shared iff their *lowered* index terms print the same; call sites iff their lowered arg lists print the same. `Debug` is derived, so this is structural equality of the lowered term — including variable names and widths. | `read_at` 510, `ackermann` 588 | sharing is what makes `a[5] ≠ a[5]` unsat; *over*-sharing (two different terms with one `Debug` string) would be unsound; `Debug` of a `String` is escaped, so it does not happen today | **re-established** structurally: in a hash-consed D0 two lowered subterms are equal iff they are one node, so the check's read table is keyed on the core index *node* and the call table on core arg *nodes*; a wrong share is a wrong node id and is rejected |
| S3 | **Fresh-variable names.** Read variables are `$sel:<array>:<c>` / `$sel:<array>:#<n>`, call results `$uf:<name>:<n>`. Nothing stops a caller's own `BvTerm::Var` from carrying one of these names. | `read_at` 517–524, `ackermann` 592 | **HOLE (confirmed 2026-10-20, probe since removed):** `Ne(select(a, 5), Var "$sel:a:5")` lowers to `Ne($sel:a:5, $sel:a:5)` and `Solver::check_sliver` returns a **certified `Unsat`** for a query that is satisfiable in the array theory; the same for `Ne(f(1), Var "$uf:f:0")`. loom's reflector names variables after Z3's declarations, so loom is not exposed in practice; the API contract is. | **re-established**: the check partitions D0's `Var` nodes into "image of an extended variable" (injective, as phase 7's `seen`), "registered read" and "registered call", each node in exactly one class. A caller variable aliasing a fresh one is two classes on one node — rejected. The Rust should also refuse `$`-prefixed caller names (`SliverError::ReservedName`), independently of the proof |
| S4 | **`base_fill`.** `SliverModel` is total (unlisted cells read as `base_fill`, default 0). | 693–705 | not a lowering concern — the array semantics is a total function, and the lowering never consults a fill | the Lean semantics takes `arrs : Nat → BitVec 32 → BitVec 8`, total by type; the sat-direction construction fills unread cells with `0`, which is one of the interpretations the unsat direction quantifies over |
| S5 | **`eval_const`'s dual-fill probe.** A ground extended term is "constant" iff it evaluates equal under `base_fill = 0` and `0xFF`. | 1063–1073 | **HOLE (confirmed 2026-10-20, probe since removed):** `(select(a, 7) + 1) & 0xFE` is `0` under both fills and `2` when `a[7] = 1`; `eval_const` returns `Some(0)`. A two-point probe does not decide constancy of an 8-bit function. Neither loom nor synth calls `eval_const` (GitHub code search, origin/main, 2026-10-20 — an index, not a proof), so the exposure is the API. | **out of scope** of the lowering proof; fix in the Rust: a base read that *reaches* evaluation (walk the chain with the ground indices; any miss ⇒ `None`) instead of a probe — the chain walk is `eval_array` with a "fell through" flag. Worth its own issue |
| S6 | **Calls and reads under dropped values and untaken branches are registered unconditionally.** A `store` value that the fast path skips is still lowered (its calls registered, its reads memoized) and then discarded; an `ExtOp::Ite` branch likewise. | `resolve_select` 475, `ExtOp::Ite` doc 122–131 | sound either way (congruence constraints are valid under every interpretation and never contradict a model), but the discarded term may be **absent from D0** while its call variable appears in a congruence root — or, for a function with one site, absent altogether | **accommodated**: the extended→core map is partial (`NONE` for a node with no image, as phase 7); a `Select`/`Call` node needs an image only where it is *live* (reached from a root through the chain walk); the sat-direction interpretation is built from the registered entries, which is a superset of the live ones |
| S7 | **Signature consistency per call name** (`call_sigs`): the first site fixes `(arg widths, result width)`; a later site that disagrees is `InconsistentCall`. | 568–586 | a UF has one signature; without the refusal two sites could be "congruent" at different widths | **re-established**: the function table carries one `(arity, widths, result width)` per id; every mapped call must match it; the Lean `ufs` is coerced to the declared width (`toW`) so a mismatch cannot be exploited anyway |
| S8 | **Array sorts** (`BadArraySort`): index width 32, value width 8, checked on every chain node, selected or not. | `lower_index`, `resolve_select` 476–482 | the read variable is BV8 and the `ite` branches must agree in width | **re-established** by the extended well-formedness check `ext_wf`: `Select` index of width 32, chain values of width 8, chain indices of width 32 (the fixed `32 → 8` is the Lean type of `arrs`; generalizing to per-array widths costs nothing in the proof and is not needed by loom) |
| S9 | **`(Const, Const)` congruence pairs are skipped** as "statically unequal" (`debug_assert_ne!` that equal constants never reach here because of the memo). | `array_congruence` 633–636 | if two *equal* constants ever had two read variables, the missing constraint would admit `a[5] ≠ a[5]` | **re-established**: the check skips a pair iff both index nodes are `Const` with *unequal* bits; two `Const` nodes with equal bits are two reads it demands a constraint for (or, with D0 hash-consed, one node — the memo is forced, not assumed) |
| S10 | **Ordering of the congruence roots.** Arrays in `BTreeMap` order of their names, reads in creation order, pairs `i < j`; then functions likewise. Only byte identity depends on it, not truth. | 629–631, 656–658 | the CNF, the certificate and the `term` block are byte-for-byte functions of this order | **made canonical**: the check enumerates the expected roots itself (array ids in first-appearance order, reads in table order, `i < j`; then functions), so the completeness proof is a loop invariant, not a counting argument. `sliver.rs` switches its two `BTreeMap`s to first-appearance order (a byte change for multi-array / multi-function sliver queries only; no shipped fixture is a sliver query — the CLI, `cli_baseline` and the digests are SMT-LIB core) |
| S11 | **Arity-0 calls** collapse to one variable (memo on an empty arg list), so no empty antecedent is built. | 649–653 | an empty `And` would have to be `true`; the code never needs it | **re-established** trivially: the expected shape for `n = 0` is the bare conclusion, and the table check forbids two entries for one `(fid, [])` |
| S12 | **`SliverError` refusals.** `BadArraySort`, `InconsistentCall`; `NonConcreteIndex` is dead since v0.11.0. `from_sliver` surfaces the refusal; the one-shots map it to `Unknown`. | 154–170, `solver.rs` 417–478 | a refusal is the conservative branch; it must stay a refusal in the new entry points | **kept** on the untrusted side (a refused query is never lowered, so there is nothing to check); the trusted check's own rejections (`SliverCheckError`) degrade to `Unknown`, exactly as `TermError` does today (`Solver::verdict`) |
| S13 | **`Lowered.reads` provenance is concrete-only** (a symbolic index has no `u32` to report), so a caller cannot rebuild a model's array contents at symbolic indices from `Lowered`. | 200–205, 260–262 | not a soundness point; a completeness gap for counterexample reporting | **replaced** by the certificate's read table `(read var, array id, index node)`: the model's array contents at *every* read come from evaluating the index node under the model — the Lean `pullback` construction, made available to the caller as a `SliverModel` |

Independently of the decision below, S3 and S5 are two issues to file
against the shipped Rust: S3 is a certified wrong `Unsat` reachable
through the public API, S5 a wrong `Some` from a constant helper. The
trusted check closes S3 by construction; S5 is a helper outside the
lowering and needs its own fix.

## The semantics (Lean), common to every option

The extended query is a node list, like the term and the DAG, with two
constructors beyond the closed fragment. In the kernel (Aeneas fragment:
`Copy` enums of `usize` fields, side tables instead of nested `Vec`s):

```rust
/// A node of the extended query (`ordeal-ext/v1`).
pub enum ExtNode {
    /// A closed-fragment node over extended operands (one for one with `DagNode`).
    Core(DagNode),
    /// `select` of array `aid` at BV32 node `idx`, through the store chain
    /// `side[s .. s + 2n]` — `n` `(index node, value node)` pairs, the
    /// outermost (most recent) store first; `n = 0` reads the base array.
    Select(usize, usize, usize, usize),           // (aid, idx, s, n)
    /// `pure_call` of function `fid`, result width `w`, arguments `side[s .. s + n]`.
    Call(usize, usize, usize, usize),             // (fid, w, s, n)
}
```

An `ArrayTerm` never has a value of its own in the Rust (`ArrayTerm` is
only ever consumed by a `select`, and the sliver is non-extensional), so
store chains are a side table of a `Select`, not array-valued nodes:
there is no array sort in the value universe and `DVal` stays as it is.

```lean
/-- An array interpretation: every array id is a total map BV32 → BV8. -/
abbrev Arrs := Nat → BitVec 32 → BitVec 8
/-- A UF interpretation: every function id is a total map from argument values.
    The call node coerces the result to its declared width (`toW`), so every
    `ufs` is an interpretation of every signature. -/
abbrev Ufs := Nat → List DVal → DVal

/-- Read-over-write, as `eval_array` walks it: the most recent store whose
    index equals `j` wins; past the chain, the base array. -/
def chainRead (arrs : Arrs) (vals : List DVal) (side : List Std.Usize) (aid : Nat)
    (j : BitVec 32) : Nat → Nat → BitVec 8
  | _, 0 => arrs aid j
  | s, n + 1 =>
    if toW 32 (vals.getD (side.getD s 0#usize).val dDflt) = j
    then toW 8 (vals.getD (side.getD (s + 1) 0#usize).val dDflt)
    else chainRead arrs vals side aid j (s + 2) n

def argVals (vals : List DVal) (side : List Std.Usize) (s n : Nat) : List DVal :=
  (List.range n).map (fun k => vals.getD (side.getD (s + k) 0#usize).val dDflt)

/-- The value of one extended node (`dagNodeVal` on the closed arms). -/
def extNodeVal (inp bits : List Bool) (arrs : Arrs) (ufs : Ufs) (side : List Std.Usize)
    (vals : List DVal) (nin : Nat) : ExtNode → DVal
  | .Core nd => dagNodeVal inp bits vals nin nd
  | .Select aid j s n =>
    ⟨8, chainRead arrs vals side aid.val (toW 32 (vals.getD j.val dDflt)) s.val n.val⟩
  | .Call fid w s n => ⟨w.val, toW w.val (ufs fid.val (argVals vals side s.val n.val))⟩

def extSim (inp bits : List Bool) (arrs : Arrs) (ufs : Ufs) (side : List Std.Usize)
    (e : List ExtNode) : List DVal := …   -- the `dagSimAux` fold with `extNodeVal`
def extBool (inp bits) (arrs ufs side) (e : List ExtNode) (i : Nat) : Bool :=
  bval ((extSim inp bits arrs ufs side e).getD i dDflt)

/-- An extended model satisfies the query: every asserted root is true. -/
def ExtSat (inp bits arrs ufs side e eroots) : Prop :=
  ∀ k (hk : k < eroots.length), extBool inp bits arrs ufs side e (eroots[k]).val = true
```

`extSim` is `dagSim` with two more arms, and the `Core` arm *is*
`dagNodeVal`, so every lemma of `BlasterDag.lean` about a closed node
(`dagNodeVal_congr_op`, the prefix lemmas `dagSim_prefix_of_prefix` /
`dagSim_snoc`, widths) lifts by one `cases`. Names — array, function and
variable — are not in the semantics: an array is its id, a function its
id, exactly as a variable is its `Var` node. The untrusted flattener
assigns ids by name, 1:1, in the same trust position as `dag::flatten`
and the `vars` table today ("the names stay trusted"): a consumer holding
the `ExtBoolTerm`s re-runs `sliver::flatten_ext` and compares the hash.

## Option (A): a trusted correspondence check, phase-7 style — as asked

The certificate carries E (the `ext` block), the lowered core D0 (the
`term` block, as today) and an untrusted map E → D0; the trusted
`kernel::check_sliver_lowering` verifies that D0 *is* the read-over-write
+ Ackermann + congruence elimination of E, with theorems transferring
unsat and sat across it. Three facts about the code force the shape; the
result is (A′), which is what the rest of this document means by "the
check".

**1. The map E → D0 is one-to-many as D0 stands.** `dag::flatten` is 1:1
on the *tree*, and the lowered `BoolTerm`s are trees with clones in them:
`resolve_select` clones the selected index `j` into every `Ite` level
(line 496), `array_congruence` clones every index into every pair,
`congruence` every argument. One extended index node has as many core
copies as levels and pairs that mention it. Phase 7's map is a function
term node → DAG node (`map[i]`, `NONE` or one image). **Fix: D0 is built
hash-consed** (`DagBuilder::new(true)`, the production builder; the
`term` block's `encoding` becomes `ordeal-term/v2` for sliver bundles).
Sharing is not a semantic decision — the Lean semantics is over the
shared list either way — and it makes the map a function again (many
extended nodes may share one image; that is fine, D1 is already shared).

**2. Memo identity needs node identity.** Two selects share a read
variable iff their lowered indices are structurally equal (S2). The check
cannot compare subtrees (no recursion over trees in the Aeneas fragment,
and a `Debug` string is not a Lean object). In a hash-consed D0,
structural equality of two lowered subterms *is* equality of node ids,
so the read table is `(read var node, array id, index node)` and a
select's base read is checked by `map[select.idx] == entry.idx`: one
comparison. The same for call sites and their argument nodes. This is
the same move as phase 7's "hash-consing made each key unique" in
`term_map`, and as `compact`'s reuse hints.

**3. A read's index may be absent from D0.** `select(a, j) = 0` lowers to
`Eq($sel:a:#0, 0)`: `j` appears nowhere in the core unless a congruence
root mentions it. The read table then has no core node to point at, and
the sat-direction interpretation (`arrs a (⟦j⟧) := value of $sel:a:#0`)
has nothing to evaluate. **Fix: the `term` block's D0 carries, after the
roots' cones, the lowered index of every read entry and the lowered
arguments of every call entry as non-root nodes** (the untrusted
`QueryTerm::flatten_sliver` appends them from `Lowered.reads` /
`Lowered.calls`, extended to carry the index *terms*). `dag_wf` does not
require reachability, `check_term_dag` skips nodes whose D1 image is
`NONE` (`term_step`, line 1543), and `term_map` already yields `NONE` for
a node without a candidate — so phase 7 is untouched. Every registered
read and call now has its index/arguments in the core, where the model
can evaluate them.

### (A′) The check: `kernel::check_sliver_lowering`

```rust
/// Why the lowering was rejected. Data-only, like `TermError`.
pub enum SliverCheckError { Ext(QueryError), Core(QueryError), MapLength, MapOutOfRange { node },
    NodeMismatch { node }, ChainMismatch { node, level }, ReadEntry { entry }, CallEntry { entry },
    VarClass { node }, RootMismatch, CongruenceMismatch { root }, Signature { fid }, TooLarge }

/// **The sliver correspondence check.** Is the lowered core `t` (constants
/// `tbits`, roots `troots`) — the D0 `check_term_dag` relates to the DAG —
/// the read-over-write + Ackermann + congruence elimination of the extended
/// query `e` (constants `ebits`, side table `eside`, roots `eroots`,
/// function signatures `sigs`), along the untrusted map `map` (extended
/// node → core node, `usize::MAX` = no image) and the untrusted tables
/// `reads` (3 per entry: read var node, array id, index node) and
/// `calls` (4 per entry: result var node, function id, first arg, arity;
/// args in `cargs`)?
pub fn check_sliver_lowering(
    e: &[ExtNode], ebits: &[bool], eside: &[usize], eroots: &[usize], sigs: &[usize],
    map: &[usize], reads: &[usize], calls: &[usize], cargs: &[usize],
    t: &[DagNode], tbits: &[bool], troots: &[usize],
) -> Result<(), SliverCheckError>
```

What it does, in the order the proof wants it:

1. `ext_wf(e, ebits.len(), eside, sigs) -> Vec<usize>` — widths of every
   extended node (`dag_wf` extended by two arms: a `Select` has width 8, its
   index width 32, every chain index width 32 and value width 8, the
   chain inside `eside`; a `Call` has its declared width, its args inside
   `eside` with the widths `sigs` declares for `fid`). `dag_wf(t,
   tbits.len())` for the core, as `check_term_dag` does.
2. **Tables.** Every `reads` entry: `var` is a `Var(8)` core node, `idx` a
   width-32 core node (no order between them is required: neither
   transport recurses through the core assignment — see the theorems);
   no two entries share `var`; no two entries share `(aid, idx)` (the
   memo, forced). Every `calls` entry: `var` is a `Var(w)` with
   `w = sigs[fid].width`, arity matches, each arg node has the declared
   width; no two entries share `var`; no two share `(fid, args)`.
3. **Variable classes** (S3): one pass over the core `Var` nodes with a
   class table — image of a mapped extended `Var` of the same width
   (injective, phase 7's `seen`), a `reads` var, a `calls` var; every
   core `Var` in exactly one class, and every core `Var` in *some* class
   (a core variable that is none of the three has no meaning on the
   extended side).
4. **Per node**, `i` ascending over `e`, when `map[i] != NONE`:
   - `Core(nd)`: `node_eq(map_node(map, nd), t[map[i]])` — the exact
     correspondence (`pMapNode`, phase 7), no swap, no mirror, no fold:
     the sliver rewrites nothing in the closed fragment.
   - `Call(fid, w, s, n)`: `map[i]` is the var of a `calls` entry with the
     same `fid` and `map[eside[s + k]] == cargs[entry.s + k]` for every `k`.
   - `Select(aid, j, s, n)`: the **chain walk** (its own function, state
     in locals — the Aeneas loop discipline of `kernel.rs`): `k := map[i]`,
     then for each level `l < n` with index node `x_l = eside[s + 2l]`,
     value node `v_l`: if `e[x_l]` and `e[j]` are both `Const` — equal bits
     ⇒ require `k == map[v_l]` and stop; unequal bits ⇒ next level with
     `k` unchanged (S1); otherwise require `t[k] == Ite(c, map[v_l], k')`
     with `t[c] == Eq(map[x_l], map[j])`, continue with `k := k'`. Past
     the chain: `k` is the var of a `reads` entry with `aid` and `idx ==
     map[j]`.
5. **Roots.** `troots.len() == eroots.len() + expected congruence
   roots`; `troots[k] == map[eroots[k]]` for `k < m` (`roots_corr`);
   then the canonical enumeration (S10): for each array id in order, for
   each pair `p < q` of its read entries not both-`Const`-unequal, the
   next root is `Or(Not(Eq(idx_p, idx_q)), Eq(var_p, var_q))`; for each
   function id, for each pair of its entries, `Or(Not(And(…And(Eq(a_p1,
   a_q1), Eq(a_p2, a_q2))…)), Eq(var_p, var_q))` with the left-nested
   `And` of `congruence` (bare `Eq` for arity 0, which the tables make
   unreachable). Shape checks are `node_eq` against the expected
   constructor over the table's nodes; no new evaluator.

Everything the untrusted side supplies — `map`, `reads`, `calls`,
`cargs` — is advice: a wrong entry is rejected, never accepted on a
different formula (phase 7's rule). There is no `cong` hint table: the
expected roots are computed, so the only way to pass is to have emitted
exactly them.

### The theorems (`lean/SliverCheck.lean`)

The one lemma both directions rest on — the sliver's `corr_values`:

```lean
/-- The two sides agree on everything the tables register: a read variable
    holds the array's byte at its index's core value, a call variable the
    function's result on its arguments' core values. -/
def TablesAgree (t tbits reads calls cargs) (arrs : Arrs) (ufs : Ufs) (inp1 : List Bool) : Prop :=
  (∀ r < reads.length / 3, dagVal inp1 tbits t (reads[3r]) =
      ⟨8, arrs (reads[3r+1]) (toW 32 (dagVal inp1 tbits t (reads[3r+2])))⟩) ∧
  (∀ c < calls.length / 4, dagVal inp1 tbits t (calls[4c]) =
      ⟨w_c, toW w_c (ufs (calls[4c+1]) (argValsCore inp1 tbits t cargs (calls[4c+2]) (calls[4c+3])))⟩)

/-- Extended variables read the same bits as their images (phase 7's
    `VarsAgree`, with `t` on the right). -/
def ExtVarsAgree (e t map) (inp0 inp1 : List Bool) : Prop := …

/-- **The syntactic correspondence is a semantic one.** -/
theorem sliver_corr_values (e ebits eside t tbits map reads calls cargs) (cv : SliverCorr …)
    (arrs ufs inp0 inp1) (hv : ExtVarsAgree e t map inp0 inp1)
    (ha : TablesAgree t tbits reads calls cargs arrs ufs inp1) :
    ∀ i (hi : i < e.length), img map i ≠ NONE →
      (extSim inp0 ebits arrs ufs eside e).getD i dDflt
        = (dagSim inp1 tbits t).getD (img map i).val dDflt
```

By induction on `i`: the `Core` arm is `pMapNode_val` (phase 7, reused
as is, since the operands' images are earlier nodes); the `Call` arm is
`TablesAgree` plus the induction hypothesis on the arguments; the
`Select` arm is a lemma on the chain walk, by induction on the chain,
with S1 discharged by `getLsbD_bvOfFn` on the two bit strings.

The two transports, and what each direction *needs*:

```lean
/-- UNSAT direction: an extended model pushes forward to a core model.
    Needs: the per-node correspondence, and that every congruence root is
    VALID (true under every interpretation) — it does not need the
    congruence set to be complete. -/
def pushforward (e ebits eside t map reads calls cargs) (inp0 : List Bool) (arrs : Arrs) (ufs : Ufs) :
    List Bool :=
  -- bit `o + j` of core `Var` node `v`: if `v` is the image of extended var `u`, bit `j` of `u`
  -- in `inp0`; if `v` is a read entry `(v, aid, x)`, bit `j` of `arrs aid ⟦ext index of the FIRST
  -- select mapped onto the entry⟧_{inp0,arrs,ufs}`; if a call entry, likewise through `ufs`.
  -- Defined on the EXTENDED side, so there is no recursion through `inp1`; the induction in
  -- `sliver_corr_values` reaches the index node of that first select before any select that
  -- uses the entry (its index precedes it in node order), which is what `TablesAgree` needs.
  …
theorem pushforward_sat (h : check_sliver_lowering … = ok (Ok ())) (inp0 arrs ufs)
    (hs : ExtSat inp0 ebits arrs ufs eside e eroots) :
    ∀ k (hk : k < troots.length), dagBool (pushforward …) tbits t (troots[k]) = true
  -- the first `m` roots by `sliver_corr_values`; a congruence root because
  -- `TablesAgree` makes both sides of `idx_p = idx_q → var_p = var_q` read `arrs aid` at
  -- one value (Ackermann's functional consistency — the only theory fact used).

/-- SAT direction: a core model pulls back to an extended model.
    Needs: the per-node correspondence, and that the congruence set is
    COMPLETE — it is what makes the interpretation well defined. -/
def pullbackArrs (t tbits reads) (inp1 : List Bool) : Arrs :=
  fun aid v => match (first read entry `(r, aid, x)` with `toW 32 ⟦x⟧ = v`) with
    | some r => toW 8 ⟦r⟧ | none => 0#8
def pullbackUfs (t tbits calls cargs) (inp1 : List Bool) : Ufs := … (likewise; default `⟨0, 0#0⟩`)
def pullbackInp (e t map) (inp1 : List Bool) : List Bool := … (phase 7's `pullback`)
theorem pullback_tables_agree (h : …) (inp1) (hall : ∀ k, dagBool inp1 tbits t (troots[k]) = true) :
    TablesAgree t tbits reads calls cargs (pullbackArrs …) (pullbackUfs …) inp1
  -- for an entry `r` that is not the first with its index value: the congruence root for the
  -- pair (first, r) is among the roots `hall` makes true, its antecedent holds, so `⟦r⟧ = ⟦first⟧`;
  -- a skipped pair is two `Const`s with unequal bits, whose values differ (`getLsbD_bvOfFn`),
  -- so neither is "first with the other's value".
```

The capstones, composed with the unchanged phase-7 and phase-4/6
theorems:

```lean
theorem check_sliver_lowering_sound (e ebits eside eroots sigs map reads calls cargs t tbits troots)
    (h : kernel.check_sliver_lowering e ebits eside eroots sigs map reads calls cargs t tbits troots
          = ok (core.result.Result.Ok ())) :
    (∀ inp0 arrs ufs, ExtSat inp0 ebits.val arrs ufs eside.val e.val eroots.val →
        ∃ inp1, ∀ k (hk : k < troots.val.length), dagBool inp1 tbits.val t.val (troots.val[k]).val = true) ∧
    (∀ inp1, (∀ k (hk : k < troots.val.length), dagBool inp1 tbits.val t.val (troots.val[k]).val = true) →
        ∃ inp0 arrs ufs, ExtVarsAgree e.val t.val map.val inp0 inp1 ∧
          TablesAgree t.val tbits.val reads.val calls.val cargs.val arrs ufs inp1 ∧
          ExtSat inp0 ebits.val arrs ufs eside.val e.val eroots.val)

/-- **THE UNSAT CAPSTONE**: the extended query is unsatisfiable under EVERY
    assignment, EVERY array interpretation and EVERY UF interpretation. -/
theorem check_sliver_unsat_sound … (ns bits roots map1 hints steps cnf)
    (hs : kernel.check_sliver_lowering … = ok (Ok ()))
    (ht : kernel.check_term_dag t tbits troots map1 ns bits roots = ok (Ok ()))
    (hq : kernel.check_query ns bits roots hints steps = ok (Ok cnf)) :
    ∀ inp0 (arrs : Arrs) (ufs : Ufs), ¬ ExtSat inp0 ebits.val arrs ufs eside.val e.val eroots.val

/-- **THE SAT CAPSTONE**: an interpretation, built from the model, under which
    the extended query holds — and bound to the model: the variables through
    the two maps, the arrays at every read, the functions at every call. -/
theorem check_sliver_model_sound … (ns bits roots map1 inp2)
    (hs : …) (ht : …) (hm : kernel.check_query_model ns bits roots inp2 = ok (Ok ())) :
    ∃ inp0 inp1 arrs ufs, VarsAgree t.val ns.val map1.val inp1 inp2.val ∧
      ExtVarsAgree e.val t.val map.val inp0 inp1 ∧ TablesAgree … arrs ufs inp1 ∧
      ExtSat inp0 ebits.val arrs ufs eside.val e.val eroots.val

theorem sliver_verdicts_exclusive … (hs) (ht) (hq) (hm) : False
```

`check_sliver_unsat_sound` is `check_term_unsat_sound` applied to the
pushforward; `check_sliver_model_sound` is `check_term_model_sound`'s
`inp1` pulled back. `TermCheck.lean` and `QueryCheck.lean` are not
touched; `AxiomCheck.lean` pins the four new capstones.

### Leaves the trust base

`sliver.rs`'s `Lowering` entirely (S1, S2, S3, S6–S11). **Stays
trusted:** the extended flattener `sliver::flatten_ext` (1:1 on the
`ExtBoolTerm` tree, ids by name — the consumer re-runs it and compares
hashes, as for `dag::flatten` today), the names, `eval_const` (S5, its
own fix), the front ends, and the pieces every phase has listed
(Charon/Aeneas faithfulness, Lean's kernel, the three axioms).

### Lean effort

Anchors: `TermCheck.lean` is 2658 lines for the 680 Rust lines of
`check_term_dag` (kernel.rs 1016–1694) — about 4 Lean lines per Rust
line, with the loop specs and the transports the bulk; `QueryCheck.lean`
is 1215 lines for ~330 Rust lines (`dag_wf`, `roots_wf`, the capacity
checks, `check_query`, `check_query_model`). The check above is ~700–800
Rust lines (`ext_wf` ~120, tables and classes ~150, chain walk ~120, per
node ~80, canonical roots ~180, driver ~100). Estimate, by section:

| section | lines | anchor |
|---|---|---|
| `extSim` and its lifts of the `dagSim` lemmas (prefix, snoc, widths, `ext_wf_spec`) | 450–600 | `BlasterDag.lean` 48–400 + `QueryCheck.lean` `dag_wf_spec` |
| pure mirrors and `_eq` equations of the new total helpers, `ExtNode` tag/field lemmas | 250–350 | `TermCheck.lean` 50–220 |
| `sliver_corr_values` (`Core` arm reused, chain-walk lemma, call arm) | 400–550 | `corr_values` 875–965 + `pMapNode_val` |
| canonical-roots loop specs and `cong_root_valid` / `cong_set_complete` | 400–550 | `check_term_dag_loop2_spec` |
| variable classes (`VarClass` invariant, injectivity) | 200–300 | `LoopFacts` / `VarInj` |
| `pushforward`, `pushforward_sat` | 300–400 | `pushforward` / `varsAgree_pushforward` 1100–1300 |
| `pullbackArrs` / `pullbackUfs` / `pullback_tables_agree` (classical choice over "first entry with this value") | 350–450 | `pullback` + new |
| `check_sliver_lowering_accepted` (the `SliverCorr` assembly) and the four capstones | 300–400 | `check_term_dag_accepted` … `term_verdicts_exclusive` |

**≈ 2700–3600 lines**, i.e. 1.0–1.35 × `TermCheck.lean` — the largest
single proof file so far but entirely in its pattern, with the per-node
`Core` case and the two transports reused rather than re-proved. The
risky items are the chain-walk lemma (a loop whose state is a core node
id, with the fast path a `cases` on two `Const`s) and the choice-based
pullback (well-definedness through the congruence roots).

### Aeneas risks

- **No names, no maps, no strings reach the kernel.** Arrays and
  functions are ids; the memo is node identity; the tables are flat
  `&[usize]` slices with fixed strides (3 and 4), the chains and
  arguments live in `eside` / `cargs`. All of it is advice, all of it is
  checked. This is the phase-7 discipline (`kernel.rs` header: "no
  `&str`, no `String`"; the `HashMap` of `dag.rs` replaced by the checked
  map) applied once more.
- **Nested enum match**: `ExtNode::Core(DagNode)` is a two-level enum.
  Phase 7 already matched `DagNode` 37 ways inside loops (`node_tag` …);
  the pinned Charon handles a nested `match` when the inner scrutinee is
  copied into a local first (`dag_nin`'s comment). Mitigation if it does
  not: flatten `ExtNode` into `DagNode` by adding `Select`/`Call`
  constructors to `DagNode` itself, with `encode_node` rejecting them —
  touches the proven encoder's exhaustiveness, so a last resort.
- **Loops with early exits**: the chain walk and the canonical-root
  enumeration are nested loops; each inner loop is its own function
  carrying its verdict in a local (the `roots_corr` pattern), per the
  "no early `return` inside nested loops" rule.
- **Capacity**: `reads.len() / 3`, `calls.len() / 4`, and the expected
  root count `Σ C(n_a, 2) + Σ C(n_f, 2)` must be computed with overflow
  checks (`TooLarge`), as `encode_fits` / `tseitin_fits` are.
- **No `u128`** anywhere: constants are compared as bit strings
  (`bits_eq`), never evaluated.
- The one Aeneas *novelty*: `classical` choice in `pullbackArrs` is on
  the Lean side only; the kernel never computes an interpretation.

### Certificate format: `ordeal-cert/v4`, additive

A v4 bundle is a v3 bundle plus one block, `ext`, after `term`;
`format: "ordeal-cert/v4"`; v1/v2/v3 readers refuse it by `format`
exactly as v1/v2 readers refuse v3 (`from_cert_v3`, cert_bundle.rs
1149–1160: the first thing read is `format`). A core query keeps
producing v3 — byte for byte — because it has no `ext` block to carry;
v4 is emitted only through the sliver entry points. The `term` block of a
v4 bundle is `encoding: "ordeal-term/v2"` (hash-consed, with the read
indices and call arguments appended as non-root nodes; a v3 reader that
somehow saw it would refuse the encoding, as `term_from_block` refuses an
unknown `encoding` today).

```jsonc
"ext": {
  "encoding": "ordeal-ext/v1",
  "num_nodes": N, "nodes": [["op", arg…], …, ["select", aid, idx, s, n], ["call", fid, w, s, n]],
  "bits": "0101…", "side": [ … ], "roots": [ … ],
  "vars":   [{ "name": "x", "width": 32, "node": 3 }, …],       // untrusted names
  "arrays": [{ "name": "mem", "id": 0 }, …],                     // untrusted names
  "funcs":  [{ "name": "f", "id": 0, "width": 8, "args": [32] }, …],
  "map": [ … ],                                                  // ext node → term node, usize::MAX = none
  "reads": [[var, aid, idx], …], "calls": [[var, fid, s, n], …], "cargs": [ … ],
  "sha256": "…"                                                  // over the canonical text, names included
}
```

`recheck.cmd` is `ordeal recheck --with-ext <bundle>` (the CLI gains the
JSON reader; it needs no SMT-LIB front end for arrays — the bundle is
self-contained). `SliverBundle::from_cert_v4(..).recheck()` runs
`check_sliver_lowering`, then `check_term_dag`, then `check_query` (or
`check_query_model` and the binding checks), and a sat recheck
additionally rebuilds the `SliverModel` by the pullback and re-evaluates
every `ExtBoolTerm` with `eval_ext_bool` as untrusted defence in depth.

### How loom's API carries the check

loom does not use `check_sliver*` (its own words: "deliberately NOT");
it lowers with `sliver::lower` and asserts the core. The change is to
make the solver remember the extended query and gate on it:

- `Solver` gains a private `sliver: Option<SliverTrace>` (`E` flattened,
  the `Lowered` tables, the map). `Solver::from_sliver` (TR-067, already
  the entry loom is meant to use) sets it; `Solver::assert` on such a
  solver appends the core assertion to both sides (a `BoolTerm` embeds
  into `ExtNode::Core` 1:1). `check` / `check_with_deadline` /
  `check_with_limit` / `check_with_term` are unchanged in signature and
  run `check_sliver_lowering` in `gate_unsat` / `gate_sat` before
  `check_term_dag` when the trace is present — the TR-070 shape: the
  gate is on every path, and a rejection is `Unknown`.
- loom's `lower_goal_ne` returns `Solver::from_sliver(&[Ne(a, b)])`
  instead of `sliver::lower(..)` + `assert` — one line in loom, and its
  `check_with_deadline` + `cert.recheck()` keep working. The refusal
  stays an `Err(SliverError)` (TR-067).
- `Solver::check_sliver_with_term(&self) -> SliverCheckResult` (the
  sliver twin of `check_with_term`) exposes `SliverCertificate { ext,
  term, query, certificate }` with `recheck()` and `to_cert_v4()`, and on
  sat a `SliverSatCertificate` carrying the `SliverModel` built by the
  pullback (`arrays` at every read's evaluated index, `calls` at every
  site's evaluated arguments, the core `env`) — which closes S13 and gives
  loom a counterexample in its own vocabulary (`render_ordeal_model`
  today prints `$sel:`/`$uf:` variables).
- The one-shots `check_sliver`, `check_sliver_with_deadline`,
  `check_sliver_with_limit`, `prove_equiv_sliver` go through
  `from_sliver` already and inherit the gate.

### Performance: how big do the certificates get

Array congruence is quadratic in the reads of one base array, and the
UF congruence in the sites of one function. The question is what the
**check and the `ext` block add** on top of what the bundle carries
*today* — because the quadratic set of congruence roots is already in
the v3 `term` block (D0), in the `query` block (D1), in the CNF and in
the LRAT proof.

loom's measured shape (`verify_solver.rs`, `n` i32 store/load pairs, the
5000 ms deadline, release): 1 pair = 20 accesses / 0 ms; 2 = 72 / 3 ms;
4 = 272 / 15 ms; 6 = 600 / 37 ms; 8 pairs refuse at `MAX_TERM_NODES =
4096` before any lowering. loom's cap is `DEFAULT_MAX_MEMORY_ACCESSES =
1024` (selects + stores, both sides). Per pair of reads the bundle pays:

| item | per read pair | 6 pairs (24 distinct reads, 276 read pairs) |
|---|---|---|
| D0 / D1 nodes (`Or(Not(Eq32), Eq8)`, indices shared) | 4 nodes ≈ 60–120 B JSON per block | ≈ 20–60 KB per block (already in v3) |
| CNF: `Eq` over 32 bits ≈ 127 AND gates, over 8 bits ≈ 31, Tseitin ≈ 3 clauses/gate, ≈ 12 B/clause | ≈ 5.7 KB | ≈ 1.6 MB (already in v1) |
| LRAT proof: the solver's, 1–5 × the CNF in practice | 6–30 KB | 1.6–8 MB (already in v1) |
| **`ext` block, new:** nothing per pair — the tables are per read (3 ints) and per site (4 + arity); `map` is per extended node | **0** | reads 24 × 3 ints, `map` ≈ 1–2 k ints (one per reflected node): ≈ 10–15 KB |
| **check time, new:** `node_eq` per expected root, one pass per node | ≈ 1 µs | < 1 ms |

So at loom's sizes the `ext` block is under 1 % of the bundle, and the
check is linear in the bundle. At the theoretical cap (1024 accesses all
reads of one array: 5 · 10⁵ pairs, a CNF of ~2 · 10⁸ clauses) the
*solver* is the binding constraint by three orders of magnitude; the
certificate's quadratic part is the CNF, not the check. The honest
performance statement is: **the check adds no quadratic term of its
own; the quadratic term is the lowering's, is already in every bundle,
and is bounded by loom's `max_memory_accesses` before ordeal sees it.**
If that term ever matters, the lever is on the untrusted side (lazy
congruence — emit a pair only when the SAT core needs it — is the
standard answer and does not change the check, which verifies whatever
pairs are present for the unsat direction; it would, though, cost the
sat direction's completeness argument, see "Open risks").

## Option (B): prove `sliver::lower` itself (Aeneas over the existing Rust)

Not feasible as the code stands, and not worth making feasible:

- `sliver.rs` is outside the Aeneas fragment on every axis the phase-7
  design listed: `String` names and `format!("{:?}")` memo keys
  (`read_memo`, `call_memo`: `BTreeMap<(String, String), BvTerm>`),
  `BTreeMap`s with string keys (`array_reads`, `calls_by_name`,
  `call_sigs`), `Box`ed recursive enums with `Vec<ExtBvTerm>` arguments,
  recursion over trees, closures (`cmp`, `bin`), iterator chains with
  `?`, `Result` early returns inside recursion. Phase 7 hit the `String`
  and `HashMap` walls on 267 + ~200 lines of canon/dag and chose a check;
  this is 680 lines with more of each.
- Rewriting it in the fragment (ids for names, node lists for trees,
  reuse hints for the memo) is option (C). There is no middle: Aeneas
  translates what it translates, and the pieces that make `lower`
  readable Rust are exactly the pieces it does not.
- Even translated, the theorem would be about a *builder*: "the output
  of `lower` is equisatisfiable with its input". That is option (C)'s
  theorem, with a worse model (`BTreeMap` axioms in the Lean, if the
  support library even had them; it has `sorry`s in `Slice` and
  `StringIter` already, per `lean/README.md`).

**Leaves the trust base:** nothing, because it cannot be built. Listed
for completeness; the issue's option (B) for phase 7 was "dominated" for
the same reasons and this one is further behind.

## Option (C): a trusted lowerer in the kernel

`kernel::lower_sliver(e, ebits, eside, eroots, sigs, reuse) -> (t,
tbits, troots, reads, calls)`: the elimination re-implemented in the
Aeneas fragment, emitting a **hash-consed** core (so the memo is node
identity, as in (A′)) with the hash-consing driven by `reuse` hints
(`reuse[k]`: an earlier output node this one may share, checked by
`node_eq` — `compact`'s `hint_matches` over `DagNode`s), the read and
call tables computed as it goes (a linear scan over the entries of one
array/function per select/call — quadratic in total, the same order as
the congruence it then emits), and the congruence roots emitted in the
canonical order. The solver runs it (phase 2/3's "the solver runs the
proven code") or the certificate carries its output and the recheck
compares.

- **Theorem**: the same two-way statement as `check_sliver_lowering_sound`
  with `lower_sliver`'s output in place of a checked `t`, plus the
  composition. The proof is a *builder* invariant: after `k` extended
  nodes, the output is well-formed, every emitted node denotes what its
  extended source denotes under `TablesAgree`, the tables are
  consistent, the reuse hint was honoured only when sound. That is
  `encode_sound`'s shape (`BlasterProof.lean` + `BlasterDag.lean`, ~2900
  lines for a builder of comparable complexity) rather than
  `check_term_dag_sound`'s.
- **Effort:** ≈ 3200–4200 Lean lines (the same semantics and transports
  as (A′), plus the builder invariant in place of the per-node check,
  plus output well-formedness which (A′) gets from `dag_wf` for free).
- **Leaves the trust base:** the same as (A′). **Plus**: no map and no
  tables to get wrong on the untrusted side, so there is no "the check
  rejected our own lowering ⇒ `Unknown`" failure mode (completeness by
  construction; the reuse hints only steer sharing, as `compact`'s do).
- **Against:** the solver's production path changes for every sliver
  query (the proven lowerer's output replaces `sliver::lower`'s, or the
  two must be made byte-identical, which is the check again); the
  kernel grows by a builder with three tables; the untrusted `sliver.rs`
  stays as the *test* oracle only; and the sat-direction model
  construction is identical, so nothing is saved there.
- **When to prefer it:** if the per-node check's incompleteness ever
  bites — a lowering the Rust gets right but the check cannot verify.
  With D0 hash-consed and the appended witness nodes, the author knows
  of no such case: every decision `lower` makes is structural, and the
  check sees the structure.

## Comparison

| | (A′) correspondence check | (B) Aeneas over `sliver.rs` | (C) trusted lowerer |
|---|---|---|---|
| leaves the trust base | `Lowering` (S1–S3, S6–S11) | — (not buildable) | same as (A′) |
| stays trusted | `flatten_ext`, names, `eval_const` (S5), front ends | — | same |
| new Lean semantics | `extSim` (two arms over `dagSim`) | — | same |
| hints from the untrusted side | map, read table, call table | — | reuse hints |
| Lean effort | ≈ 2700–3600 lines; `TermCheck`'s pattern, nothing existing touched | — | ≈ 3200–4200; `encode_sound`'s pattern |
| Aeneas risk | nested enum, nested loops, flat tables — all seen before | `String`, `BTreeMap`, `Box` trees, closures: not in the fragment | the same as (A′) plus a growing output `Vec` of enums (seen in `encode`) |
| certificate | `ordeal-cert/v4` = v3 + `ext`; v1–v3 refuse by `format`; core queries unchanged | — | same block, minus `map`/tables, plus `reuse` |
| default bytes (sliver queries) | congruence order becomes canonical (S10): changes multi-array/function sliver CNFs; no shipped fixture | — | all sliver CNFs change (new lowerer) |
| default bytes (core queries) | unchanged | — | unchanged |
| completeness | the check can reject a correct lowering only through an untrusted-side bug (→ `Unknown`, sound) | — | by construction |
| what loom certifies | "the memory/UF obligation as asked is unsat under every array and UF interpretation" / "this interpretation is a counterexample" | — | same |

## Recommendation and plan

**(A′).** It is the phase-7 decision applied to the next trusted step,
with the same hint discipline, the same proof pattern, the same
additive certificate story, and no change to the production path of a
core query. The three amendments the code forces (hash-consed D0, witness
nodes, computed rather than hinted congruence order) are each a small
untrusted-side change and each *removes* a thing the check would
otherwise have to trust. (C) buys completeness-by-construction for
~500 more Lean lines and a changed production path, and is the fallback
if the check turns out to refuse real lowerings.

- **8a (this document):** design; decision requested. Two issues to file
  now, independent of the decision: S3 (reserved fresh names reachable
  through the API, certified wrong `Unsat`) and S5 (`eval_const`'s
  dual-fill probe is a two-point test).
- **8b (kernel + proof):** `crates/ordeal-lrat/src/sliver_kernel.rs`
  (`#[path]`-included into `kernel.rs`, one translation unit — phase 4's
  move): `ExtNode`, `ext_wf`, `check_sliver_lowering` and its helpers
  (`read_entry_ok`, `call_entry_ok`, `var_classes`, `chain_walk`,
  `expected_array_roots`, `expected_uf_roots`, `roots_corr_sliver`).
  `lean/SliverCheck.lean` with the capstones above, pinned in
  `AxiomCheck.lean`; the negative controls in the phase-7 style (fast
  path on *values* instead of bits, a skipped non-`Const` pair, a missing
  variable class, a dropped chain level — each a one-line kernel
  mutation under which the named proof fails). The `cargo` crate root
  re-exports `check_sliver_lowering`, `ExtNode`, `SliverCheckError`.
- **8c (untrusted side + certificate):** `sliver::flatten_ext`
  (`ExtQuery`: nodes, bits, side, roots, vars, arrays, funcs, sigs; 1:1,
  ids by first appearance), `sliver::lower_traced` extended to report
  the index *term* of every read and the canonical order (S10),
  `QueryTerm::flatten_sliver` (hash-consed D0 + witness nodes),
  `sliver::ext_map` (the map, computed after the fact as `term_map` is),
  `Solver::from_sliver` keeping the trace, the gate in
  `gate_unsat`/`gate_sat`, `Solver::check_sliver_with_term`,
  `SliverCertificate` / `SliverSatCertificate` with the pullback
  `SliverModel`, `ordeal-cert/v4` writer and reader (`to_cert_v4`,
  `from_cert_v4`, `recheck`), `ordeal recheck --with-ext`;
  `sliver::lowering::sliver_lowering_preserves_every_model` gains the
  trusted check as its positive control (every seeded query must pass
  it); `SliverError::ReservedName` (S3); the `eval_const` fix (S5).
- **8d (loom):** `lower_goal_ne` → `Solver::from_sliver`; the v4
  bundle as the evidence loom's safety case ingests; `render_ordeal_model`
  on the `SliverModel`.
- **Not in this phase:** per-array index/value widths (the Lean takes
  them as parameters at no cost; the Rust fixes `32 → 8`), extensional
  array equality (loom never asserts it), lazy congruence.

## Open risks

- **The check refuses a correct lowering.** By construction only an
  untrusted-side bug can cause it (a wrong map or table entry), and the
  outcome is `Unknown`, never a wrong verdict. The positive control over
  the 400-query seeded corpus of `sliver::lowering` plus loom's
  obligation corpus is the evidence; (C) is the fallback.
- **`pullbackArrs`'s well-definedness** is the subtle proof. It rests on
  the congruence set being complete *among the registered entries* and
  on skipped pairs being provably unequal. If the Rust ever emits
  congruence lazily (performance), the sat direction needs a different
  construction (the model's own read values, with the solver proving the
  missing pairs are satisfied — a check, not a proof, and it would weaken
  the capstone to "under this interpretation" without "built from the
  model"). Flag it before any lazy-congruence change.
- **Dropped-value registration (S6).** The design accommodates it; a
  simpler Rust (register only what is live) would shrink the tables but
  is not required and would change bytes. Leave it.
- **Nested-enum translation.** The one Aeneas item not previously
  exercised in this exact shape; the mitigation (fold `Select`/`Call`
  into `DagNode`) is known but touches the proven encoder's match
  exhaustiveness, so it is a last resort, to be tried in 8b's first
  week on a stub.

## What was delivered (TR-072, v0.33.0)

Option (A′) as designed, with the following departures, each forced by
the code or by the proof:

- **No `sigs` table.** A call node carries its result width
  (`ExtNode::Call(fid, w, s, n)`); the Lean `Ufs := Nat → List DVal → DVal`
  is coerced to the declared width at the call node, so every `ufs` is an
  interpretation of every signature — unsat under every coerced `ufs`
  implies unsat under every properly typed UF, and the sat direction
  constructs one. Signature consistency (S7) stays a Rust refusal; the
  check does not need it.
- **Every table entry must be live.** The proof found that the check as
  first written was unsound without it: a dead read entry whose index
  mentions its own variable — `($d, a, zext($d))` with the congruence root
  `¬(idx_p = zext($d)) ∨ $p = $d` against live constant reads `a[c] = c+1`
  — makes the core unsat (`$d = $d + 1`) while the extended query is
  satisfiable, and the kernel accepted it. The transport needs every read
  and call variable to be resolved by some mapped `select` or call (its
  value is then defined on the extended side, from the first such node),
  so the kernel refuses a dead entry (`DeadEntry`). This is the design's
  "pullback well-definedness" risk showing up in the *other* direction,
  and it is a point the Rust never had to think about. The lowering had one
  source of them: a `select` settled by a concrete hit still registered
  the base read it discarded. `resolve_select` now walks the rest of such
  a chain (sort checks, flattening, the calls inside the dropped values)
  but registers no read for it — that variable was unconstrained, so no
  verdict changes (the old-vs-new scan below is the evidence), and the
  design's S6 case ("dropped values may register entries nobody uses")
  no longer arises for reads.
- **The congruence order is the table's**, as designed (S10): pairs
  `p < q` of the access set in creation order, then of the call sites;
  `sliver.rs` lost its two `BTreeMap`s. The check computes the expected
  roots; there is no `cong` hint.
- **One walk.** `sliver::lower_ext` flattens and lowers in the same
  traversal, so the extended node ids and the lowered images of every
  `select` and call come from one place; `flatten_ext` is the consumer's
  half of it. The mapper (`QueryTerm::flatten_sliver`) interns rather
  than searches: a variable by name, a constant by value, a closed
  operator as the operator over its operands' images
  (`DagBuilder::intern_node`), a `select` or call by its lowered term —
  the hash-consed D0 makes each of those a lookup.
- **The SAT certificate carries the extended model** and the recheck
  re-derives it from the certificate alone (`SliverBlock::pullback_model`:
  the lowered core evaluated under the model with the proven encoder and
  simulator, the arrays read at every read's index value, the functions
  at every call's argument values) — S13 closed without the trace.

Files: `crates/ordeal-lrat/src/sliver_kernel.rs` (the check;
`kernel.sliver_kernel.*` in the generated model), `lean/SliverCheck.lean`
(the proof; the capstones pinned in `AxiomCheck.lean`),
`crates/ordeal/src/sliver.rs` (`lower_ext`, `flatten_ext`, `ExtQuery`,
`SliverTrace`, the table-order congruence, the liveness fix),
`crates/ordeal/src/query.rs` (`SliverBlock`, `QueryTerm::flatten_sliver`,
`SliverCertificate`, `SliverSatCertificate`, `SliverCheckResult`),
`crates/ordeal/src/solver.rs` (`Solver::from_sliver` keeps the extended
query; the gates run the check first; `check_sliver_with_term`),
`crates/ordeal/src/cert_bundle.rs` (`ordeal-cert/v4`),
`crates/ordeal/examples/sliver_scan.rs` and `sliver_size.rs` (the
evidence harnesses). The verification record is VE-062.

**Measured** (release, Apple M4; `examples/sliver_size.rs`, the loom
`all-unsat` shape with `4n` byte stores over a symbolic base and `4n`
reads of one array):

| pairs | reads | core roots | ext nodes | v3 bundle | v4 bundle | `ext` block | check | solve |
|---|---|---|---|---|---|---|---|---|
| 1 | 4 | 7 | 40 | 224 876 B | 228 952 B | 1 287 B | 0.002 ms | 1 ms |
| 2 | 8 | 29 | 112 | 891 276 B | 901 563 B | 3 074 B | 0.004 ms | 5 ms |
| 4 | 16 | 121 | 352 | 3 546 265 B | 3 577 292 B | 9 014 B | 0.013 ms | 39 ms |
| 6 | 24 | 277 | 720 | 8 040 314 B | 8 102 972 B | 17 909 B | 0.026 ms | 116 ms |

The `ext` block is 0.2–0.6 % of the bundle (the rest is the CNF and the
proof, there since v1), and the check is three orders of magnitude below
the solve — as the design's performance section predicted. The
old-vs-new verdict scan (`examples/sliver_scan.rs`, v0.32.0 against this
tree, `check_with_deadline(10 s)` per query, verdicts streamed line by
line): 1 050 queries — the three seeded corpora (`0x5111_5EED…`/300,
the lifted `0x5111_0231…`/300, `0x5111_0DFF…`/250), the loom-shaped
chains for 1–6 store/load pairs (every byte read back, against a fresh
variable, the whole `Or` and `And`, an aliasing pair), the #231
trap-guard shapes, the bounded-entry queries — verdict-identical on all
1 050 (928 sat, 122 unsat, 0 Unknown on either side), 4 778 ms in total
against 4 897 ms on v0.32.0. The first scan, before the liveness fix,
degraded 126 engine-SAT queries to `Unknown` (`DeadEntry`): that is the
completeness risk the design named, and it was caught by the scan, not
by a proof — the kind of finding the scan exists for.
