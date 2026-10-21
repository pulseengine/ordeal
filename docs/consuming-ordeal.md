# Consuming ordeal (loom / synth trial guide)

ordeal is a certificate-checked QF_BV SMT decision procedure. This is the
guide for trying it as a dependency and reporting back.

## Depend on it

```toml
[dependencies]
ordeal = "0.23"
```

`ordeal-lrat` (the trusted checker) is pulled transitively. The default
build has **zero external dependencies** and builds on `wasm32-wasip2`.
Requires a Rust toolchain with **edition 2024** support (rustc ≥ 1.85).

## The API

```rust
use ordeal::{Solver, BoolTerm, BvTerm, Sort, CheckResult};

let mut s = Solver::new();
s.assert(/* a BoolTerm: the negation of your equivalence */);
match s.check() {
    CheckResult::Unsat(cert) => { /* equivalence holds; cert is a portable
                                     proof — cert.recheck() re-validates it */ }
    CheckResult::Sat(model)  => { /* counterexample in model.assignments */ }
    CheckResult::Unknown     => { /* DO NOT optimize — see contract below */ }
}
```

Array/UF (linear memory + `pure_call`) queries use the sliver entry:

```rust
use ordeal::sliver::{ArrayTerm, ExtBvTerm, ExtBoolTerm};
let verdict = Solver::check_sliver(&[/* ExtBoolTerm assertions */]);
```

`check_sliver` is unbounded and maps an out-of-sliver query to `Unknown`.
For a whole-function obligation, bound it and keep the refusal visible
(#236):

```rust
// Bounded one-shots, the sliver twins of check_with_deadline / check_with_limit.
// The deadline clock starts before the sliver is lowered.
let v = Solver::check_sliver_with_deadline(&query, 2_000);
let v = Solver::check_sliver_with_limit(&query, 100_000);

// Or lower first: a refusal is an Err (SliverError), never confused with an
// undecided Unknown, and every core entry point applies to the result.
match Solver::from_sliver(&query) {
    Ok(solver) => { let v = solver.check_with_deadline(2_000); }
    Err(refusal) => { /* out of the sliver: defer to another engine */ }
}
```

**Build the solver with `Solver::from_sliver`, not by calling
`ordeal::sliver::lower` and asserting the core yourself.** Since TR-072
a solver built from the extended query runs the trusted
`check_sliver_lowering` — that the lowered core IS the elimination of
your `select`/`store`/`pure_call` query — before the term and query
checks, on every entry point; a solver you fill with the lowered core is
a core solver, and its verdict is about the core only. The extended
certificate is `solver.check_sliver_with_term()` (the `ordeal-cert/v4`
section below).

The fragment is the closed loom #246 op set (bit-widths 1 to 128) plus the sliver
(`Array(BV32→BV8)` select/store over concrete **and symbolic** BV32 indices
— symbolic decided since v0.11.0 — plus uninterpreted `pure_call`).
Quantifiers, floating-point, optimization, and incremental push/pop are out
of scope by design.

### Layout / data-type equivalence (spar #38)

For "does layout A encode the same bits as layout B?" — e.g. spar checking a
generated WIT record faithfully encodes an AADL `data implementation` — use the
one-call `Solver::prove_equiv` helper. It's the standard equivalence-as-UNSAT
encoding (asserts the terms differ, decides), so `Unsat` = **equivalent**.

```rust
use ordeal::{Solver, BvTerm, Sort, CheckResult};

// A packed record's low field must survive pack+extract: the low 8 bits of
// concat(hi: u32, flags: u8) recover `flags`. Build the term graph directly —
// no SMT-LIB2 text round-trip on machine-generated queries.
let flags = BvTerm::Var { name: "flags".into(), sort: Sort::new(8) };
let hi    = BvTerm::Var { name: "hi".into(),    sort: Sort::new(32) };
let packed = BvTerm::Concat(Box::new(hi), Box::new(flags.clone())); // 40 bits
let low8   = BvTerm::Extract { hi: 7, lo: 0, arg: Box::new(packed) };

match Solver::prove_equiv(low8, flags) {
    CheckResult::Unsat(cert) => { /* layouts are equivalent; cert is checked */ }
    CheckResult::Sat(model)  => { /* NOT equivalent — inputs that differ */ }
    CheckResult::Unknown     => { /* no claim; a width mismatch lands here too */ }
}
```

Model field packing with `Concat` / `Extract{hi,lo}` / `ZeroExt` (offsets and
widths fall out directly); overflow/range checks are `bvult` / `bvule`
assertions; a conditional field selector (`cond ? A : B`) is `BvTerm::Ite`.
`prove_equiv` is decision-only — it does **not** grow an optimization/LP arm
(that problem class stays on HiGHS/good_lp).

### Translation validation (synth): a certificate you can re-check

A WASM→ARM translation validator proves each codegen rule equivalent: assert
the two results *differ*, and `Unsat` means "equal for every input". A bare
`z3.check() == Unsat` verdict is **unchecked** — if the solver has a soundness
bug, an *incorrect* lowering is silently accepted as proven. ordeal returns the
same `Unsat`, but as a **portable proof object**: the certificate carries both
the refuted CNF (`cert.cnf`) and the LRAT proof (`cert.lrat`), so the caller
re-establishes the result with zero trust in the solver.

```rust
use ordeal::{Solver, BvTerm, Sort, CheckResult};

// i32.mul(x, 2)  ⇒  LSL x, #1   (a strength-reduction the backend emits)
let x = || BvTerm::Var { name: "x".into(), sort: Sort::new(32) };
match Solver::prove_equiv(
    BvTerm::Mul(Box::new(x()), Box::new(BvTerm::Const { value: 2, sort: Sort::new(32) })),
    BvTerm::Shl(Box::new(x()), Box::new(BvTerm::Const { value: 1, sort: Sort::new(32) })),
) {
    CheckResult::Unsat(cert) => {
        // Re-run the trusted checker yourself. Ok(()) ⟺ the proof refutes the
        // CNF, so "equivalent" is evidence you reproduced — not solver faith.
        cert.recheck().expect("independent re-check confirms equivalence");
    }
    CheckResult::Sat(model) => { /* NOT equivalent: model is a counterexample */ }
    CheckResult::Unknown    => { /* undecided — do NOT accept the lowering */ }
}
```

`cert.recheck()` runs the formally-verified `ordeal-lrat` checker over
`(cert.cnf, cert.lrat)` — the same validation ordeal did internally, now
reproducible on your side or in a separate audit step. See the runnable
[`translation_validation` example](../crates/ordeal/examples/translation_validation.rs)
(`cargo run -p ordeal --example translation_validation`) for correct rules being
proven and a buggy `i32.mul(x,3) ⇒ LSL x,#1` being caught with a counterexample.

## Parallelize across queries, not inside them

Real workloads are many *independent* queries — synth validates many VCs,
loom checks many rewrite rules, a BMC gate asks one query per unrolling
depth and per property. That independence is where your speedup lives:

- `Solver` is one-shot and self-contained, and every API type (`Solver`,
  `BvTerm`, `BoolTerm`, `CheckResult`, `Certificate`, `Model`) is
  `Send + Sync` — guaranteed by a compile-time assertion in ordeal's test
  suite, so it cannot silently regress. Build one solver per query and fan
  the queries out over your thread pool (e.g. `rayon`'s `par_iter`); there
  is no shared state and no ordering requirement between checks.
- For BMC-style use: race all depths `k = 1..N` and all properties
  concurrently. Any SAT is your counterexample; all-UNSAT clears the depth.
  A single-query envelope measured once to plan around (macOS arm64,
  certified end-to-end incl. the checker; TR-031 / VER-028, not re-measured
  by CI, which only builds the benches): a queue-overflow-shaped unrolling
  crossed 1 s around k ≈ 90 and sat at ~2.5 s at k = 128; deadlock-shaped
  instances stayed under ~275 ms through k = 96 (`benches/bmc.rs`). Treat
  these as a dated measurement, not a guarantee.
- Blast/Tseitin are microseconds; the SAT search is the whole cost on hard
  queries. Parallelizing *inside* one solve is therefore deliberately not
  offered today: a seed portfolio would make certificates run-to-run
  nondeterministic (different proof bytes → different bundle hashes), and
  proof-carrying parallel CDCL is a research problem. If you hit a
  single-query latency wall that the `cadical` accelerator does not clear,
  report it — that measurement is what activates the parked portfolio work.

## The soundness contract (read this)

- **`Unknown` is conservative.** It means "not proven" — the solver could
  not decide, would not stand behind an answer, or the query used a
  construct outside the enabled fragment (e.g. a bitvector width outside
  1 to 128).
  You MUST NOT apply an optimization / accept a transformation on `Unknown`.
  Keep the original.
- **`Unsat` is the only verdict that authorizes a transformation.** It
  carries a self-contained proof — the refuted CNF (`cert.cnf`) and the LRAT
  refutation (`cert.lrat`) — that the formally-verified `ordeal-lrat`
  checker already validated. Since v0.32.0 (TR-070) it validated more than
  the proof: before `check` returned, the trusted crate related your
  assertions (flattened as asked) to the DAG the solver lowered them to
  (`check_term_dag`), re-encoded that DAG with the proven lowering and
  checked the LRAT proof against the CNF *it* produced (`check_query`) —
  so the certificate is about the term you asked, not a CNF you take on
  faith (`docs/formal-verification.md`, "the default path"). Call
  `cert.recheck()` (or `ordeal_lrat::check(&cert.cnf,
  cert.lrat_text().unwrap())`) to re-validate the proof independently, or
  `check_with_term()` to receive the term and the DAG the gate checked,
  re-checkable with `TermCertificate::recheck()`: your trust rests on the
  proof, not on the solver.
- **`Sat` carries a counterexample** re-evaluated against your assertions
  by the evaluator and, since v0.32.0, accepted by the trusted crate as a
  model of the term (`check_query_model` and the proven binding of every
  value through the term's variable map) before it was returned.
- **Anything the trusted crate rejects is `Unknown`**, on every entry
  point — the solver, the search, the proof and the model are all
  untrusted, and a rejection never becomes a verdict.

## Reporting trials back

Please file issues on `pulseengine/ordeal` with these labels so they triage
straight into the delivery loop:

- `field-report` — general "we tried it" feedback.
- `missing-capability` — a query shape/op you emit that comes back
  `Unknown` and needs deciding (tell us the exact term).
- `soundness` — any verdict you believe is wrong (attach the query; this is
  top priority).
- `perf` — a latency cliff on your real query mix (attach a measurement).

For `missing-capability` and `soundness`, a minimal reproducing `BoolTerm`
(or SMT-LIB) makes the turnaround fast.

## SAT verdicts as evidence: the re-checkable witness

Since TR-038, `Solver::check_with_witness()` (no feature gate since #162)
returns `Sat` as a `SatCertificate`: the model **plus** the full CNF
assignment and per-variable bit map. `cert.recheck()` re-establishes the
verdict through the same trusted `ordeal-lrat` crate that validates UNSAT
proofs — every clause checked satisfied, every advertised model binding
checked consistent — so **both** verdict directions are now evidence you
reproduce rather than solver output you trust. `to_cert_v1()` /
`SatCertificate::from_cert_v1()` round-trip it as an `ordeal-cert/v1`
bundle with an optional `witness` block (hash-verified before parsing
returns). A `Sat` whose witness the trusted crate rejects is never
returned — it degrades to `Unknown`, symmetric with the UNSAT gate.

The SAT direction of the trusted crate is machine-checked too (v0.21.0,
TR-044 / VER-039, `lean/SatWitness.lean`, `sorry`-free and CI-gated like
the UNSAT proof): `kernel.spec.check_sat_sound` — an accepted witness
satisfies the *actual* carried CNF; `check_sat_satisfiable` — hence that
CNF is not unsatisfiable; `check_binding_sound` — bit `k` of an advertised
model value *is* the truth value of the CNF literal it is bound to; and
`verdicts_exclusive` — no CNF has both an accepted LRAT refutation and an
accepted witness. All four depend only on Lean's three standard axioms,
pinned in CI; `docs/formal-verification.md` states the trust boundary
exactly.

### At the command line

Since #162 (TR-045) the released binary carries the same witness:
`ordeal check foo.smt2 --format json` on `sat` prints `certificate.clauses`
and a `witness` block — `encoding` (`bitstring-lsb-var1`), the full
`assignment`, the per-variable `bit_map` (`name`, `width`, LSB-first signed
CNF literals) and `assignment_sha256` / `bit_map_sha256` — byte-identical
to the `ordeal-cert/v1` witness the API emits, so rivet's field mapping
(`witness-sha256`, `bit-map-sha256`) applies to CLI output too. From rivet
0.39.0 an `ordeal-certificate` with `verdict: sat` that carries
`witness-sha256` and a recorded `verification-result: pass` counts as
evidence without the "SAT is self-checked" warning;
`examples/rivet_witness_ingestion.rs` produces such a fixture from a live
solve (and the no-witness control that still warns). Re-check
it exactly as the API's: `ordeal_lrat::check_sat(clauses, assignment)`
and `ordeal_lrat::check_binding(assignment, bits, value)` per model
variable. The hashes are computed in-tree (`ordeal::sha256`, FIPS-tested
and cross-checked against `sha2` in CI) so the default binary stays
dependency-free; they are integrity only — the verdict rests on the
recheck, never on the hash. A `sat` is only printed after the trusted
recheck passed; text mode notes the witness size on stderr.

## UNSAT verdicts as evidence about the query: `ordeal-cert/v2`

A v1 certificate (`cert.cnf`, `cert.lrat`) proves the **CNF**
unsatisfiable; that the CNF is the one your assertions lower to was the
solver's word (its lowering is proven since v0.26.0, but no re-check ran
it). Since v0.27.0 (#192 phase 4) the trusted `ordeal-lrat` crate holds
that proven lowering itself and exposes `ordeal_lrat::check_query`: given
the lowered term DAG, it re-encodes the DAG inside the trusted crate and
checks the LRAT proof against the CNF *it* produced. An accepted re-check
therefore proves the **query** unsatisfiable (`kernel.spec.check_query_sound`,
`lean/QueryCheck.lean`, axiom-clean; `docs/formal-verification.md` states
exactly what "query" means there). Opt in:

```rust
use ordeal::{Solver, QueryCheckResult};

match solver.check_with_query() {
    QueryCheckResult::Unsat(cert) => {
        // cert.certificate: the v1 pair (cnf + lrat), still recheck()-able.
        // cert.query:       the lowered DAG (nodes, constant bits, roots, hints).
        cert.recheck().expect("the trusted crate re-encodes the query and accepts the proof");
        #[cfg(feature = "cert-bundle")]
        let json = cert.to_cert_v2(&attests);          // "format": "ordeal-cert/v2"
    }
    QueryCheckResult::Sat(cert) => {
        // cert.witness: the v1 witness (model, cnf, assignment, bit_map), still recheck()-able.
        // cert.query:   the lowered DAG;  cert.inputs: its input bits + the (name, width, node) map.
        cert.recheck().expect("the trusted crate evaluates the query to true under the inputs");
        #[cfg(feature = "cert-bundle")]
        let json = cert.to_cert_v2(&attests);          // "format": "ordeal-cert/v2", "verdict": "sat"
    }
    QueryCheckResult::Unknown => { /* no claim */ }
}
```

`check_with_query` runs the trusted re-check *before* returning `Unsat`
(a certificate it would reject degrades to `Unknown`, like the witness
gate), at the cost of one extra lowering; `check` and
`check_with_witness` are untouched. To verify a received bundle:
`QueryCertificate::from_cert_v2(json)` (every content hash — problem,
proof, query — verified before it returns) then `bundle.recheck()`. Or,
without the feature, decode the `query` block yourself
(`ordeal::query::node_from_op`, `bits_from_string`) and call
`ordeal_lrat::check_query(nodes, bits, roots, hints, lrat_text)` — it
returns the re-encoded CNF, which should equal `problem.clauses`.

The v2 bundle is the v1 envelope with one more block after `proof`:

```json
"query": {
  "encoding": "ordeal-dag/v1",
  "num_nodes": 7,
  "nodes": [["const",0,8],["var",8],["add",0,1],["const",8,8],["eq",2,3],["const",16,8],["ne",1,5]],
  "bits": "101000001100000001111111",
  "roots": [4, 6],
  "hints": [0, 1, 2, "…"],
  "sha256": "…"
}
```

(`nodes` are `[op, args…]` in constructor order; `bits` is the constant
table; `hints` are the solver's compaction hints — untrusted advice the
re-check verifies.) Nothing about v1 changed: `to_cert_v1` /
`from_cert_v1` emit and read what they did, rivet's v1 ingestion keeps
working, and a v1 reader refuses a v2 bundle by its `format` string
rather than silently ignoring the query (a rivet issue for v2 ingestion
follows). At the command line, `ordeal check foo.smt2 --format json
--with-query` prints the same `query` block inside `certificate` on
`unsat` (JSON only); without the flag the output is byte-identical to
v0.26.0.

Since v0.28.0 (#192 phase 5) the five formerly derived ops — `bvnot`,
`bvneg`, `bvrotl`, `bvsdiv`, `bvsrem` — are nodes of their own in the
query block (`"bvnot"`, `"neg"`, `"rotl"`, `"sdiv"`, `"srem"`), each with a
proven rule the trusted crate runs, so the block carries the operation you
asked about rather than its rewrite. A block that uses one of them is
tagged `"encoding": "ordeal-dag/v2"` with `recheck.min_version` `0.28.0`
(a v0.27.0 reader refuses it as unsupported rather than misreading it); a
block without them stays `ordeal-dag/v1`, and readers from v0.28.0 accept
both. Only `check_with_query` / `--with-query` lower them as nodes: the
default `check` still rewrites them first, so its certificates are
byte-identical to v0.27.0's (for a few queries the two paths' CNFs differ
in variable numbering — both certified; `docs/design/query-cnf-gap.md`,
phase 5).

Since v0.29.0 (#192 phase 6, TR-065) the `sat` direction is symmetric on
this path. `QueryCheckResult::Sat` carries a `QuerySatCertificate`: the
v1 witness (`.witness`, exactly what the variant used to carry), the same
`query` block, and an `inputs` block — the DAG's primary-input assignment
(`"bits"`: a `0`/`1` string, input 0 first; the `Var` nodes' bits in node
order, LSB first within a variable) plus the `(name, width, node)` map
from each model variable to its `Var` node, with its own `sha256` over a
canonical text tagged `ordeal-inputs/v1`. `check_with_query` returns
`Sat` only after the trusted `ordeal_lrat::check_query_model(nodes, bits,
roots, inputs.bits)` evaluated EVERY root of the DAG to true under those
bits (`kernel.spec.check_query_model_sound`, the same `dagBool` semantics
`check_query_sound` negates; `query_verdicts_exclusive` says no query has
both an accepted refutation and an accepted model). A model it rejects
degrades to `Unknown`. `QuerySatCertificate::to_cert_v2` /
`from_cert_v2` emit and read the SAT bundle (`"verdict": "sat"`, the v1
witness envelope plus `query` and `inputs`, `recheck.min_version`
`0.29.0`; five hashes verified before `QuerySatBundle::recheck`), and
`ordeal check --format json --with-query` prints the two blocks inside
`certificate` on `sat` — without the flag, and for every v1 bundle and
reader, nothing changed. Re-check a received SAT bundle without the
feature by decoding `query` and `inputs.bits` and calling
`ordeal_lrat::check_query_model`; the CNF-level `check_sat` /
`check_binding` re-check still applies to the `witness` block and is run
first by `recheck()` as defence in depth. What the trusted step does not
establish: that the DAG is your question, and that the `Var` node a
model value is written into is the one made for that name — the builder's
`(name, width, node)` map; `QueryInputs::check_consistent` (untrusted)
confirms the printed model agrees with the carried inputs.

What a v2 recheck does *not* cover (still the solver's word): the
untrusted DAG builder's choice of DAG for your assertions (now visible in
the bundle), canonicalization, the sliver and the SMT-LIB front end —
`docs/formal-verification.md` has the list. The first two are what
`ordeal-cert/v3` closes.

## Verdicts as evidence about the TERM: `ordeal-cert/v3`

Since v0.31.0 (#192 phase 7, TR-069) a certificate can carry the **term
you asked** next to the DAG the solver built from it, and the trusted
crate verifies — before a verdict is returned — that the DAG is a
semantics-preserving rewrite of the term (`ordeal_lrat::check_term_dag`,
`kernel.spec.check_term_unsat_sound` / `check_term_model_sound`). The
term block (`ordeal-term/v1`) is your assertions flattened with no
canonicalization and no hash-consing — variables shared by name,
constants interned, every other subterm its own node, in the `query`
block's node spelling — plus the variable names and an index map
`term node → query node` (`18446744073709551615` = no image: the inside
of a folded constant). In v0.31.0 this was opt-in; **since v0.32.0
(TR-070) it is what every entry point does** — `check`,
`check_with_limit`, `check_with_deadline`, `check_with_witness`,
`check_with_query`, the sliver one-shots and the CLI all run the same
pipeline and return a projection of the same gated result, so
`check_with_term` costs nothing beyond `check` and only keeps more:

```rust
use ordeal::{Solver, TermCheckResult};

match solver.check_with_term() {
    TermCheckResult::Unsat(cert) => {
        // cert.query: the v2 certificate (cnf + lrat + the lowered DAG), still recheck()-able.
        // cert.term:  the term as asked (nodes, bits, roots, vars) and the map onto the DAG.
        cert.recheck().expect("the trusted crate relates the term to the DAG and refutes the DAG");
        #[cfg(feature = "cert-bundle")]
        let json = cert.to_cert_v3(&attests);          // "format": "ordeal-cert/v3"
    }
    TermCheckResult::Sat(cert) => {
        // cert.query: the v2 SAT certificate (witness, DAG, inputs);  cert.term: as above.
        cert.recheck().expect("term-to-DAG, the model, and every binding through the term's variables");
        #[cfg(feature = "cert-bundle")]
        let json = cert.to_cert_v3(&attests);          // "format": "ordeal-cert/v3", "verdict": "sat"
    }
    TermCheckResult::Unknown => { /* no claim */ }
}
```

To verify a received v3 bundle: `TermCertificate::from_cert_v3(json)` /
`TermSatCertificate::from_cert_v3(json)` (every content hash verified
before it returns — four on `unsat`, six on `sat`) then
`bundle.recheck()`. Without the feature, decode `term` and `query` and
call `ordeal_lrat::check_term_dag(term.nodes, term.bits, term.roots,
term.map, query.nodes, query.bits, query.roots)` before the v2 calls;
on `sat`, bind each printed model value with
`ordeal_lrat::check_input_value(inputs.bits, ordeal_lrat::var_offset(query.nodes,
term.map[term.vars[name].node]), width, value)` (both proven, 7d). At
the command line, `ordeal check foo.smt2 --format json --with-term`
prints the `--with-query` output plus the `term` block inside
`certificate` (JSON only); `--with-query` and the default output are
byte-identical to v0.30.0 — and to v0.31.0 after the default path
switched to the term check: the verdict, the certificate bytes and the
model are unchanged, only what they rest on is.

**What to compare it against.** Since v0.34.0 (TR-073) the term block
is produced by the trusted crate itself: re-run
`ordeal_lrat::flatten_tree(&ordeal::mirror::of_bools(&assertions))`,
`ordeal_lrat::project_core` on its `nodes`, and compare `term.sha256`
with `QueryTerm::canonical_text` of the result, or compare the `nodes`
/ `vars` / `roots` lists (`ordeal::dag::flatten` is the same walk and
remains as the differential twin; by hand: post-order, left-to-right,
variables shared by name, a name at two widths refused); the `map` is
the solver's and does not need to be reproduced. What a v3 recheck does
*not* cover: the copy of your `BoolTerm`s into the kernel's tree
(`ordeal::mirror`, one `match` arm per constructor, a tested
bijection), the sliver (a v4 bundle covers it) and the front ends — the
flattening and the names it does cover (`tree_unsat_sound`,
`tree_model_sound`: the model's values are bound BY NAME through the
kernel's own variable table). A v1 or v2 reader refuses a v3 bundle by
its `format`, and the v3 readers refuse v1 and v2, so nobody silently
downgrades.

## Verdicts as evidence about the EXTENDED query: `ordeal-cert/v4`

Since v0.33.0 (TR-072) a certificate about an array/UF query — loom's
memory and `pure_call` obligations — carries the **extended query as
asked** next to the lowered core, and the trusted crate verifies, before
a verdict is returned, that the core is the read-over-write + Ackermann +
congruence elimination of it (`ordeal_lrat::check_sliver_lowering`,
`kernel.spec.check_sliver_unsat_sound` / `check_sliver_model_sound`). So
an `Unsat` means: unsatisfiable under **every** array and UF
interpretation; a `Sat` comes with the interpretation built from the
model. The `ext` block (`ordeal-ext/v1`) is your `ExtBoolTerm`s
flattened 1:1 — the `term` block's node spelling plus `["select", aid,
idx, s, n]` (the store chain in `side`, outermost store first, index
then value per level) and `["call", fid, w, s, n]` (arguments in `side`),
variables shared by name, constants interned, arrays and functions
numbered by first appearance with their names in `arrays` / `funcs` —
plus the untrusted `map` (extended node → `term` node), `reads` (3 per
entry: read variable node, array id, index node) and `calls` (4 per
entry: result variable node, function id, first argument in `cargs`,
arity). The `term` block of a v4 bundle is `ordeal-term/v2`: the lowered
core hash-consed, with the reads' indices and the calls' arguments
appended as non-root nodes, so the tables can always point at them.

```rust
use ordeal::{Solver, SliverCheckResult};

let solver = Solver::from_sliver(&query)?;          // Err: out of the sliver
match solver.check_sliver_with_term() {
    SliverCheckResult::Unsat(cert) => {
        // cert.term:   the v3 term certificate about the lowered core (still recheck()-able);
        // cert.sliver: the ext block — your query as asked, the map and the tables.
        cert.recheck().expect("check_sliver_lowering + check_term_dag + check_query");
        #[cfg(feature = "cert-bundle")]
        let json = cert.to_cert_v4(&attests);          // "format": "ordeal-cert/v4"
    }
    SliverCheckResult::Sat(cert) => {
        // cert.model: the extended model — arrays at every read's index value,
        // functions at every call's argument values, the query variables' bindings.
        cert.recheck().expect("the model is the pullback the SAT capstone builds");
        #[cfg(feature = "cert-bundle")]
        let json = cert.to_cert_v4(&attests);          // "verdict": "sat", with ext_model
    }
    SliverCheckResult::Unknown => { /* no claim; also what a core solver returns here */ }
}
```

To verify a received v4 bundle: `SliverCertificate::from_cert_v4(json)` /
`SliverSatCertificate::from_cert_v4(json)` (every content hash verified
before it returns — five on `unsat`, seven on `sat`) then
`bundle.recheck()`. Without the feature, decode `ext`, `term` and
`query` and call `ordeal_lrat::check_sliver_lowering(ext.nodes, ext.bits,
ext.side, ext.roots, ext.map, ext.reads, ext.calls, ext.cargs, term.nodes,
term.bits, term.roots)` before the v3 calls. `recheck.min_version` is
`0.33.0`; a v1, v2 or v3 reader refuses a v4 bundle by its `format`, and
the v4 readers refuse them.

**What to compare it against.** Since v0.34.0 (TR-073) the `ext` block
is produced by the trusted crate itself: re-run
`ordeal_lrat::flatten_tree(&ordeal::mirror::of_ext_bools(&assertions))`
and compare it with `ext` (`nodes`, `bits`, `side`, `roots`, and the
tables `vars`, `arrays`, `funcs` read back with `ordeal::mirror::ext_query`
— or the hash after putting your flattening into the block's
`canonical_text`; `ordeal::sliver::flatten_ext` is the same walk and
remains as the differential twin); the `map` and the tables are the
solver's and do not need to be reproduced. What a v4 recheck does *not*
cover: the copy of your `ExtBoolTerm`s into the kernel's tree
(`ordeal::mirror`, a tested bijection) and the front ends — the
flattening and the variable, array and function names it does cover
(`ext_tree_unsat_sound`, `ext_tree_model_sound`: the extended model's
variables are bound BY NAME through the kernel's table and the two
maps). Core queries are untouched: they keep producing v3 bundles, byte
for byte.

## Supply chain: SBOM and VEX

From v0.20.0 each GitHub Release carries a CycloneDX SBOM
(`ordeal-<ver>.cdx.json`) and a CycloneDX VEX (`ordeal-<ver>.vex.json`),
both listed in the cosign-signed `SHA256SUMS.txt`. The VEX answers "does
advisory X affect the ordeal I'm running?" for the **shipped closure** —
the crates a release binary is built from. Because ordeal's default build
has no third-party dependencies (CI-asserted), that closure is `ordeal` +
`ordeal-lrat`, and the VEX normally carries no statements at all; it
records the RustSec advisory-db commit and the time it was asserted, so a
reader can tell how fresh the answer is.

A weekly job re-audits the latest release. If the answer changes, a person
classifies the new advisory and a re-issue is published as
`ordeal-<ver>.vex.r<N>.json` with its own cosign bundle (signing identity:
the `vex-reissue.yml` workflow). Take the highest revision present; the
release-time VEX is never overwritten, so the signed sums stay valid.

## Building the trusted checker yourself (overflow checks)

The `ordeal-lrat` soundness proofs are about a model in which every
arithmetic operation fails on overflow. ordeal's own release builds (the CLI,
the wasm component) enable `overflow-checks` for `ordeal-lrat`, so an
overflow panics instead of wrapping (#225). Cargo applies profile settings
only from the **root** workspace, so if you build `ordeal-lrat` (directly or
through `ordeal`) in your own release profile, add the same override:

```toml
[profile.release.package.ordeal-lrat]
overflow-checks = true
```

The measured cost is under 1% on a checker-heavy query (30 MB LRAT proof).
