# Design: close the query→CNF gap — a proven re-encoder beside the checker

**Issue:** #192 · **Milestones:** v0.25.0 (phases 1 and 2), v0.26.0
(phase 3), v0.27.0 (phase 4), v0.28.0 (phase 5) · **Decision:** option
(b), maintainer, 2026-10-01; phase 4 ships `ordeal-cert/v2` *alongside* v1
(maintainer, 2026-10-01) · **Status:** phases 1–5 delivered (this
document records all five); the default path's switch to the phase-5
nodes is an open maintainer decision (see phase 5, "byte identity");
phase 6 (v0.29.0) delivered; **phase 7 delivered** (the design, option
(C) approved by the maintainer 2026-10-15, and what shipped —
`check_term_dag`, `lean/TermCheck.lean`, `ordeal-cert/v3`,
`--with-term`, the proven model binding); **the default path switched
to the term check** (v0.32.0, TR-070, maintainer decision 2026-10-15;
the last section).

## The claim being protected

ordeal's certificate proves that the *CNF* is unsatisfiable, not that the
*query* is. The query→CNF path is not covered by any proof, which makes it
effectively trusted. #182 showed the consequence: a wrong encoding, and a
certified wrong answer.

**Decision (b):** the certificate will carry the query as a term DAG. The
trusted `ordeal-lrat` re-encodes it with a *proven* encoder and checks the
LRAT proof against its own CNF. A third party re-checking a bundle then
certifies the query, not only a CNF. This is how Lean's `bv_decide` works.
The trusted base grows, but only by proven code.

## Pipeline map (claims checked against the code)

| Stage | Assurance before #192 | After phase 1 | After phase 2 | After phase 3 | After phase 4 |
|---|---|---|---|---|---|
| SMT-LIB / Verus front ends | tests and the Z3 differential | unchanged | unchanged | unchanged | unchanged |
| lowering of derived ops | tests (exhaustive at width 8) and Z3 | unchanged | unchanged | unchanged | unchanged (still lowered to the closed core *before* the DAG; the v2 bundle carries the lowered DAG) — **phase 5 (v0.28.0):** `bvnot`, `bvneg`, `bvrotl`, `bvsdiv`, `bvsrem` are `DagNode`s with **proven** composite rules (`lean/BlasterDerived.lean`); the v2 bundle carries the operation; the default `check` path keeps the rewrite so its bytes are unchanged (the rewrite stays untrusted there) |
| sliver (array/UF) | tests only | unchanged | unchanged | unchanged | unchanged |
| canon (including constant folding via `eval.rs`) | tests only | unchanged | unchanged | unchanged | unchanged |
| term walk | tests only | unchanged | unchanged (it now *calls* the proven rules, but is itself unproven) | split in two: the **DAG builder** (`dag.rs`, term → `DagNode` list; untrusted glue, tests only) and the **encoder** (`blast_kernel::encode`, **proven**: `encode_sound`) | the DAG builder stays untrusted, but its output is now **in the certificate** (`ordeal-cert/v2` `query`), so a consumer sees the question that was lowered; the encoder runs **inside the trusted crate** |
| blast rules | proven in Lean via the `blast_kernel.rs` mirror, plus a mirror/real differential (#202, #210) | mirror is now **gate-identical** to the shipped rules (XOR shape fixed; replay test, every op, widths 1..=16) | **the solver runs the proven rules** — `blast_kernel.rs` is the only implementation; the hand-written copies are deleted | unchanged (called by the proven encoder) | moved into `ordeal-lrat` (`kernel::blast_kernel`); the solver re-exports them — one source |
| bridge (reference arena → shipped arena replay) | — | — | new, unproven: ~100 lines in `blast/mod.rs`; pinned by the gate-identity tests and the byte-identity digests | **out of the production path** (test harness for the per-family differentials) | unchanged |
| AIG folding and hashing | tests only | tests only (benchmarked below) | tests only (now applied at replay time; same gates, same CNF) | **proven** as a separate pass (`blast_kernel::compact`, `compact_sound`); the strash decisions come from untrusted hints the pass checks | the hints travel in the certificate; the trusted re-check compacts with them (and checks them) |
| Tseitin | randomised brute-force test | **proven** on the mirror (`tseitin_sat_preserving`), mirror pinned to `cnf.rs` clause for clause | unchanged | **the solver runs the proven encoder** (`blast_kernel::tseitin`); `cnf.rs` is out of the production path | unchanged, in the trusted crate |
| `DagWF` side condition | — | — | — | assumed by `encode_sound` / `dag_refuted` (the builder meets it by construction; no proven code checks it) | **checked by proven code**: `kernel::dag_wf`, `dag_wf_spec` (Ok iff `DagWF`) |
| LRAT / SAT-witness check | proven, axiom-clean | unchanged; now composed with the encoder proof (`tseitin_refutes_outputs`) | unchanged | composed all the way to the DAG: `dag_refuted` | **one trusted entry point for the query**: `kernel::check_query`, `check_query_sound` (no side conditions left: well-formedness and every capacity bound are checked at run time) |

The SAT path already re-checks the model against the query, via `eval.rs`.
The UNSAT path has no such check, and that is the gap.

## Phases (each shippable)

- **v0.25.0 — phase 1 (this document).** Make the model's XOR gate-identical
  to `aig::xor`. Prove Tseitin satisfiability preservation in Lean. Fix the
  stale `rotate_left` doc in `smtlib.rs`. Benchmark CNF size and time with
  no folding, folding only, and folding plus hashing.
- **v0.25.0 — phase 2 (delivered, below; shipped with phase 1).** The
  shipped walk calls the proven rules directly, and the duplicate rule
  bodies are deleted. Acceptance: `cli_baseline` CNF and certificate bytes
  are unchanged.
- **v0.26.0 — phase 3 (delivered, below).** A proven DAG walk, plus a
  proven folding/hashing pass after encoding. The proofs count nodes
  exactly, so folding can't go inside `push_and`. `encode_sound` is
  composed with `lrat_check_sound` (`dag_refuted`). Acceptance: shipped
  bytes unchanged.
- **v0.27.0 — phase 4 (delivered, below).** Move the encoder into
  `ordeal-lrat` as `check_query`, with an `ordeal-cert/v2` `query` block
  *alongside* v1 (no breaking change; consumers opt in). Acceptance:
  flipping one constant bit in `query` fails the recheck even though the
  CNF and proof are untouched; default output byte-identical. Derived ops
  are **not** DAG constructs yet (see "what phase 4 does not claim").
- **v0.28.0 — phase 5 (delivered, below).** The derived ops stop being
  trusted rewrites: `bvnot`, `bvneg`, `bvrotl`, `bvsdiv`, `bvsrem` become
  `DagNode` constructors whose `encode_node` arms are compositions of the
  already-proven rules, each with a `_bitvec` theorem against the matching
  Lean `BitVec` operation; `check_with_query` lowers them as nodes and the
  v2 query block carries the operation. Acceptance: default output
  byte-identical to v0.27.0 (the default path keeps the rewrite); a v2
  bundle whose `sdiv` node is changed to `udiv` fails the recheck.
- **v0.29.0+.** A query-level SAT check, so `eval.rs` leaves the trust
  path; the sliver; the SMT-LIB parser stays trusted, mitigated by a round
  trip and Z3; switching the default path to the phase-5 nodes (changes
  emitted certificates for some `bvsdiv`/`bvsrem`/`bvnot` queries —
  maintainer's call, measured below).

(The milestones moved up by one against the first plan: phases 1 and 2
both shipped in v0.25.0.)

## Phase 1: what was delivered

### F1 — the XOR gadget is `aig::xor`'s shape

`blast_kernel::push_xor` built `(x | y) & !(x & y)`; the shipped `aig::xor`
builds `(a & !b) | (!a & b)`. Same function, different circuit: three AND
gates either way, but different fanins, so the model's CNF was not the
shipped CNF (only equisatisfiable). The model now pushes the shipped shape
in the shipped order. `push_xor_gadget` (`lean/BlasterProof.lean`) was
re-proved; its statement — and therefore every downstream theorem that
counts XOR as three gates (`blast_xor_spec`, `ripple_carry`, `full_adder`,
the multiplier, the divider, the comparisons) — is unchanged.

### Gate identity, tested (every mirrored op, widths 1..=16)

`blast_kernel.rs` tests build each mirrored rule once per (op, width) in
its own fresh AIG pair and check two identities:

1. **raw** — the shipped rule on an `Aig` with folding and hashing *off* is
   node-for-node the model's arena;
2. **replay** — the model's arena, replayed node by node through a default
   `aig::Aig::and` (folding + hashing), is node-identical to the shipped
   rule's AIG built directly, same gates in the same order, same output
   literals.

Result (`gate_identity_raw_every_op_widths_1_to_16`,
`gate_identity_replay_every_op_widths_1_to_16`): all 30 entries identical
under both notions — and, or, xor, add, sub, sub(b,a), mul, udiv, urem,
udivrem (both halves), ult, ule, ugt, uge, slt, sle, sgt, sge, eq, ne, ite,
shl, lshr, ashr, rotr, extract (every range), concat (both orders),
zero_ext, sign_ext (by 0/1/4/w), and the one-bit mux gadget. Negative
control: with the old XOR shape both tests fail at gate 0 of `xor` at
width 1.

One asymmetry remains and is documented in the tests rather than hidden:
the shipped `Aig::and` stores its operands order-normalized (`a.raw() <=
b.raw()`, the strash key, in every mode) while the model stores them as
given. Raw-identity therefore compares gate operands as unordered pairs,
and the Tseitin differential on model-built arenas holds up to that
normalization (the two binary clauses of a gate swapped, the two negated
literals of the ternary clause swapped). On a shipped arena converted
node-for-node to a model arena the two encoders agree byte for byte.
Normalizing in the model's `push_and` would make this exact; it touches
`push_and_spec` (the appended node would become conditional) and was
deferred to phase 2. *Phase 2 resolution:* the model's `push_and` is left
as is. The shipped walk now runs the model's rules and replays them
through `Aig::and`, which normalises; the CNF the solver ships is encoded
from the shipped arena, so the normalisation question is settled by
construction — the proven rules never see the shipped arena, and the
replay (unproven, phase 3) is where the order is fixed.

### The Tseitin proof

`blast_kernel::tseitin` mirrors `cnf::tseitin` clause for clause and in
order: `[-1]` (the constant node), then `(¬o ∨ a) (¬o ∨ b) (o ∨ ¬a ∨ ¬b)`
per AND gate in node order, then one unit clause per asserted output. A
test pins the two encoders to equal `Vec<Vec<i32>>` on the gate-identical
AIGs above and on random circuits.

`lean/BlasterTseitin.lean` (axiom-clean, pinned in `AxiomCheck.lean`):

```lean
theorem tseitin_sat_preserving (aig : Aig) (outputs : Slice Lit)
    (inp : List Bool) (L : Nat)
    (hwf : AigWF aig.nodes.val L)
    (h0 : aig.nodes.val[0]? = some Node.False)
    (hi32 : (aig.nodes.val.length : Int) ≤ I32.max)
    (hcap : 1 + 3 * aig.nodes.val.length + outputs.val.length < Usize.max)
    (houts : ∀ l ∈ outputs.val,
      l.node.val < aig.nodes.val.length ∧
      pEvalLit (pSim inp aig.nodes.val) l = true) :
    tseitin aig outputs ⦃ cnf =>
      cnfHolds (simAsn (pSim inp aig.nodes.val)) (cnf.val.map (fun c => c.val)) ⦄
```

The CNF semantics are Sound.lean's (`cnfHolds` / `unsat`), so the encoder's
output is judged by the meaning `lrat_check_sound` refutes, and the two
halves compose today:

```lean
theorem tseitin_refutes_outputs … (henc : tseitin aig outputs = ok cnf)
    (hchk : kernel.check_steps ⟨cnf.val, cnf.property⟩ steps
      = ok (core.result.Result.Ok ())) :
    ∀ inp : List Bool, ¬ (∀ l ∈ outputs.val,
      l.node.val < aig.nodes.val.length ∧
      pEvalLit (pSim inp aig.nodes.val) l = true)
```

This is the UNSAT direction at the AIG level: a certified refutation of the
encoded CNF refutes the circuit it was encoded from. What it does *not* yet
say: anything about the shipped `cnf.rs` / `aig.rs` (differential tests
only), the term walk, canon, or the front ends — those are phases 2–5.

### Benchmark: what folding and hashing buy

Measured with the `#[ignore]`d `cnf_gap_measurement` test in `solver.rs`
(`cargo test -p ordeal --release --lib --features oracle cnf_gap_measurement
-- --ignored --nocapture`; the oracle corpus is generated in-process, Z3 is
linked but not called). Apple M4 (arm64), macOS 27.0, rustc 1.98.1, release
build, median of 7 runs of `Solver::lower_with` (canon + blast + Tseitin)
per cell. Configurations: **raw** = no folding, no hashing (one gate per
`and` call — the shape of the Lean-modelled arena); **fold** = constant
folding only; **fold+hash** = production (folding + structural hashing).

### benches/latency.rs corpus
| query | config | AIG ANDs | CNF vars | CNF clauses | blast+Tseitin median (µs) |
|---|---|---:|---:|---:|---:|
| srem_vc_32 | raw | 48688 | 48753 | 146066 | 997.5 |
| srem_vc_32 | fold | 37331 | 37396 | 111995 | 648.4 |
| srem_vc_32 | fold+hash | 18413 | 18478 | 55241 | 1474.5 |
| urem_vc_32 | raw | 36352 | 36417 | 109058 | 738.7 |
| urem_vc_32 | fold | 34699 | 34764 | 104099 | 547.5 |
| urem_vc_32 | fold+hash | 17286 | 17351 | 51860 | 1368.8 |
| layout_roundtrip_32 | raw | 128 | 161 | 386 | 4.6 |
| layout_roundtrip_32 | fold | 0 | 33 | 2 | 2.5 |
| layout_roundtrip_32 | fold+hash | 0 | 33 | 2 | 2.5 |
| trap_vc_32 | raw | 515 | 548 | 1547 | 10.5 |
| trap_vc_32 | fold | 127 | 160 | 383 | 4.7 |
| trap_vc_32 | fold+hash | 31 | 64 | 95 | 6.2 |
| ult_cycle_64 | raw | 1728 | 1921 | 5188 | 42.5 |
| ult_cycle_64 | fold | 1716 | 1909 | 5152 | 28.6 |
| ult_cycle_64 | fold+hash | 1716 | 1909 | 5152 | 78.5 |
| shl1_eq_add_64 | raw | 2234 | 2299 | 6704 | 36.3 |
| shl1_eq_add_64 | fold | 0 | 65 | 2 | 4.5 |
| shl1_eq_add_64 | fold+hash | 0 | 65 | 2 | 4.4 |

### benches/bmc.rs corpus
| query | config | AIG ANDs | CNF vars | CNF clauses | blast+Tseitin median (µs) |
|---|---|---:|---:|---:|---:|
| queue_overflow_k16 | raw | 6447 | 6712 | 19360 | 158.3 |
| queue_overflow_k16 | fold | 3318 | 3583 | 9973 | 138.8 |
| queue_overflow_k16 | fold+hash | 3005 | 3270 | 9034 | 203.6 |
| queue_overflow_k32 | raw | 12863 | 13384 | 38624 | 299.9 |
| queue_overflow_k32 | fold | 6630 | 7151 | 19925 | 216.2 |
| queue_overflow_k32 | fold+hash | 5873 | 6394 | 17654 | 399.0 |
| queue_overflow_k64 | raw | 25695 | 26728 | 77152 | 616.5 |
| queue_overflow_k64 | fold | 13254 | 14287 | 39829 | 449.5 |
| queue_overflow_k64 | fold+hash | 11477 | 12510 | 34498 | 837.0 |
| deadlock_k24 | raw | 11743 | 12136 | 35331 | 745.8 |
| deadlock_k24 | fold | 3795 | 4188 | 11487 | 646.3 |
| deadlock_k24 | fold+hash | 2763 | 3156 | 8391 | 825.8 |
| deadlock_k48 | raw | 23455 | 24232 | 70563 | 1565.6 |
| deadlock_k48 | fold | 7587 | 8364 | 22959 | 1274.9 |
| deadlock_k48 | fold+hash | 5523 | 6300 | 16767 | 1564.1 |

### oracle::gen_corpus(0x192, 200) — the Z3 differential corpus (200 queries)
| config | total AIG ANDs | total CNF vars | total CNF clauses | median ANDs/query | median clauses/query | total blast+Tseitin (ms, sum of medians) | median per query (µs) |
|---|---:|---:|---:|---:|---:|---:|---:|
| raw | 6421395 | 6428359 | 19264789 | 5962 | 17890 | 114.28 | 99.7 |
| fold | 3453964 | 3460928 | 10362496 | 1068 | 3207 | 66.98 | 38.1 |
| fold+hash | 3423916 | 3430880 | 10272352 | 1037 | 3113 | 205.29 | 81.8 |

**Reading.** Going raw costs 1.3–3× the CNF (3.1× on `deadlock`, 1.9× on
the oracle corpus). Folding alone recovers most of it, except on the
div/rem-heavy VCs where hashing halves the CNF again (`srem_vc_32`:
37k → 18k ANDs). At blast+Tseitin time hashing is a net *loss* at this
scale — the `HashMap` lookups make fold+hash 1.5–2.5× slower than
fold-only despite fewer nodes; the smaller CNF pays off in SAT time, which
this table does not measure (the existing `latency`/`bmc` benches do, for
the production configuration). For phase 3 (a proven folding/hashing pass
*after* encoding) this says: folding is the pass that matters for size on
most consumer shapes; hashing matters for the divider/multiplier shapes.


## Phase 2: what was delivered

### Design: the walk runs the proven rules through a replay bridge

Option (c) of the phase-1 plan. `solver.rs`'s `Blaster::blast_bv` /
`blast_bool` now name a `blast_kernel::blast_*` rule at every arm; the
five op-family files `blast/{arith,bitwise,shift,muldiv,structural}.rs`
contain no rule body any more (a grep for `aig.and(` / `aig.or(` /
`aig.xor(` / `aig.mux(` / `ripple_carry` / `full_adder` / `barrel` /
`stage_count` / `sub_with_uge` across them returns nothing). They remain
as one-line entry points so the per-family evaluator differentials
(UV-005..UV-009, VER-049) and the Kani harnesses in `blast/proofs.rs`
keep their homes and keep proving the code that runs.

The bridge (`blast/mod.rs`, ~100 lines) is the design the phase-1 plan
suggested. The proven rules build on the reference arena, whose
`push_and` appends exactly one node — the Lean proofs count nodes
(`push_and_spec`), so folding and hashing cannot move there without
weakening every theorem. So each rule runs in two steps: (1) a reference
arena whose primary inputs stand, in order, for the shipped operand
literals (a constant, a complement or a repeated literal is just a
placeholder); the proven rule runs on it unchanged; (2) the arena is
replayed node by node into the shipped `aig::Aig` — input *j* becomes the
literal it stood for, every AND node becomes one `Aig::and` call (folding
+ hashing, exactly as before). A shipped rule used to be that same
`Aig::and` sequence written out by hand, which is what phase 1's
`gate_identity_replay_*` test established; the replay therefore yields
the same arena, the same CNF and the same certificate.

Why not the alternatives: making the proven rules generic over the arena
(a `push_and` trait) is outside the Aeneas fragment the file must stay
in, and folding inside the model's `push_and` is ruled out by the proofs.
The bridge keeps the proven file untouched (this phase changed only its
comments; `lean/regen.sh` was re-run and every proof still closes).

The bridge's working memory (`blast::Scratch`: reference arena,
placeholder table, replay map) is owned by the `Blaster` and reused
across rule calls, so the bridge's own allocations are amortised; the
rules' output words are fresh `Vec`s either way.

### Acceptance: the shipped bytes are unchanged

1. `cli_baseline` passes, and for every `.smt2` under
   `crates/ordeal/tests/fixtures/differential/`, `evidence/certs/` and
   `fuzz/seeds/smtlib/` (24 files) the SHA-256 of `ordeal check <f>
   --format json` (stdout + stderr + exit code; the JSON carries the full
   CNF and, on unsat, the LRAT text) from a release binary built at the
   base commit equals the one from this branch: 0 differ.
2. Stronger, because those fixtures are few and the unsat ones fold to
   `[[-1],[1]]` under canon: the `#[ignore]`d `cnf_gap_digest` test in
   `solver.rs` hashes the production CNF (`num_vars`, every clause, every
   literal) of every query in the bench corpora and in two oracle corpora
   — 1211 queries, 44.6 M clauses. Run on the base commit (the old rule
   bodies, with the same test spliced in) and on this branch:

| corpus | queries | clauses | sha256 of every production CNF (base = branch) |
|---|---:|---:|---|
| benches/latency.rs corpus | 6 | 112352 | `78aaa670cd461529af79ccf2c8ec780d88671f23f8a51aa75abd7bc311b620bb` |
| benches/bmc.rs corpus | 5 | 86344 | `5c14a69e452c4fbfb736c98dade24c06547968e06ec853194e8262a9e26826b5` |
| oracle::gen_corpus(0x192, 200) | 200 | 10272352 | `a1d80de907c207a589d7fd1bb7b4a2d7751764776d85d75e6184d43e64e52597` |
| oracle::gen_corpus(0xC0FFEE, 1000) | 1000 | 34117473 | `42d44115dec319b317cf34e64494b33f29404653a5cbabd4c8334c2b27570f7c` |

3. The phase-1 gate-identity tests (every op, widths 1..=16, raw and
   replayed) and the mirror/real simulation differentials (exhaustive at
   widths 1..=8, sampled to 128) now compare the *bridged* rule against the
   reference arena, so they pin the bridge: it adds no gate and drops none.

### Cost: blast+Tseitin time

Same harness and machine as the phase-1 table (`cnf_gap_measurement`,
Apple M4, macOS 27.0, rustc 1.98.1, release; each cell is the median of 7
`lower_with` runs). Because single runs scatter by ±15% on this machine,
each side was measured in three separate processes and the table shows
the median of the three (all three in parentheses); "base" is the same
test on origin/main's rule bodies, swapped into the tree. Only the
production configuration (folding + hashing) is shown; gate and clause
counts are identical on both sides, as the digests above require.

| query | AIG ANDs | CNF clauses | base, blast+Tseitin | phase 2, blast+Tseitin | ratio |
|---|---:|---:|---:|---:|---:|
| srem_vc_32 | 18413 | 55241 | 1256.4 µs (1215.0, 1256.4, 1413.5) | 1426.2 µs (1403.3, 1426.2, 1477.0) | 1.14× |
| urem_vc_32 | 17286 | 51860 | 1124.2 µs (1120.9, 1124.2, 1157.4) | 1308.5 µs (1297.9, 1308.5, 1323.8) | 1.16× |
| layout_roundtrip_32 | 0 | 2 | 2.4 µs (2.3, 2.4, 2.5) | 5.0 µs (4.4, 5.0, 5.2) | 2.08× |
| trap_vc_32 | 31 | 95 | 6.3 µs (6.2, 6.3, 6.3) | 8.1 µs (8.1, 8.1, 8.5) | 1.29× |
| ult_cycle_64 | 1716 | 5152 | 81.8 µs (77.5, 81.8, 91.3) | 84.8 µs (84.7, 84.8, 85.1) | 1.04× |
| shl1_eq_add_64 | 0 | 2 | 4.4 µs (4.2, 4.4, 4.4) | 13.2 µs (13.1, 13.2, 13.6) | 3.00× |
| queue_overflow_k16 | 3005 | 9034 | 198.0 µs (196.3, 198.0, 199.3) | 236.5 µs (233.2, 236.5, 240.7) | 1.19× |
| queue_overflow_k32 | 5873 | 17654 | 383.1 µs (380.4, 383.1, 389.7) | 452.8 µs (452.0, 452.8, 453.2) | 1.18× |
| queue_overflow_k64 | 11477 | 34498 | 744.1 µs (743.2, 744.1, 752.1) | 863.2 µs (853.9, 863.2, 878.0) | 1.16× |
| deadlock_k24 | 2763 | 8391 | 677.0 µs (669.0, 677.0, 692.9) | 753.9 µs (747.0, 753.9, 764.3) | 1.11× |
| deadlock_k48 | 5523 | 16767 | 1348.0 µs (1339.2, 1348.0, 1349.0) | 1514.8 µs (1511.1, 1514.8, 1534.3) | 1.12× |
| oracle::gen_corpus(0x192, 200), sum of per-query medians | 3423916 | 10272352 | 178.0 ms (176.1, 178.0, 178.5) | 200.0 ms (198.3, 200.0, 200.7) | 1.12× |
| oracle::gen_corpus(0x192, 200), median per query | — | — | 69.7 µs (68.5, 69.7, 70.4) | 108.7 µs (104.5, 108.7, 109.8) | 1.56× |

**Reading.** On every query with real gate work the bridge costs 11–19%
of blast+Tseitin time; `ult_cycle_64` (no folding, no sharing) costs 4%.
The outliers are the two queries whose circuits fold away entirely
(`layout_roundtrip_32`, `shl1_eq_add_64`, 0 ANDs): the old hand-written
rules folded each gate as it was requested and never materialised the
circuit, while the proven rule always builds its full reference arena
(2234 raw gates for `shl1_eq_add_64`) before the replay folds it to
nothing — 2–3× relative, 3–9 µs absolute. The same effect is the 1.56×
on the oracle corpus's *median* query (small, mostly-constant queries)
against 1.12× on its total. The regression is in the stage that the
phase-1 tables already show is a small share of a solve: blast+Tseitin
for `deadlock_k48` is 1.5 ms against a SAT search measured in seconds by
`benches/bmc.rs`. Accepted as the cost of running the proven code; the
mitigations, if it ever matters, are (a) sizing the reference arena's
`Vec` from the operand width (not possible inside the Aeneas fragment
today — `Vec::with_capacity` has no model; it would be a bridge-side
pre-allocation that the kernel cannot use), and (b) phase 3's proven
folding pass, after which the shipped arena *is* the reference arena and
the replay disappears.

### Kani: the harnesses moved to the proven rules

`blast/proofs.rs` (82 harnesses, widths 8/32/64) used to call the shipped
rules on a shipped `aig::Aig`. Through the bridge they do not terminate:
measured 2026-10-01 (Kani 0.67 / CBMC, Apple M4), `and_8` — eight gates —
and `add_8` were still in symbolic execution after 20 minutes each, with
and without the wide tier's `--max-field-sensitivity-array-size 1024`,
where `add_8` took seconds before (6–64 s per fast-tier harness on CI). A
bounded run (`--default-unwind 40`, `and_8`: symex 49 s, 593k steps, then
CBMC out of memory in the SAT phase) names the mechanism: the one loop
whose bound CBMC can no longer see is `Aig::simulate`'s, i.e. the shipped
arena's length is no longer a constant after the replay. A literal read
back out of a reallocated `Vec` (the reference arena and the kernel's
words grow by `push`) is opaque to CBMC's constant propagation, so every
fold in `Aig::and` is a symbolic branch and every push conditional — the
same effect #169 met at width 32 with the hand-written rules, now at
every width. That is structural to the bridge path; `cfg(kani)` capacity
hacks would only rescue the rules that never read an inner word as an
operand.

The harnesses now build each rule on the reference arena and simulate
with the kernel's own `simulate` — the same functions the Lean theorems
are about, as a bounded, independent witness — with their names and tiers
unchanged (`kani_tiers.sh check` passes). Measured on the new harnesses,
2026-10-01, Kani 0.67 / CBMC 6.8.0, Apple M4, wall time (CBMC's own
"Verification Time" in parentheses); the "before" column is the last
timed figure for the old harness from `scripts/kani_tiers.sh` (local,
same machine class, 2026-09-30) or, for the fast tier, CI's 6–64 s band:

| harness | tier | before | kernel harness |
|---|---|---:|---:|
| and_8 | fast | 6–64 s (CI band) | 15 s (12.4 s) |
| add_8 | fast | 6–64 s | 34 s (31.6 s) |
| sub_8 | fast | 6–64 s | 35 s (34.2 s) |
| xor_8 | fast | 6–64 s | 20 s (17.1 s) |
| shl_8 | fast | 6–64 s | 56 s (55.0 s) |
| rotr_8 | fast | 6–64 s | 49 s (45.9 s) |
| eq_8 | fast | 6–64 s | 18 s (15.8 s) |
| slt_8 | fast | 6–64 s | 43 s (41.9 s) |
| ite_8 | fast | 6–64 s | 19 s (16.6 s) |
| concat_4_4 | fast | 6–64 s | 9 s (8.1 s) |
| extract_16_hi | fast | 6–64 s | 13 s (11.0 s) |
| sext_8_8 | fast | 6–64 s | 10 s (8.4 s) |
| mul_8 | heavy | 374 s (CI) | 227 s (223.7 s) |
| xor_32 | wide | 79–83 s | 92 s (90.2 s) |
| add_32 | wide | 238 s | 208 s (204.6 s) |
| udiv_8 | unscheduled | 3035 s (local) | **CBMC exit 139 (segfault) at 17 s** — see below |

All fifteen scheduled samples verify in the same band as before. The one
anomaly is `udiv_8`, which is not in any CI tier (unscheduled since #169:
the runner shut down under it at ~50 min): on the kernel harness CBMC
itself crashed (status 139, a segmentation fault at the start of symbolic
execution, no property reported), reproducibly (3 of 3 runs, 16–17 s;
`urem_8` identically). With the process stack raised from the default
8 MB to the 64 MB hard limit the crash disappears — it is CBMC's own
recursion over the divider's program, not a property — and the run then
goes through symbolic execution (286 s) into the SAT phase, where CBMC
exits out of memory at 20.1 M variables / 70.8 M clauses (941 s wall;
the same with the wide-tier flag, 1025 s). The old harness needed a 64 GB
machine for the same proof (3035 s, #169); this one has 16 GB. The
divider's correctness evidence is unchanged by this — the Lean theorems
`blast_udivrem_bitvec` / `blast_udiv_bitvec` / `blast_urem_bitvec` hold
at every width and the exhaustive width-8 differentials pass — but a
Kani witness for the width-8 divider is currently not available, and
that is recorded here rather than hidden.

What left Kani's coverage: the replay and the shipped fold/hash, covered
by the gate-identity tests (every op, widths 1..=16, raw and replayed),
the exhaustive evaluator differentials and the digests above, until
phase 3 removes the replay.

### What phase 2 does not claim

The proofs cover the rules. Still unproven, in the order the remaining
phases take them: the bridge's replay and the folding and hashing inside
`Aig::and` (phase 3 — a proven folding/hashing pass after encoding,
composed with `tseitin_sat_preserving`); the term walk (phase 3's proven
DAG walk); `cnf.rs` (the shipped encoder; its reference is proven and
pinned clause for clause); canon, lowering, the sliver and the front ends
(phases 4–5). `docs/formal-verification.md` states the same boundary.

## Phase 3: what was delivered

### Design: the lowering is three proven kernel functions in a row

Option (a) of the phase-1 plan, as the stepping stone to (b). The
production path (`solver.rs::lower_with`) is now:

1. **DAG builder** (`dag.rs`, untrusted glue). The canonicalized
   assertions become a `Vec<blast_kernel::DagNode>` in post-order —
   operands before operators, the same left-to-right visit the old walk
   made — hash-consed on `(operator, operand indices)`, constants interned
   by `(value, width)` into a flat bit table, variables shared by name.
   `DagNode` is the closed `term.rs` fragment with operands as node
   indices: `Var(w)`, `Const(start, w)`, the twelve binary word ops,
   `Extract`, `Concat`, `ZeroExt`, `SignExt`, `Ite(c, t, e)`, the ten
   comparisons, `Not`, `BoolAnd`, `BoolOr`. The roots are the asserted
   boolean nodes.
2. **Proven encoder** (`blast_kernel::encode`). Walks the DAG once,
   calling the Lean-proven rule for every node on the append-only
   reference arena (`Var` takes the next `w` primary inputs, in order;
   `Const` is a word of constant literals; the boolean connectives are
   one `push_and` / `push_or`). Returns every node's word and the root
   literals.
3. **Proven compaction** (`blast_kernel::compact`). Rebuilds the raw
   arena node by node with the shipped `Aig::and`'s constant folds in its
   order, its operand-order normalisation, and gate sharing driven by
   *hints*: `hints[i]` names an earlier raw node whose compacted gate
   node `i` may reuse; `hint_matches` checks the named gate really has
   the operands at hand and otherwise pushes a fresh gate. The hints come
   from the untrusted `dag::strash_hints`, which is the old `HashMap`
   strash run over the same fold logic — so the sharing decisions are
   the ones `Aig::and` used to make, gate for gate — but the proof holds
   for *any* hints (`wrong_hints_only_cost_sharing` exercises that:
   hints to node 0, to a pseudo-random earlier node, past the end and an
   empty hint list all give a correct arena).
4. **Proven Tseitin** (`blast_kernel::tseitin`) over the compacted arena
   and the mapped root literals. `cnf.rs` no longer runs in production.

Why the bridge could go: phase 2's replay was `Aig::and` applied to the
reference arena gate by gate; `compact_and` is `Aig::and` spelled in the
Aeneas fragment (the `HashMap` replaced by the checked hint), so
compacting the concatenation of the per-rule reference arenas is the same
computation as replaying each of them. Hash-consing the DAG changes
nothing in the arena either: the old walk re-blasted a repeated subterm,
but every one of those `Aig::and` calls hit the strash and added no node.
`dag::tests::compact_matches_replay_on_a_shared_query` pins the first
claim (the compacted arena is node-for-node the `Aig::and` replay — inputs,
gates, operands, the map of every raw node — and the kernel Tseitin on it is
`cnf::tseitin` on the replay clause for clause, under the production
options and under folding only); the acceptance below pins both on the
shipped bytes.

### The theorems

`lean/BlasterDag.lean` defines the DAG semantics directly over Lean
`BitVec`: `dagSim inp bits ns` folds over the node list, giving each node
a width-tagged `BitVec` (`DVal`) computed from the earlier nodes' values
and the running primary-input counter; `dagWidths` is the width
projection, `DagWF` the syntactic well-formedness (operands are earlier
nodes of agreeing, positive widths; extract ranges fit; boolean operands
have width 1), `dagBool` a root's boolean value. The per-node theorem
`encode_node_spec` is a 32-arm case split, each arm gluing the rule's
structural frame (`lean/BlasterFrame.lean`, new for every rule that
lacked one) to its `_bitvec` capstone with `spec_and` and harvesting the
pure-simulator fact for an arbitrary input list (`harvest`:
`simulate_spec_pSim` plus input-list congruence under `AigWF`). The
headline:

```lean
theorem encode_sound (aig : Aig) (ns : Slice DagNode) (bits : Slice Bool)
    (roots : Slice Std.Usize) (W : Nat)
    (hne : 0 < aig.nodes.val.length) (h0 : aig.nodes.val[0]'hne = Node.False)
    (hwf0 : AigWF aig.nodes.val 0)
    (hdag : DagWF ns.val bits.val.length)
    (hW : ∀ w ∈ dagWidths ns.val, w ≤ W)
    (hcap : aig.nodes.val.length + ns.val.length * gateBound W ≤ Usize.max)
    (hroots : ∀ r ∈ roots.val, r.val < ns.val.length ∧ (dagWidths ns.val).getD r.val 0 = 1) :
    encode aig ns bits roots ⦃ p =>
      aig.nodes.val <+: p.2.nodes.val ∧
      AigWF p.2.nodes.val (dagNin ns.val) ∧
      p.1.1.val.length = ns.val.length ∧
      (∀ (inp : List Bool) (j : Nat) (hj : j < p.1.1.val.length),
        Denotes (pSim inp p.2.nodes.val) (p.1.1.val[j]).val
          ((dagSim inp bits.val ns.val).getD j dDflt).1
          ((dagSim inp bits.val ns.val).getD j dDflt).2) ∧
      p.1.2.val.length = roots.val.length ∧
      (∀ l ∈ p.1.2.val, l.node.val < p.2.nodes.val.length) ∧
      ∀ (inp : List Bool) (k : Nat) (hk : k < p.1.2.val.length),
        pEvalLit (pSim inp p.2.nodes.val) p.1.2.val[k]
          = dagBool inp bits.val ns.val (roots.val.getD k 0#usize).val ⦄
```

`gateBound W = 25·W² + 20·W + 1` is one node's gate budget at operand
widths ≤ W (the worst case is `rotr` at a non-power-of-two width); the
capacity hypothesis is the only place the width bound enters.

`lean/BlasterCompact.lean`:

```lean
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
          = (pSim inp aig.nodes.val).getD j false ⦄
```

(`compact_sound_lit` restates it per literal through `pMapLit`.)

`lean/BlasterCapstone.lean` composes `encode_sound`, `compact_sound_lit`,
`map_word_spec` and phase 1's `tseitin_refutes_outputs` (which already
carries `lrat_check_sound`):

```lean
theorem dag_refuted (ns : Slice DagNode) (bits : Slice Bool) (roots : Slice Std.Usize) (W : Nat)
    (hdag : DagWF ns.val bits.val.length) (hW : ∀ w ∈ dagWidths ns.val, w ≤ W)
    (hcap : 1 + ns.val.length * gateBound W ≤ Usize.max)
    (hroots : ∀ r ∈ roots.val, r.val < ns.val.length ∧ (dagWidths ns.val).getD r.val 0 = 1)
    (aig0 : Aig) (hnew : aig_new = ok aig0)
    (words : alloc.vec.Vec (alloc.vec.Vec Lit)) (outs : alloc.vec.Vec Lit) (aig1 : Aig)
    (henc : encode aig0 ns bits roots = ok ((words, outs), aig1))
    (hints : Slice Std.Usize) (aig2 : Aig) (map : alloc.vec.Vec Lit)
    (hcomp : compact aig1 hints = ok (aig2, map))
    (outs2 : alloc.vec.Vec Lit)
    (hmap : map_word (alloc.vec.Vec.deref map) (alloc.vec.Vec.deref outs) = ok outs2)
    (hi32 : (aig2.nodes.val.length : Int) ≤ I32.max)
    (hcapT : 1 + 3 * aig2.nodes.val.length + outs2.val.length < Usize.max)
    (cnf : alloc.vec.Vec (alloc.vec.Vec Std.I32))
    (htse : tseitin aig2 (alloc.vec.Vec.deref outs2) = ok cnf)
    (steps : Slice kernel.Step)
    (hfit : cnf.val.length + steps.val.length ≤ Std.Usize.max)
    (hchk : kernel.check_steps ⟨cnf.val, cnf.property⟩ steps = ok (core.result.Result.Ok ())) :
    ∀ inp : List Bool, ¬ (∀ (k : Nat) (hk : k < roots.val.length),
      dagBool inp bits.val ns.val (roots.val[k]).val = true)
```

`dag_refuted_raw` is the same with `encode` straight into `tseitin`. All
four capstones are pinned in `lean/AxiomCheck.lean` (axioms: `propext`,
`Classical.choice`, `Quot.sound` only). `lake build`: 1724 jobs, no
`sorry`; `Kernel.lean` / `BlastKernel.lean`: 0 axioms.

### Negative controls

One-line mutations of `blast_kernel.rs`, each followed by `lean/regen.sh
blaster` and a build of the named library (the proof must fail), then a
byte-for-byte restore, `touch`, `regen.sh all` and a clean full build:

| mutation | proof that fails |
|---|---|
| `encode_node`'s `Add` arm calls `blast_sub` | `BlasterDag` (`encode_node_spec`, the `Add` arm's semantics) |
| `compact_and` drops the `x & !x = 0` fold | `BlasterCompact` (`compact_and_spec`) |
| `map_lit` forgets the negation | `BlasterCompact` (`map_lit_spec`) |

### Acceptance: the shipped bytes are unchanged

1. For every `.smt2` under `crates/ordeal/tests/fixtures/differential/`,
   `evidence/certs/` and `fuzz/seeds/smtlib/` (24 files) the SHA-256 of
   `ordeal check <f> --format json` (stdout + stderr + exit code) from the
   v0.25.0 release binary built from `65aa715` equals the one from this
   branch: 24 same, 0 differ.
2. The `cnf_gap_digest` test over the bench and oracle corpora prints the
   four phase-2 digests unchanged:

| corpus | queries | clauses | sha256 of every production CNF (v0.25.0 = phase 3) |
|---|---:|---:|---|
| benches/latency.rs corpus | 6 | 112352 | `78aaa670cd461529af79ccf2c8ec780d88671f23f8a51aa75abd7bc311b620bb` |
| benches/bmc.rs corpus | 5 | 86344 | `5c14a69e452c4fbfb736c98dade24c06547968e06ec853194e8262a9e26826b5` |
| oracle::gen_corpus(0x192, 200) | 200 | 10272352 | `a1d80de907c207a589d7fd1bb7b4a2d7751764776d85d75e6184d43e64e52597` |
| oracle::gen_corpus(0xC0FFEE, 1000) | 1000 | 34117473 | `42d44115dec319b317cf34e64494b33f29404653a5cbabd4c8334c2b27570f7c` |

3. `dag::tests::compact_matches_replay_on_a_shared_query` (above) and the
   phase-1/2 gate-identity and Tseitin differentials, which still pass on
   the bridge path, now a test harness.

### Cost: blast+Tseitin time

Same harness as the phase-1 and phase-2 tables (`cnf_gap_measurement`,
Apple M4, macOS 27.0, release; each cell is the median of 7 `lower_with`
runs; production configuration), "v0.25.0" being the same test run in a
checkout of `65aa715`. Two processes per side this time, both shown; the
ratio takes the better of the two on each side, because the run-to-run
scatter on this machine was larger than in the phase-2 measurement (up to
1.5× on the same binary — the v0.25.0 numbers here are themselves 10–50%
slower than the phase-2 record). Gate and clause counts are identical on
both sides, as the digests above require.

| query | AIG ANDs | CNF clauses | v0.25.0 blast+Tseitin (run 1, run 2) | phase 3 blast+Tseitin (run 1, run 2) | ratio (best of 2) |
|---|---:|---:|---:|---:|---:|
| srem_vc_32 | 18413 | 55241 | 1921.2 µs, 1444.4 µs | 1941.5 µs, 1710.4 µs | 1.18× |
| urem_vc_32 | 17286 | 51860 | 1649.3 µs, 1402.4 µs | 2321.8 µs, 2160.3 µs | 1.54× |
| layout_roundtrip_32 | 0 | 2 | 14.0 µs, 4.8 µs | 5.3 µs, 5.3 µs | 1.10× |
| trap_vc_32 | 31 | 95 | 8.8 µs, 8.3 µs | 7.7 µs, 7.7 µs | 0.93× |
| ult_cycle_64 | 1716 | 5152 | 123.7 µs, 91.0 µs | 146.4 µs, 141.5 µs | 1.55× |
| shl1_eq_add_64 | 0 | 2 | 13.8 µs, 14.6 µs | 20.4 µs, 17.0 µs | 1.23× |
| queue_overflow_k16 | 3005 | 9034 | 259.0 µs, 241.8 µs | 359.1 µs, 356.2 µs | 1.47× |
| queue_overflow_k32 | 5873 | 17654 | 638.5 µs, 457.6 µs | 798.8 µs, 695.1 µs | 1.52× |
| queue_overflow_k64 | 11477 | 34498 | 1456.9 µs, 940.2 µs | 1543.3 µs, 1324.7 µs | 1.41× |
| deadlock_k24 | 2763 | 8391 | 955.2 µs, 788.9 µs | 1038.6 µs, 905.8 µs | 1.15× |
| deadlock_k48 | 5523 | 16767 | 2077.2 µs, 1571.1 µs | 1934.2 µs, 1790.1 µs | 1.14× |
| oracle::gen_corpus(0x192, 200), sum of per-query medians | 3423916 | 10272352 | 219.4 ms, 201.1 ms | 378.7 ms, 372.7 ms | 1.85× |
| oracle::gen_corpus(0x192, 200), median per query | — | — | 124.9 µs, 105.4 µs | 170.6 µs, 168.4 µs | 1.60× |

**Reading.** The proven path costs 1.1–1.55× of phase 2's blast+Tseitin
time on the bench queries and 1.85× on the oracle corpus's total (1.6× on
its median query). The mechanism is structural, not a bug: phase 2
folded and hashed each rule's gates as they were replayed, so a query
whose circuits fold away never materialised more than one rule's raw
arena at a time; phase 3 builds the whole query's raw arena first
(`encode`), then walks it twice more (`strash_hints` with a `HashMap`,
then `compact`), and the DAG builder's own hash-consing maps are a new
fixed cost per query — which is why the small oracle queries pay the
most. The two fold-away queries are no worse (`layout_roundtrip_32`
1.10×, within the scatter; `trap_vc_32` 0.93×). As in phase 2, this is
the stage that is a small share of a solve: `deadlock_k48` spends ~2 ms
here against a SAT search measured in seconds by `benches/bmc.rs`.
Accepted as the cost of running the proven code; the obvious mitigation,
if it ever matters, is to fuse the hint computation into the untrusted
DAG builder (it knows the operands before `encode` runs) and to size the
kernel's `Vec`s from the DAG (not expressible in the Aeneas fragment
today — `Vec::with_capacity` has no model).

### What phase 3 does not claim

The proofs cover `encode`, `compact` and `tseitin` and their composition
with the checker, for a well-formed DAG. Still unproven, in the order the
remaining phases take them: the DAG builder (`dag.rs`: which node is made
for which term, variable sharing by name, hash-consing — a wrong decision
changes the question asked, exactly as the old walk could) and the
`DagWF` side condition, which the builder meets by construction but no
proven code checks (phase 4, where an untrusted certificate carries the
DAG, adds a proven `dag_wf` checker and the `check_query` entry point in
`ordeal-lrat`); canon, lowering, the sliver and the front ends (phases
4–5). The hint generator `dag::strash_hints` is untrusted *by design* —
it decides gate sharing, never a value — and is pinned to the old strash
only by the byte-identity evidence above. `docs/formal-verification.md`
states the same boundary.

## Phase 4: what was delivered

### Design: one translation unit, one entry point, one more block

**The encoder lives in the trusted crate.** `crates/ordeal/src/blast_kernel.rs`
moved to `crates/ordeal-lrat/src/blast_kernel.rs` (the proven code is the
same file; only its header comment changed and the `pub` fields and
variants gained the doc comments the trusted crate's `missing_docs` lint
requires). `crates/ordeal/src/blast_kernel.rs` is now a re-export
(`pub use ordeal_lrat::blast_kernel::*;`) plus the solver-side
differential tests it always had — they compare the kernel against the
solver's `aig.rs` / `cnf.rs` references, which the trusted crate must not
depend on, so the tests stay on the solver side. Nothing else in the
solver changed: `solver.rs::lower_with`, `dag.rs`, `blast/*.rs` and the
Kani harnesses keep calling `crate::blast_kernel::*`. `ordeal-lrat` still
declares no dependencies (its manifest guard test is unchanged).

**The single translation unit is a `#[path]` submodule.** The pinned
Charon/Aeneas translate one crate root per run (`regen.sh`'s open risk
below). `kernel.rs` now declares `#[path = "blast_kernel.rs"] pub mod
blast_kernel;`, which resolves to the same file whether `kernel.rs` is a
module of the cargo crate or the crate root Charon is handed, so `regen.sh
kernel` (now the only mode; `all` and `blaster` are aliases) translates
checker and lowering together into one `lean/Kernel.lean` (6.4 k lines,
0 axioms). The Lean names are `kernel.*` for the checker, exactly as
before, and `kernel.blast_kernel.*` for the lowering; the thirteen
`Blaster*.lean` developments were migrated by changing their `import
BlastKernel` to `import Kernel` and their `namespace blast_kernel.spec`
to `namespace kernel.blast_kernel.spec` — no theorem was restated and no
proof was touched (`lake build`: 1722 jobs, unchanged, before the new
file was added). `BlastKernel.lean` and its lakefile target are gone.

**`kernel::check_query`** (`crates/ordeal-lrat/src/kernel.rs`, the
string-free core; `ordeal_lrat::check_query` is the text-facing entry
that parses the LRAT exactly as `check` does):

```rust
pub fn check_query(ns: &[DagNode], bits: &[bool], roots: &[usize],
                   hints: &[usize], steps: &[Step]) -> Result<Vec<Vec<i32>>, QueryError>
```

1. `dag_wf(ns, bits.len())` — every node against the widths of the nodes
   before it (`node_wf`, a 32-arm match mirroring the Lean `DagNodeWF`:
   operands are earlier nodes of agreeing, positive widths; boolean
   operands have width 1; extract ranges and constant slices fit) and the
   node's width (`node_width`, mirroring `dagNodeWidth`), returning the
   width list. The only thing it rejects that `DagWF` admits is a
   `Concat` / `ZeroExt` / `SignExt` whose width sum passes `usize::MAX`
   (rejected, never wrapped).
2. `roots_wf` — every root is a width-1 node.
3. The capacity hypotheses the theorems carry, computed without overflow:
   `encode_fits(max_width, n)` is `1 + n · gateBound(W) ≤ usize::MAX`
   (every product bounded by a division first), the arena length is
   `≤ i32::MAX`, `tseitin_fits` is `1 + 3·|nodes| + |outs| < usize::MAX`,
   and `|cnf| + |steps| ≤ usize::MAX`. A query past these bounds is
   `QueryError::TooLarge`; nothing of that size is ever produced, and
   rejecting is sound.
4. `aig_new` → `encode` → `compact(hints)` → `map_word` → `tseitin` —
   the same four calls, in the same order, as `solver.rs::lower_with`.
5. `check_steps` on that CNF. `Ok` carries the re-encoded CNF so a bundle
   reader can confirm it is the CNF the bundle also carries for v1
   readers (`QueryRecheckError::CnfMismatch` otherwise); the soundness
   statement does not depend on the payload.

**`ordeal-cert/v2`** (`cert_bundle.rs`, `cert-bundle` feature) is the v1
envelope with `format: "ordeal-cert/v2"` and one more block after
`proof`:

```json
"query": {
  "encoding": "ordeal-dag/v1",
  "num_nodes": 7,
  "nodes": [["const",0,8],["var",8],["add",0,1],["const",8,8],["eq",2,3],["const",16,8],["ne",1,5]],
  "bits": "101000001100000001111111",
  "roots": [4, 6],
  "hints": [0, 1, 2, ...],
  "sha256": "<sha256 of QueryDag::canonical_text>"
}
```

`nodes` is the `DagNode` list as `[op, args…]` in constructor-argument
order (`["const", start, width]`, `["extract", hi, lo, a]`, `["zero_ext",
a, by]`, `["ite", c, t, e]`, `["not", a]`, binary ops `[op, a, b]`);
`bits` is the constant table as a `0`/`1` string; `hints` are the
compaction hints the solver used (`dag::strash_hints`), one per raw arena
node. `problem`, `proof` and their hashes are byte-for-byte v1's;
`recheck.min_version` is `0.27.0` and `recheck.cmd` names
`ordeal_lrat::check_query`. The canonical text the hash covers is in
`query.rs` (`QueryDag::canonical_text`): the encoding tag, `nodes <n>`,
one `<op> <args…>` line per node, `bits …`, `roots …`, `hints …`.

The API: `Solver::check_with_query()` returns
`QueryCheckResult::Unsat(QueryCertificate { certificate, query })` —
the trusted `check_query` runs *before* `Unsat` is returned, symmetric
with the witness gate, so a certificate it would reject degrades to
`Unknown`. `QueryCertificate::to_cert_v2` / `from_cert_v2` /
`QueryBundle::recheck` are the v2 counterparts of the v1 trio; the CLI
emits the block under `ordeal check <f> --format json --with-query`
(JSON only; the flag is refused in text mode). Everything v1 is
untouched: `check`, `check_with_witness`, `to_cert_v1`, `from_cert_v1`,
the default CLI output. A v1 reader refuses a v2 bundle by its `format`
and the v2 reader refuses a v1 bundle — nobody silently downgrades or
upgrades; the two shipped v1 bundles under `evidence/certs/` parse and
re-check through `from_cert_v1` as before (`shipped_v1_bundles_still_parse_and_recheck`).

### The theorems

`lean/QueryCheck.lean` (namespace `kernel.spec`; the exact statements are
in the file and in `docs/formal-verification.md`):

- `dag_wf_spec`: `kernel.dag_wf ns nbits` returns `Ok ws` **iff** `DagWF
  ns nbits` holds and every width fits `usize`, with `ws` the `dagWidths`
  of the DAG — the side condition phase 3 assumed is now decided by proven
  code.
- `check_query_sound`: `kernel.check_query ns bits roots hints steps = ok
  (Ok cnf)` ⟹ for every input assignment, not every root is true — the
  conclusion of `dag_refuted`, with **no hypotheses left**: `dag_wf_spec`
  discharges `DagWF`, `roots_wf_spec` the roots condition,
  `max_width_spec` + `encode_fits_spec` the gate budget, the run-time
  tests the `i32` / `usize` capacities, and `dag_refuted` does the rest.
- `check_query_refutes_cnf`: the returned CNF is `unsat` (from
  `lrat_check_sound`).

Both capstones are pinned axiom-clean in `lean/AxiomCheck.lean`
(`propext`, `Classical.choice`, `Quot.sound` only).

### Negative controls

One-line mutations of `crates/ordeal-lrat/src/kernel.rs`, each followed
by `lean/regen.sh kernel` and `lake build QueryCheck` (the proof must
fail), then a byte-for-byte restore, `touch`, regen and a clean full
build:

| mutation | proof that fails |
|---|---|
| `node_wf`'s `Ite` arm drops `ws[c] == 1` | `QueryCheck` (`node_wf_spec`, hence `dag_wf_spec`) |
| `check_query` runs `tseitin(&aig, &outs)` — the un-mapped root literals on the compacted arena | `QueryCheck` (`check_query_sound`) |

And the bundle-level control the phase was specified by: flip one
constant bit of a v2 bundle's `query` (hash recomputed, so integrity
passes), leave `problem` and `proof` untouched — `QueryBundle::recheck`
fails, while the v1 recheck of the same pair still passes
(`v2_flipped_query_bit_fails_recheck_with_cnf_and_proof_untouched`;
`flipping_one_constant_bit_fails_the_recheck_with_cnf_and_proof_untouched`
in `query.rs` does it for *every* bit of the test query, at the API). A
stale `query.sha256` fails at parse (`HashMismatch("query")`), as do a
forged proof or problem; a wrong encoding, an unknown op or a wrong node
count are `Unsupported` / `Malformed`.

### Acceptance: the shipped bytes are unchanged

For every `.smt2` under `crates/ordeal/tests/fixtures/differential/`,
`evidence/certs/` and `fuzz/seeds/smtlib/` (24 files) the SHA-256 of
`ordeal check <f> --format json` (stdout + stderr + exit code) from the
v0.26.0 release binary built from `4bf1430` (origin/main) equals the one
from this branch: 24 same, 0 differ; the same in text mode. The `query`
block appears only under `--with-query`, and `sat` output is identical
with and without the flag (`with_query_is_opt_in_and_json_only`).

### What phase 4 does not claim

The trusted re-check certifies the **lowered** DAG a bundle carries.
Still unproven, in the order phase 5 takes them: the DAG builder
(`dag.rs`: which `DagNode` is made for which term, variable sharing by
name, hash-consing) — a wrong decision changes the question asked, but it
is now *visible* in the certificate, so a consumer (or a round trip from
SMT-LIB to the DAG and back) can audit it; canon (`canon.rs`, including
constant folding via `eval.rs`); **the lowering of the derived ops**
(`lowering.rs`: `bvnot`, `bvneg`, `bvrotl`, `bvsdiv`, `bvsrem`, … are
still rewritten into the closed core *before* the DAG is built, so a v2
bundle carries the rewritten query, not the derived op — "derived ops
become proven DAG constructs" is deferred to phase 5 because `DagNode` is
the closed `term.rs` fragment and adding an operator means adding a
proven rule); the sliver; the SMT-LIB and Verus front ends. The hints
stay untrusted *by design* (`compact_sound` holds for any hints); a wrong
hint set changes gate sharing, so the re-encoded CNF differs from the
carried one and the bundle is rejected as inconsistent rather than
accepted on a different formula (`hints_are_advice_not_trust`).

## Phase 5: what was delivered

### Design: each derived op is its rewrite, spelled over the proven rules

Until phase 5 the five derived operations synth emits — `bvnot`, `bvneg`,
`bvrotl`, `bvsdiv`, `bvsrem` — were rewritten into the closed core by
`lowering.rs` *before* the term DAG was built (`bvneg x = 0 - x`, the
SMT-LIB sign-mask construction for `bvsdiv`, …). The rewrite was backed
by tests and Z3 only, and a v2 bundle carried the rewritten query, so a
consumer certified `(q ^ (sa ^ sb)) - (sa ^ sb)` rather than `bvsdiv`.

Phase 5 makes each of them a construct of the closed fragment with a
proven rule — the admission criterion of CLAUDE.md:

1. **`DagNode` gains five constructors** — `BvNot(a)`, `Neg(a)`,
   `Rotl(a, b)`, `Sdiv(a, b)`, `Srem(a, b)` — and `BvTerm` the matching
   variants (`Not`, `Neg`, `Rotl`, `Sdiv`, `Srem`; the SMT-LIB front end
   builds them directly, `lowering::bvsdiv` and friends now construct
   them, so API consumers keep working). The `encode_node` arm of each
   is a **composition of the already-proven rules in the rewrite's own
   operand order** (`crates/ordeal-lrat/src/blast_kernel.rs`):
   `blast_bvnot = word_not` (gate-free: the XOR with all-ones folds to
   exactly these literals in `compact`), `blast_neg = blast_sub(0, a)`,
   `blast_rotl = blast_rotr(a, 0 - b)` at a power-of-two width and
   `blast_rotr(a, (w - b urem w) urem w)` otherwise, `blast_sdiv` = the
   sign-mask construction (`sign_mask = ashr(x, w-1)`, `abs_word =
   (s ^ x) - s`, `udiv`, two XORs and a subtraction), `blast_srem =
   a - blast_sdiv(a, b) * b` (multiplicative, #97, unchanged).
2. **`node_wf` / `node_width`** (`kernel.rs`) treat them as the word
   operators they are (`un_wf` for the unary two, `bin_wf` for the
   rest); `dag_wf_spec`'s iff is re-proved (`un_wf_spec`).
3. **The gate budget grew:** `gateBound W` is now `70·W² + 70·W + 1`
   (was `25·W² + 20·W + 1`): `bvrotl` at a non-power-of-two width runs
   three remainders plus the barrel (`66·w² + 60·w + 3·w·stages`). The
   Rust `encode_fits` spells the same polynomial, `encode_fits_spec` is
   re-proved against it. At `w ≤ 128` this is `1.2·10⁶` gates per node
   against `usize::MAX`: nothing a solver produces comes near it.
4. **Two lowering paths, one proven encoder.** `Solver::check` /
   `check_with_witness` (and `ordeal check` without `--with-query`) apply
   the rewrite first — `lowering::expand_bool`, the v0.27.0 lowering as
   one pass over the term — then canon, then the DAG, so their
   certificates are byte-identical to v0.27.0's (`DerivedOps::Rewrite`).
   `Solver::check_with_query` (and `--with-query`) does not rewrite: the
   derived ops reach the DAG as their own nodes, the proven composite
   rules encode them, and the v2 query block carries the operation
   (`DerivedOps::Nodes`). Why two paths, below.

### The theorems

`lean/BlasterDerived.lean` (new; namespace `kernel.blast_kernel.spec`),
each stated in the standard simulate-wrapped capstone shape of every
other rule, for every width `w ≥ 1`:

```lean
theorem blast_bvnot_bitvec (a : Slice Lit) {w : Nat} (A : BitVec w) :
    blast_bvnot a ⦃ out => ∀ vals, Denotes vals a.val w A → Denotes vals out.val w (~~~A) ⦄

theorem blast_neg_bitvec … (A : BitVec w) :
    blast_neg aig a ⦃ p => ∀ inputs, AigWF … → simulate p.2 inputs ⦃ vals =>
      Denotes vals.val a.val w A → Denotes vals.val p.1.val w (-A) ⦄ ⦄

theorem blast_rotl_bitvec … (A B : BitVec w) :
    blast_rotl aig a b ⦃ p => … Denotes vals.val p.1.val w (A.rotateLeft (B.toNat % w)) ⦄ ⦄

theorem blast_sdiv_bitvec … (A B : BitVec w) :
    blast_sdiv aig a b ⦃ p => … Denotes vals.val p.1.val w (A.smtSDiv B) ⦄ ⦄

theorem blast_srem_bitvec … (A B : BitVec w) :
    blast_srem aig a b ⦃ p => … Denotes vals.val p.1.val w (A.srem B) ⦄ ⦄
```

`BitVec.smtSDiv` is Lean core's SMT-LIB signed division (all-ones
quotient on division by zero, so `a sdiv 0 = -1` for `a ≥ 0` and `1`
otherwise; `INT_MIN sdiv -1 = INT_MIN`), `BitVec.srem` is core's
sign-of-the-dividend remainder (`a srem 0 = a`, `INT_MIN srem -1 = 0`),
`BitVec.rotateLeft` reduces its amount mod the width. The mathematics
is four `BitVec` lemmas: `rotateRight_sub_eq_rotateLeft` (rotating right
by `(w - r) % w` is rotating left by `r`) with
`rotateRight_neg_eq_rotateLeft` for the power-of-two branch (`2^w` is a
multiple of `w = 2^s`, the identity that is *false* at other widths —
0.22.1 — which is why the other branch reduces explicitly);
`sshiftRight_last` (`ashr(x, w-1)` is the sign mask), `xor_sub_signMask`
(`(s ^ x) - s` is `-x` under the all-ones mask and `x` under the zero
mask) and `sdiv_construction` (the whole construction equals `smtSDiv`,
four sign cases); and `srem_eq_sub_smtSDiv_mul` (`A.srem B = A -
A.smtSDiv B * B` for all `B`, zero included, from phase 2's
`umod_eq_sub_smtUDiv_mul` in each sign case).

The compositions are proved in a *pure conditional* form (`bin_pure_of_sim`
harvests a rule's capstone at the pure level, `Denotes.up` transports the
operand facts along the aig prefixes; `sim_of_pure` turns the result
back into the simulate-wrapped statement); `BlasterDag.lean` gains the
five arms of `encode_node_spec` (37 node kinds now; `bin_word_rule_pure`
/ `un_word_rule_pure` glue a pure-form rule to `NodePost`) and the three
budget lemmas `rotl_le_gateBound`, `sdiv_le_gateBound`,
`srem_le_gateBound`. `dagSim` / `DagWF` / `dagNodeWidth` cover the new
constructors; `encode_sound`, `compact_sound`, `dag_refuted`,
`dag_wf_spec`, `check_query_sound` and `check_query_refutes_cnf` are
re-established with their statements unchanged (the DAG language is
larger; `gateBound` is a `def` whose value changed). The five new
capstones are pinned axiom-clean in `lean/AxiomCheck.lean` next to every
earlier one. `lake build`: 1726 jobs, no `sorry`; `Kernel.lean`: 0 axioms.

### Negative controls

One-line mutations, each followed by `lean/regen.sh all` and a build of
the named library (the proof must fail), then a byte-for-byte restore,
`touch`, regen and a clean full build:

| mutation | proof that fails |
|---|---|
| `blast_sdiv`: the result sign uses `sign_mask(a)` twice (`rs = sa ^ sa`) — wrong sign handling | `BlasterDerived` (`blast_sdiv_pure`, line 1260: the final `sdiv_construction` rewrite no longer unifies — the output denotes `(Q ^ 0) - 0`, not `smtSDiv`) |
| `blast_rotl`: the power-of-two branch computes `b - 0` instead of `0 - b` (rotates by `b`) | `BlasterDerived` (`blast_rotl_frame` line 562 and `blast_rotl_pure` line 706: the subtraction step no longer has the zero word as its first operand, and `rotateRight_neg_eq_rotateLeft` would not apply) |
| `blast_neg`: `blast_sub(a, zero)` instead of `blast_sub(zero, a)` | `BlasterDerived` (`blast_neg_frame` line 403 and `blast_neg_bitvec` line 432: the proof steps through `blast_sub(zero, a)`; the mutated rule denotes `A - 0`, not `-A`) |
| `node_wf`: the `Sdiv` arm uses `bool_bin_wf` | `QueryCheck` (`node_wf_spec` line 180: unsolved goals, hence `dag_wf_spec`) |

(The `lake build` exit codes and the first error lines of each run are
in the execution record VE-054; the sources were restored byte-for-byte
— SHA-256 `c5fef1ad…` for `blast_kernel.rs`, `7b281b69…` for
`kernel.rs` — touched, regenerated (0 axioms) and the full tree rebuilt
clean, 1726 jobs, with the axiom gate, before the final test runs.)

And the bundle-level control the phase was specified by: a v2 bundle of
the refutation `(a sdiv b) ≠ rewrite(a sdiv b)` whose `sdiv` node is
changed to `udiv` (hash recomputed, so integrity passes; CNF and proof
untouched) fails `QueryBundle::recheck`, while the v1 recheck of the same
pair still passes
(`v2_sdiv_node_swapped_to_udiv_fails_recheck_with_cnf_and_proof_untouched`;
`sdiv_node_swapped_to_udiv_fails_the_recheck` at the API, in both
directions). The semantics differ for a negative dividend, so the control
is not a formatting accident.

### The v2 query block: `ordeal-dag/v2`

A DAG that uses one of the five new node kinds is emitted under the
encoding tag `ordeal-dag/v2` (`bvnot`, `neg`, `rotl`, `sdiv`, `srem`
spellings) with `recheck.min_version` `0.28.0`; a DAG without them keeps
`ordeal-dag/v1` and `0.27.0`, so v0.27.0 readers keep reading what they
could read and refuse (`Unsupported`) what they could not. The reader
accepts both tags, hashes the block under the tag it *declares*
(`QueryDag::sha256_tagged`), and refuses a v1-tagged block that carries
a derived node (`Malformed`). The shipped v1 bundles under
`evidence/certs/` parse and re-check unchanged.

### Acceptance: the shipped bytes are unchanged — and why the default path keeps the rewrite

1. For every `.smt2` under `crates/ordeal/tests/fixtures/differential/`,
   `evidence/certs/` and `fuzz/seeds/smtlib/` (24 files) the SHA-256 of
   `ordeal check <f> --format json` (stdout + stderr + exit code) from
   the v0.27.0 release binary built from `97d314f` (origin/main) equals
   the one from this branch: 24 same, 0 differ; the same in text mode
   (48/48).
2. The `cnf_gap_digest` test over the bench and oracle corpora prints the
   four digests unchanged (1211 queries, 44.6 M clauses):

| corpus | queries | clauses | sha256 of every production CNF (v0.27.0 = phase 5) |
|---|---:|---:|---|
| benches/latency.rs corpus | 6 | 112352 | `78aaa670cd461529af79ccf2c8ec780d88671f23f8a51aa75abd7bc311b620bb` |
| benches/bmc.rs corpus | 5 | 86344 | `5c14a69e452c4fbfb736c98dade24c06547968e06ec853194e8262a9e26826b5` |
| oracle::gen_corpus(0x192, 200) | 200 | 10272352 | `a1d80de907c207a589d7fd1bb7b4a2d7751764776d85d75e6184d43e64e52597` |
| oracle::gen_corpus(0xC0FFEE, 1000) | 1000 | 34117473 | `42d44115dec319b317cf34e64494b33f29404653a5cbabd4c8334c2b27570f7c` |

3. **Would the bytes change if the default path lowered the derived ops
   as nodes?** Yes, for some queries. The composite rule *is* the
   rewrite's gate sequence (`derived_rules_are_the_rewrite`: the raw
   arena of a DAG holding the node is, gate for gate, the raw arena of the
   DAG the rewritten term builds, at widths 1, 5, 8, 12, 32, operands
   created first; `bvnot` compacts to the same literals as its XOR), and
   on the three fixtures that use a derived op (`rotate_left` at widths 5
   and 12) `--with-query` emits the same CNF and LRAT as the default. But
   two things outside the rule can differ between the two paths:
   - **canonicalization orders commutative operands by the operands'
     `Debug` names**, and a node's name sorts differently from its
     rewrite's (`Not(` before `Var`, `Xor(` after it; inside the rewritten
     `bvsdiv` tree `Xor(a, sa)` becomes `Xor(sa, a)` only for some operand
     shapes) — so an `Eq`/`Ne`/`Xor`/`Mul` parent or inner node can swap
     its operands on one path and not the other, which changes the XOR
     gadget's gate order;
   - **a variable whose first occurrence is inside a derived op's second
     operand** gets its primary inputs created in the middle of the
     rewritten tree on the default path and before the node's gates on the
     other, so the arena — and the CNF's variable numbering — differ.

   Measured: `benches/latency.rs corpus (derived ops as nodes)` digests to
   `7b35d569f722f36db0200c2ab541b6e82fb156ff4ccbb4fefc208d52118e1e84` —
   the same 112352 clauses, different bytes, all of it `srem_vc_32` (the
   second mechanism: `b` first occurs inside `bvsrem(a, b)`); the other
   corpora contain no derived op. `derived_nodes_can_renumber_the_cnf`
   pins that case, `derived_nodes_lower_to_the_rewrite_cnf_when_operands_come_first`
   pins the identity when neither mechanism applies. Both paths are
   certified (every `--with-query` UNSAT is re-encoded and re-checked by
   the trusted crate before it is returned), so this is a question of
   *which bytes ship*, not of soundness — and therefore the maintainer's
   call: the switch is one line (`Solver::lower`, `DerivedOps::Rewrite`
   → `Nodes`). Until it is made, `lowering.rs`'s rewrite stays on the
   default path exactly as before (untrusted, backed by the same width-8
   exhaustive reference test, the Z3 differential — now stated about
   `expand_bv` — and, new, `rewrite_equals_the_proven_rule_with_a_trusted_recheck`:
   `op(a, b) ≠ rewrite(op(a, b))` is refuted through `check_with_query`
   for every derived op at widths 8/32(/64), i.e. the trusted crate
   re-encodes the DAG holding both and certifies the refutation).

### Evidence for the rules beyond the proofs

- `derived_rules_match_the_evaluator`: the five rules on the reference
  arena against the evaluator's own SMT-LIB definitions (now spelled in
  `eval.rs`, not via the rewrite), exhaustively at every width 1..=6
  (every operand pair: every sign combination, `/0`, `INT_MIN / -1`,
  rotate amounts at and beyond the width, power-of-two and other widths)
  and sampled at widths 7..=16, 24, 32, 64, 128.
- `oracle::derived_ops_differential_through_check_with_query` (the
  `oracle` feature): the five rules against Z3's native `bvnot`, `bvneg`,
  `ext_rotate_left`, `bvsdiv`, `bvsrem` at every corpus width (3, 5, 8,
  12, 24, 32, 64), through `check_with_query` — symbolic `op(a, b) = r`
  (SAT, models re-evaluated on both sides), and for the edge constants
  (`0`, `1`, all-ones, `INT_MIN`, `INT_MAX`, `2`, `w`, `w + 1`) both
  `op(x, y) ≠ eval(op(x, y))` (UNSAT, trusted-rechecked) and
  `op(a, y) = eval(op(x, y))` (SAT). 21 oracle tests pass; no `Unknown`.
- `exhaustive_width8_div_rem_family_matches_smtlib_reference` now checks
  both the evaluator's `Sdiv`/`Srem` and the rewrite against the
  independent reference over all 65536 width-8 pairs.

### What phase 5 does not claim

The trusted re-check certifies the DAG a v2 bundle carries — now
including the derived operations themselves. Still unproven, in the
order the remaining phases take them: the DAG builder (`dag.rs`); canon
(`canon.rs`, including constant folding via `eval.rs` — whose `Sdiv` /
`Srem` / `Rotl` / `Neg` / `Not` definitions are tested, not proven); the
rewrite `lowering::expand_*` on the **default** path (a v1 certificate
from `check` still carries the rewritten query; the v2 certificate from
`check_with_query` does not); the sliver; the SMT-LIB and Verus front
ends. No Kani harness was added for the five composite rules (the Lean
theorems hold at every width; `kani_tiers.sh check` requires every
harness to be tiered with a measured time, and none was measured) — an
open item, not a gap in the proof. `blast_rotl` at a non-power-of-two
width reproduces the rewrite's three remainders rather than the two it
needs, deliberately (gate identity with the rewrite); a cheaper rule
changes the bytes of such queries and is a separate decision.

## Phase 6: what was delivered — the SAT direction (TR-065)

### The gap

Phases 3–5 closed the query→CNF gap for **unsat**: `check_query` is
proven to refute the term DAG. The **sat** direction had no such step.
A `Sat` answer rested on three checks, two of them trusted-by-proof at
the CNF level only (`check_sat`: the assignment satisfies the CNF;
`check_binding`: the advertised model is the assignment's input bits) and
one untrusted and unproven: `eval.rs::eval_bool`, the solver's own
evaluator, re-running the ORIGINAL assertions under the model
(`solver.rs::decode_and_check`). Whether the model satisfies the *query*
— the DAG, in the semantics the unsat theorem is stated over — was the
evaluator's word. A bug in `eval.rs` (or in the CNF-side claim that a
model of the CNF is a model of the DAG, which `tseitin_satisfiable`
states only for the raw AIG) could yield a `Sat` with a wrong model and
nothing proven to notice.

### Design: no new evaluator — the proven encoder plus the proven simulator

`kernel::check_query_model(ns, bits, roots, inp)` (TR-065) is
`check_query`'s SAT twin, built entirely from pieces the unsat direction
already proved, so nothing new has to be trusted:

1. `dag_wf`, `roots_wf`, `max_width`, `encode_fits` — the same checks,
   establishing `encode_sound`'s hypotheses (`dag_wf_spec`,
   `roots_wf_spec`, `max_width_spec`, `encode_fits_spec`, unchanged).
2. `dag_nin` (the one new kernel function, 15 lines): the DAG's
   primary-input count — the sum of the `Var` widths in node order,
   which is how `encode` numbers the AIG inputs and how `dagSim` reads a
   `Var`'s bits off the input list. `inp.len() < nin` is rejected
   (`ModelTooShort`), never padded: `simulate` indexes `inputs[k]`, so
   the proof needs `AigWF aig inp.len`, which `AigWF_mono` gives from
   `encode_sound`'s `AigWF aig (dagNin ns)` exactly when `dagNin ns ≤
   inp.len`. (`dag_nin_spec`: `Ok n ⟹ n = dagNin ns`; the overflow guard
   is unreachable after `encode_fits` accepted — `nin ≤ n·W ≤
   n·gateBound W` — and kept so the function is total on its own.)
3. `aig_new` → `encode` (the proven encoder), then `simulate` (the
   proven simulator, `simulate_spec`: the kernel's run IS `pSim`), then
   `eval_lit` on every asserted output literal (`eval_lit_spec`); the
   first false literal is `RootFalse { root }`.

No compaction and no Tseitin: the model is checked against the raw
encoding, which is what `encode_sound` speaks about. The CNF-level
witness (`check_sat` / `check_binding`) stays the v1 check and still runs
first in the untrusted `recheck()` (defence in depth), but the answer now
rests on the trusted evaluation.

### The theorems

`lean/QueryCheck.lean` (namespace `kernel.spec`), `sorry`-free and
axiom-clean (pinned in `lean/AxiomCheck.lean`):

```lean
theorem check_query_model_sound (ns : Slice kernel.blast_kernel.DagNode) (bits : Slice Bool)
    (roots : Slice Std.Usize) (inp : Slice Bool)
    (h : kernel.check_query_model ns bits roots inp = ok (core.result.Result.Ok ())) :
    ∀ (k : Nat) (hk : k < roots.val.length),
      dagBool inp.val bits.val ns.val (roots.val[k]).val = true

theorem check_query_model_satisfiable … (h : … = ok (core.result.Result.Ok ())) :
    ¬ ∀ inp' : List Bool, ¬ (∀ (k : Nat) (hk : k < roots.val.length),
      dagBool inp' bits.val ns.val (roots.val[k]).val = true)

theorem query_verdicts_exclusive (ns bits roots hints steps cnf inp)
    (hu : kernel.check_query ns bits roots hints steps = ok (core.result.Result.Ok cnf))
    (hs : kernel.check_query_model ns bits roots inp = ok (core.result.Result.Ok ())) : False
```

The conclusion is **the same `dagBool`** that `check_query_sound`
negates (`∀ inp, ¬ ∀ k, dagBool inp … = true`), so the SAT and the UNSAT
claim about one query are about one semantics — `query_verdicts_exclusive`
is the one-line composition, the query-level twin of `verdicts_exclusive`
(TR-044). The proof (~170 lines, incl. the two loop specs
`dag_nin_loop_spec` and `check_query_model_loop_spec`) is the
composition described above: `encode_sound`'s last conjunct — `∀ inp k,
pEvalLit (pSim inp aig) outs[k] = dagBool inp bits ns roots[k]` — does the
heavy lifting; nothing about any blast rule is re-proven. Statements of
every earlier theorem are unchanged; `Kernel.lean`: 0 axioms before and
after.

### Negative controls

One mutation of the trusted function, `lean/regen.sh all`, the proof
must fail; then a byte-for-byte restore, regen, clean rebuild:

| mutation | what fails |
|---|---|
| `check_query_model`: the output loop no longer returns `RootFalse` (`if !eval_lit(…) && false`) — the check accepts every assignment | Rust: `check_query_model_accepts_a_witness_and_rejects_a_falsified_root`, `check_query_model_reads_inputs_in_node_order_lsb_first`, `tampering_the_inputs_or_the_query_fails_the_model_recheck`, `a_rejected_model_degrades_to_unknown_not_sat`, `v2_sat_bundle_flipped_input_bit_fails_recheck_with_witness_untouched`, `format_json_with_query_carries_a_recheckable_model`; Lean: `QueryCheck` (`check_query_model_loop_spec`: the `done (Ok ())` arm no longer carries `pEvalLit … = true`, hence `check_query_model_sound`) |

(Exit codes and first error lines in VE-055.)

And the API- and bundle-level controls the phase was specified by, all
with the v1 witness (CNF, assignment, bit map) UNTOUCHED and still
re-checking — exactly what the CNF-level checks cannot see: every single
flipped input bit of a unique-model query is rejected (`RootFalse`); a
negated root is rejected with the inputs untouched too; every flipped
constant bit of the query is rejected; a `vars` entry pointing at the
other variable's node fails the untrusted consistency check; and in the
solver the rejected certificate degrades to `Unknown`, never a wrong
`Sat` (`Solver::sat_verdict`).

### The v2 SAT bundle and `--with-query` on `sat`

`QueryCheckResult::Sat` now carries a `QuerySatCertificate` — `witness`
(the v1 `SatCertificate`, unchanged), `query` (the same `QueryDag` block
as the unsat side) and `inputs` (`QueryInputs`: the DAG's input bits as
a `0`/`1` string, input 0 first, plus the untrusted `(name, width, Var
node)` map, with its own sha256 over a canonical text tagged
`ordeal-inputs/v1`). `QuerySatCertificate::to_cert_v2` /
`from_cert_v2` emit and read the SAT `ordeal-cert/v2` bundle: the v1
witness envelope plus `query` and `inputs` after `witness`,
`recheck.min_version` `0.29.0` and a `cmd` naming `check_query_model`;
all five hashes verified before `QuerySatBundle::recheck`. `ordeal check
--format json --with-query` prints the same two blocks inside
`certificate` on `sat`; without the flag the output is byte-identical,
and every v1 reader and bundle is untouched. The API change: the payload
of `QueryCheckResult::Sat` (a one-release-old, opt-in entry) is the
wrapper; `.witness` is what it used to be.

### What phase 6 does not claim

The trusted re-check certifies that the DAG a v2 SAT bundle carries is
satisfied by the input bits it carries. Still trusted, as for the unsat
direction: the DAG builder (`dag.rs`) — that the DAG asks the caller's
question, and that the `Var` node it made for a name is the one the
model's value is written into (`QueryInputs::from_model`, the
`(name, width, node)` map; the untrusted `check_consistent` only confirms
the advertised model agrees with the carried inputs); canonicalization
(`canon.rs`, constant folding via `eval.rs`); the sliver and the front
ends. The CNF-level witness is NOT what the sat answer rests on any
more; it is kept as defence in depth and for v1 readers. `eval.rs` stays
in `decode_and_check` for the same reason — and because `check` /
`check_with_witness` (the default paths) still return `Sat` on the CNF
witness plus the evaluator: closing the sat gap on the DEFAULT path means
paying the second encoding there too, which is the maintainer's call, as
it was for unsat (phase 4 kept it opt-in). Until then, the trusted sat
gate is where the trusted unsat gate is: `check_with_query` and
`--with-query`.

## Open risks

- ~~Aeneas/Charon at the pinned revision with a single translation unit
  holding both the kernel and the encoder (`regen.sh` translates one file
  per crate root).~~ **Resolved in phase 4** by the `#[path]` submodule
  (above): the pinned Charon follows rustc's module loading, and Aeneas
  emits the submodule under `kernel.blast_kernel.*` in the same file.
  Phases 1–3 had kept the encoder in `blast_kernel.rs` (the blaster's own
  translation unit) with the proof files importing both generated models.
- The performance cost of going without hashing — measured above.
- `check_with_query` lowers twice (solve, then the trusted re-check);
  opt-in, so `check` pays nothing. A `cfg(debug_assertions)` note: the
  trusted crate's arithmetic is modelled by Aeneas as failing on overflow,
  while a release build wraps; the new `check_query` code reaches no
  arithmetic that can overflow (every sum and product is bounded by a
  comparison or a division first) — the earlier kernels' `usize` sums are
  bounded by the slices' sizes, as `docs/formal-verification.md`'s `hfit`
  note explains.


### Phase 5 default switch (2026-10-13, maintainer decision)

`Solver::lower` and `check_with_witness` now use `DerivedOps::Nodes`.
`DerivedOps::Rewrite` survives only for the differential tests comparing the
old rewrite with the proven nodes. Measured on the switch:

- all 24 fixture queries are byte-identical to v0.27.0;
- the `cnf_gap_digest` corpora are unchanged: latency `7b35d569…`, bmc
  `5c14a69e…`, oracle 0x192 `a1d80de9…`, oracle 0xC0FFEE `42d44115…`;
- the Z3 differential passes (13).

The stored `evidence/certs` bundles record producer version 0.23.0.
Regenerated with a later ordeal, their CNF and proof payloads are
byte-identical and only the two version fields differ (see OC-001 and
OC-002).

## Phase 7 design: the term-to-DAG translation

**Status:** design, 2026-10-15; nothing below is implemented. **Scope:**
what is still *trusted* on the query path after phase 6, and how to
prove it. **Decision requested:** option (C) below.

### What is still trusted, exactly (claims checked against the code)

After phases 4–6 the trusted crate re-checks both answers against the
query DAG — `check_query` (`check_query_sound`) and `check_query_model`
(`check_query_model_sound`), both stated over `dagBool`, the Lean
`BitVec` semantics of `lean/BlasterDag.lean`. The DAG they speak about
is the one `solver.rs::lower_with` builds; the step from the caller's
assertions to that DAG is unproven. Pinned to the code as of this
design (v0.29.0 + #236):

| piece | what it decides | where | status |
|---|---|---|---|
| `lowering::expand_bool` (the derived-op rewrite) | `bvnot`/`bvneg`/`bvrotl`/`bvsdiv`/`bvsrem` as core terms | `lowering.rs` | **not on any production path** since the 2026-10-13 switch (`Solver::lower` and `check_with_witness` use `DerivedOps::Nodes`; `DerivedOps::Rewrite` is `cfg_attr(not(test), allow(dead_code))` and reached only by the differential tests). Nothing to prove; the issue text predates the switch. |
| `canon::canonicalize_bool` / `canonicalize_bv` | (1) order the operands of `Add`/`Mul`/`And`/`Or`/`Xor` and of `Eq`/`Ne` by the `Debug` string of the *canonicalized* operands (`cmp_bv`); (2) mirror `Ugt`/`Uge`/`Sgt`/`Sge` to `Ult`/`Ule`/`Slt`/`Sle` with the operands swapped; (3) fold every all-constant **bitvector** subterm to a `Const` through `eval::eval_bv` (`u128`, width-masked; `BoolTerm`s are never folded, but an `Ite` whose condition and branches are constant is) | `canon.rs`, 267 lines | trusted; `denotation_guard` (#240) checks it against `eval.rs` |
| `dag::DagBuilder` | post-order, left-to-right (`Ite`: condition first); hash-consing on `(op, operands)` via `HashMap`; constants interned by `(value, width)` into one bit table; variables shared **by name**, their primary inputs numbered by first occurrence | `dag.rs` | trusted; same guard |
| `query::QueryInputs::from_model` + `check_consistent` | the named model value → the `Var` node's input bits | `query.rs` | trusted (the `(name, width, node)` map is untrusted glue; `check_consistent` compares bits but is not part of any theorem) |
| the front ends and the sliver | SMT-LIB / Verus text → `BoolTerm`; array/UF → core | `smtlib.rs`, `verus.rs`, `sliver.rs` | trusted; out of scope for #192 |

#240's `dag::denotation_guard` (1500 seeded assertions, every operator,
widths 1..=128, models biased to the edge values: `check_query_model`
accepts iff `eval.rs` says the ORIGINAL assertion holds) is the
regression oracle for all of the first three rows. It is evidence; phase
7 is the proof.

### The constraint that shapes the design

`check_query` re-encodes the carried DAG and requires the result to be
the CNF the LRAT proof refutes, gate for gate. The solver's CNF comes
from the **canonicalized, hash-consed DAG in the solver's node order**
— call it **D1**. So whatever the trusted side reasons about must be D1
itself, not a semantically equal DAG. Three consequences:

1. Anything that *rebuilds* D1 must reproduce canon's ordering
   decisions. Those are comparisons of `format!("{:?}")` strings of
   subterms (`canon::cmp_bv`), chosen for determinism and nothing else.
   A `String` is outside the Aeneas fragment (`kernel.rs`: "no `&str`,
   no `String`"), and re-specifying the order on the trusted side would
   be proving a `Debug` impl. **The decision has to arrive as a hint.**
2. D1's node order is the post-order of the tree *after* the swaps, and
   a variable's primary inputs are numbered at its first occurrence in
   that order (phase 5 measured exactly this: `srem_vc_32`'s CNF was
   renumbered because `b` first occurs inside the second operand). So
   D1's order is not the term's order, and a trusted *builder* driven by
   the term would need an order hint on top of the swap hints.
3. Constant folding needs an evaluation on the trusted side. A `u128`
   evaluator proven against `BitVec` is a 37-arm re-proof of `eval.rs`
   (the signed and rotate arms are the expensive ones — the ones phase 5
   calls "tested, not proven" in `eval.rs`). Phase 6 showed the way
   around it: **the proven encoder plus the proven simulator is an
   evaluator** (`check_query_model` is `encode` + `simulate`, and
   `encode_sound` already relates the result to `dagSim` under every
   input).

### The observation that simplifies everything

The issue's option (A) asks for "a minimal term AST in `ordeal-lrat`,
mirroring the closed `BvTerm`/`BoolTerm` fragment, encoded as a node
list with a Lean term semantics over `BitVec`". **That AST exists:** a
`DagNode` list whose variables are shared by name only — no
hash-consing, no canon — *is* the term. Its constructors are the closed
fragment one for one (the four "greater" comparisons and the five
derived operators included), `dagSim` is its semantics (defined directly
over Lean `BitVec`, SMT-LIB's meanings, phase 3), `dag_wf` its
well-formedness check (phase 4). The flattening `BoolTerm → Vec<DagNode>`
is a 37-arm 1:1 serialization (`Var` by name, `Const` to the bit table,
every operator to its constructor with the operands' indices) with no
semantic decision in it; a consumer holding the `BoolTerm` can re-run it
and compare hashes, which is exactly how it audits the `query` block
today. Call that list **D0**.

So the translation to be proven is not "term → DAG" but **D0 → D1: the
rewrite canon + hash-consing performs**, and the question is whether the
trusted side *rebuilds* D1 from D0 (a builder, options A/B) or *checks*
the D1 it is handed against D0 (a checker, option C).

### Option (A): a trusted builder from the canonical term

- **Data:** the certificate carries D0' — the term *after* canon, as the
  solver's `DagBuilder` saw it — as `ordeal-term/v1`, plus per-node reuse
  hints (`reuse[i]`: an earlier D1 node this term node may share, checked
  structurally like `compact`'s `hint_matches`; `usize::MAX` = fresh).
- **Trusted code:** `kernel::build_dag(t, tbits, reuse) -> (ns, bits,
  roots)`: variables by id through a `Vec<usize>` table (ids assigned
  densely by the untrusted flattener, `t.vars` carries the names),
  constants copied, every operator pushed or — if the hint names an
  earlier node of the same constructor and operands — reused. No
  `HashMap`: the reuse hint replaces it, as the strash hints replace
  `Aig::and`'s. Without hints the builder emits a tree-shaped DAG; that is
  still *correct*, but the raw arena is larger and the hints the solver
  computed on its own raw arena no longer apply, so the CNF differs and
  the recheck fails — so the hints are mandatory for acceptance, never
  for soundness.
- **Theorem** (`lean/TermBuild.lean`, new semantics `termSim env tbits t`
  reading `Var id w` from an environment `env : Nat → BitVec`):

  ```lean
  theorem build_dag_sound (t : Slice DagNode) (ids : Slice Usize) (tbits : Slice Bool)
      (reuse : Slice Usize) (h : kernel.build_dag t ids tbits reuse = ok (Ok q)) :
      ∀ env, ∃ inp, ∀ k (hk : k < q.roots.val.length),
        termBool env tbits.val t.val ids.val (q.roots.val[k]).val
          = dagBool inp q.bits.val q.nodes.val (q.roots.val[k]).val
  ```
  plus the converse (`∀ inp, ∃ env`), and the composition with
  `check_query_sound` / `check_query_model_sound`.
- **Leaves the trust base:** `dag.rs` (hash-consing, var sharing, the
  constant table). **Stays:** `canon.rs` entirely — ordering, mirroring
  and, above all, constant folding through `eval.rs`, which is the one
  piece that evaluates `bvsdiv`/`bvsrem`/`bvrotl` with definitions that
  are tested, not proven. That is the riskiest row of the table, and (A)
  keeps it.
- **Lean effort:** ~900–1300 lines (a second semantics `termSim`, the
  builder's loop invariant in the `dag_wf_loop_spec` style, the
  id-table/environment correspondence, the reuse check). Comparable to
  phase 4.
- **Certificate:** `ordeal-term/v1` carries the *canonical* term. A
  consumer can compare it to its own query only by running canon itself
  — the audit story is weaker than today's `query` block, not stronger.
- **Byte identity:** preserved trivially (the solver's path is untouched;
  the trusted builder runs only in the recheck), provided the reuse hints
  make it rebuild D1 exactly — which they do by construction when
  `DagBuilder` records them.

### Option (B): (A) plus canon proven

Move canon into the trusted crate and prove it semantics-preserving, so
the certificate carries the ORIGINAL term. Two of canon's three rewrites
cannot be *recomputed* there: the ordering (consequence 1 — it becomes a
per-node swap hint, verified by `BitVec.add_comm` and friends) and the
folding (consequence 3 — either the 37-arm `u128` evaluator proof, ~1500–
3000 Lean lines, or the encode-and-simulate evaluation). Once both are
hints verified by evaluation, (B)'s builder is (C)'s checker in the
harder form: it must also produce D1 *in the solver's node order*
(consequence 2), i.e. take an order hint and prove the permutation of
primary inputs. Everything (B) removes from the trust base, (C) removes
with less proof and no change to the production path. **Dominated by
(C).**

### Option (C), recommended: a proven correspondence check D0 → D1

The certificate carries the term as flattened *before* canon (D0, with
the variable names) and one untrusted index map `m : term node → D1
node`. The trusted crate checks that D1 — the DAG `check_query` /
`check_query_model` already judge — is a semantics-preserving rewrite
of D0 along `m`, with exactly the rewrites canon and the builder are
allowed to make, and the Lean proof composes with the two existing
capstones. No builder, no term AST, no new semantics, no new evaluator;
`check_query`, `check_query_model` and every theorem behind them are
untouched.

**The data (`ordeal-term/v1`, a block next to `query`):**

```json
"term": {
  "encoding": "ordeal-term/v1",
  "num_nodes": 9,
  "nodes": [["var",8],["var",8],["add",0,1],["const",0,8],["const",8,8],["mul",3,4],["ugt",2,5], ...],
  "bits": "…",
  "roots": [8],
  "vars": [["x", 8, 0], ["y", 8, 1]],
  "map": [1, 0, 2, 18446744073709551615, 18446744073709551615, 3, 4, ...],
  "sha256": "<sha256 of the canonical text>"
}
```

`nodes`/`bits`/`roots` are the `ordeal-dag/v2` spelling applied to the
flattened assertions (`term::flatten`, new, untrusted, ~80 lines: every
`Var` once per name, every `Const` occurrence its own node, operators
1:1, `Ugt` stays `ugt`). `vars` names the term's `Var` nodes. `map[i]`
is the D1 node that term node `i` became, or `usize::MAX` for a node
that became nothing (the inside of a folded constant subterm — its
children do not exist in D1 — or an unreferenced node).

**The check (`kernel::check_term_dag`, Aeneas fragment, ~300 lines):**

```rust
pub fn check_term_dag(t: &[DagNode], tbits: &[bool], troots: &[usize], map: &[usize],
                      ns: &[DagNode], bits: &[bool], roots: &[usize]) -> Result<(), TermError>
```

1. `dag_wf(t, tbits.len())` and `dag_wf(ns, bits.len())` (proven,
   reused): widths `ws0`, `ws1`. `map.len() == t.len()`.
2. `closed: Vec<bool>` over D0 in node order (`Const` closed; `Var`
   open; an operator closed iff its operands are) — `node_closed`, a
   37-arm match in the `node_wf` style.
3. `seen: Vec<bool>` over D1, for the variable map's injectivity.
4. The main loop, `i` over D0, skipping `map[i] == usize::MAX`;
   otherwise `mi = map[i] < ns.len()`, `d = ns[mi]`, `tn = t[i]`, and
   exactly one of:
   - `tn = Var(w)`: require `d = Var(w)` and `!seen[mi]`; set
     `seen[mi]`. (Two term variables aliased to one D1 variable would
     make D1 *more* constrained — an UNSAT of D1 would say nothing about
     D0. This is the one check whose omission is unsound rather than
     merely incomplete.)
   - `tn = Const(s0, w)`: require `d = Const(s1, w)` and
     `tbits[s0..s0+w] == bits[s1..s1+w]`.
   - `d = Const(s1, w)` and `tn` an operator: a **fold**; require
     `closed[i]` and `ws0[i] == w`; record `(i, s1, w)` for step 6.
   - otherwise `node_corr(tn, d, map)`: `d` is the same constructor as
     `tn` with operands `map[a]`, `map[b]` (37 arms); or, for `Add`,
     `Mul`, `And`, `Or`, `Xor`, `Eq`, `Ne`, `BoolAnd`, `BoolOr`, the
     operands swapped (9 arms); or the mirror `Ugt(a,b) ↦ Ult(map[b],
     map[a])`, `Uge ↦ Ule`, `Sgt ↦ Slt`, `Sge ↦ Sle` (4 arms). Nested
     `match`es, not tuple patterns, to stay inside what the pinned Charon
     is known to translate (`node_wf` is the template).
5. Roots: `troots.len() == roots.len()` and `map[troots[k]] == roots[k]`.
6. The folds, if any: `encode_fits(max_width(ws0), t.len())`, `nin0 =
   dag_nin(t)`, `inp0 = [false; nin0]`, `aig_new` → `encode(t, tbits,
   [])` → `simulate(inp0)`; for every recorded `(i, s1, w)` and `j < w`:
   `eval_lit(vals, words[i][j]) == bits[s1 + j]`. The proven encoder and
   simulator evaluate the closed subterm; the closedness check is what
   lets the proof drop the all-false assignment.

**The theorems (`lean/TermCheck.lean`, hand-written, namespace
`kernel.spec`):**

```lean
/-- The variable blocks agree along the map: a mapped `Var` of the term reads the same
    bits as its image. `dagNinPrefix ns i` is the input offset of node `i` (`dagNin` of
    the prefix). `NONE` is `Usize.max`. -/
def VarsAgree (t ns : List DagNode) (map : List Nat) (inp0 inp1 : List Bool) : Prop :=
  ∀ i (hi : i < t.length) w, t[i] = .Var w → map.getD i NONE ≠ NONE →
    ∀ j < w.val, inp0.getD (dagNinPrefix t i + j) false
               = inp1.getD (dagNinPrefix ns (map.getD i NONE) + j) false

/-- A closed node's value does not depend on the inputs. -/
theorem dagSim_closed_indep (ns : List DagNode) (bits : List Bool) (i : Nat)
    (hc : (dagClosed ns).getD i false = true) (inp inp' : List Bool) :
    (dagSim inp bits ns).getD i dDflt = (dagSim inp' bits ns).getD i dDflt

/-- The per-node step: a structurally corresponding node computes the same value
    from corresponding operand values (swap arms by `BitVec.add_comm` …, mirror arms
    by unfolding `dagNodeVal`). -/
theorem node_corr_spec (tn d : DagNode) (map : Slice Usize) …
    (h : kernel.node_corr tn d map = true) … :
    dagNodeVal inp0 tbits vals0 nin0 tn = dagNodeVal inp1 bits vals1 nin1 d

/-- The loop invariant, closed: every mapped term node has its image's value. -/
theorem check_term_dag_values (t : Slice DagNode) (tbits : Slice Bool) (troots map : Slice Usize)
    (ns : Slice DagNode) (bits : Slice Bool) (roots : Slice Usize)
    (h : kernel.check_term_dag t tbits troots map ns bits roots = ok (core.result.Result.Ok ()))
    (inp0 inp1 : List Bool) (hv : VarsAgree t.val ns.val (map.val.map Usize.val) inp0 inp1) :
    ∀ i (hi : i < t.val.length), (map.val[i]).val ≠ NONE →
      (dagSim inp0 tbits.val t.val).getD i dDflt
        = (dagSim inp1 bits.val ns.val).getD (map.val[i]).val dDflt

/-- Hence the roots agree. -/
theorem check_term_dag_sound … (h : … = ok (core.result.Result.Ok ())) :
    ∀ inp0 inp1, VarsAgree t.val ns.val (map.val.map Usize.val) inp0 inp1 →
      ∀ k (hk : k < troots.val.length),
        dagBool inp0 tbits.val t.val (troots.val[k]).val
          = dagBool inp1 bits.val ns.val (roots.val.getD k 0#usize).val

/-- Transport in both directions (Lean functions, not kernel code): lay the term's
    variable blocks out at their images' offsets, and read them back. Injectivity of the
    variable map (`seen`) is what makes `pushforward` well-defined. -/
def pushforward (t ns : List DagNode) (map : List Nat) (inp0 : List Bool) : List Bool
def pullback    (t ns : List DagNode) (map : List Nat) (inp1 : List Bool) : List Bool
theorem varsAgree_pushforward … : VarsAgree t ns map inp0 (pushforward t ns map inp0)
theorem varsAgree_pullback    … : VarsAgree t ns map (pullback t ns map inp1) inp1

/-- THE UNSAT CAPSTONE: the proof refutes the TERM. -/
theorem check_term_unsat_sound … (cnf) (hints steps)
    (ht : kernel.check_term_dag t tbits troots map ns bits roots = ok (core.result.Result.Ok ()))
    (hq : kernel.check_query ns bits roots hints steps = ok (core.result.Result.Ok cnf)) :
    ∀ inp0 : List Bool, ¬ (∀ k (hk : k < troots.val.length),
      dagBool inp0 tbits.val t.val (troots.val[k]).val = true)

/-- THE SAT CAPSTONE: the model satisfies the TERM, under the pulled-back inputs. -/
theorem check_term_model_sound … (inp1 : Slice Bool)
    (ht : kernel.check_term_dag t tbits troots map ns bits roots = ok (core.result.Result.Ok ()))
    (hm : kernel.check_query_model ns bits roots inp1 = ok (core.result.Result.Ok ())) :
    ∀ k (hk : k < troots.val.length),
      dagBool (pullback t.val ns.val (map.val.map Usize.val) inp1.val) tbits.val t.val
        (troots.val[k]).val = true

theorem term_verdicts_exclusive … (ht) (hq) (hm) : False
```

`check_term_unsat_sound` is `check_query_sound` (∀ inp1, ¬ roots D1)
pulled back through `varsAgree_pushforward`; `check_term_model_sound`
is `check_query_model_sound` pushed through `varsAgree_pullback`. The
fold step uses `encode_sound`'s fourth conjunct at the all-false
assignment, `simulate_spec`/`eval_lit_spec` (phase 6's pieces) and
`dagSim_closed_indep`; widths come from `dagSim_getD_fst` and the two
`dag_wf_spec` runs. All existing theorem statements stay as they are;
the four capstones are pinned in `AxiomCheck.lean`.

**Lean effort:** closedness ~150 lines; `node_corr_spec` ~450 (50 arms,
`node_wf_spec`'s 170 lines for 37 arms is the reference, plus nine
commutativity and four mirror arms); the main loop invariant ~400
(`dag_wf_loop_spec` / `check_query_model_loop_spec` style); transport
~300; folds ~150; capstones ~150. **~1600 lines, about 1.3× phase 4's
`QueryCheck.lean`**, and nothing re-proved. Rust: ~300 lines in
`kernel.rs`; `TermError` data-only like `QueryError`.

**Aeneas risks** (all have precedent in the current kernel): `usize::MAX`
as a sentinel (`check_query` compares against `core.num.Usize.MAX`);
`Vec<bool>` tables built by loops; early `return Err` inside `while`
(`dag_wf`); three parallel `Vec<usize>` for the fold records rather than
a `Vec` of tuples; `encode` with an empty root `Vec` (not a slice
literal); no `continue` — `if map[i] != NONE { … }` nesting instead. New
ground: `node_corr` matches on two enums (nested, as above) and the loop
carries two tables (`seen`, `closed`) — more loop-spec bookkeeping, not
a new kind of obligation. The one modelling question to settle in the
first regen is whether a `match` on a *second* copied scrutinee inside a
match arm translates cleanly; `node_wf`'s pattern (copy the node to a
local first) is the fallback.

**Certificate format — additive:** `format: "ordeal-cert/v3"` = the v2
envelope (same `problem`, `proof`, `query`; on `sat` the same `witness`,
`query`, `inputs`) plus the `term` block above; `recheck.min_version` the
shipping version, `cmd` naming `check_term_dag` then `check_query` /
`check_query_model`. v1 and v2 are untouched: their readers refuse a v3
bundle by `format`, exactly as v1 readers refuse v2 — a *new tag* rather
than an optional block because the v2 reader's serde structs do not
`deny_unknown_fields`, so a v2 reader handed "v2 plus a `term` block"
would silently ignore the term and report a weaker claim as the
stronger one. The v3 reader verifies all hashes, then `check_term_dag`,
then the v2 recheck. Any v2 bundle can be upgraded to v3 by a producer
that still has the term; no v3 bundle is required anywhere.

**API and CLI:** `Solver::check_with_term()` →
`TermCheckResult::{Unsat(TermCertificate), Sat(TermSatCertificate),
Unknown}`, each a wrapper `{ query: QueryCertificate | QuerySatCertificate,
term: QueryTerm }` (the phase-6 wrapping pattern; `QueryCertificate` and
`QuerySatCertificate` are not changed, so no struct literal breaks). The
solver computes D0 by `term::flatten` and `m` by `dag::term_map` (both
untrusted) and runs the trusted `check_term_dag` **before** returning a
verdict, symmetric with the two existing gates: a rejection degrades to
`Unknown` with a `debug_assert`. `ordeal check --format json
--with-term` emits v3; `--with-query` keeps emitting v2 byte for byte.

**Byte identity:** nothing on the production path changes — `canon.rs`
and `dag.rs` keep making exactly the decisions they make today, D1 and
the CNF are the same bytes, `check` / `check_with_witness` /
`check_with_query` are not touched. The trusted check only *reads* D0,
D1 and `m`. Acceptance for phase 7 is therefore the same as every phase:
the 24 fixtures and the four `cnf_gap_digest` digests unchanged.

**`dag::term_map` (untrusted, ~120 lines):** computed after the fact
from D0 and the builder's own tables, in D0's node order: for a closed
node, `eval.rs` gives the value and `DagBuilder::consts[(value, w)]` the
D1 constant (absent → `NONE`, the node was folded into a parent); for a
`Var`, `var_index[name]`; otherwise the `memo` lookup on `(op, m[a],
m[b])`, then the swapped key for the commutative ops, then the mirrored
key for the four comparisons. Canon makes one order canonical for every
occurrence, so at most one key hits. A wrong map is caught by the
trusted check and degrades the verdict to `Unknown` — never unsound —
and `denotation_guard` becomes its positive control: every one of its
1500 cases must now *also* pass `check_term_dag`.

**Cost:** one extra `encode` + `simulate` of D0 per query that has at
least one fold, on the opt-in path only. D0 is the unfolded term, so on
a query like `shl1_eq_add_64` (2234 raw gates that fold to nothing) it
is the whole circuit once more; on the bench corpus that is 1–2 ms
against SAT times in seconds. If it ever matters, the follow-up is to
extract the closed nodes into a sub-DAG first (a renumbering with a
~200-line transfer lemma); not in scope for 7b.

**What leaves the trust base:** `canon.rs` (all three rewrites, the
`eval.rs` folding included) and `dag.rs` (hash-consing, interning, the
variable map). **What stays:** `term::flatten` (1:1 serialization; a
consumer with the `BoolTerm` recomputes and compares the `term.sha256`);
the `(name, width, node)` names; the sliver; the front ends. On `sat`
the model's named values are still tied to the inputs by the untrusted
`check_consistent` — step 7d below closes that.

**Negative controls to run (each: mutate, regen, the named proof must
fail, restore):** `node_corr` accepting `Sub` with swapped operands
(`node_corr_spec`, the `Sub` arm); dropping the `seen` check
(`varsAgree_pushforward`, hence `check_term_unsat_sound`); dropping
`closed[i]` from the fold rule (`dagSim_closed_indep` no longer
applies, `check_term_dag_values`' fold case); comparing
`tbits[s0..]` against `bits[s0..]` instead of `bits[s1..]` (the `Const`
case). Bundle-level: a v3 bundle whose term says `ugt` where the DAG
says `ult(a, b)` un-mirrored, hash recomputed, CNF and proof untouched
— refused; two term variables mapped to one D1 variable — refused; a
term `add(2, 3)` mapped to a D1 `const 7` — `FoldMismatch`.

### Comparison

| | (A) trusted builder, canonical term | (B) (A) + canon proven | (C) correspondence check |
|---|---|---|---|
| leaves the trust base | `dag.rs` | `dag.rs`, `canon.rs` | `dag.rs`, `canon.rs` |
| stays trusted | `canon.rs` (incl. `eval.rs` folding), flatten, names, sliver, front ends | flatten, names, sliver, front ends | flatten, names, sliver, front ends |
| new Lean semantics | `termSim` (ids, environments) | `termSim` + evaluator or evaluation | none (`dagSim` on both sides) |
| hints from the untrusted side | reuse per node | reuse + swap + fold + order | one index per node |
| Lean effort | ~900–1300 lines | ~2500+ (evaluator) or ≈ (C) + order permutation | ~1600 lines, no existing proof touched |
| Aeneas risk | id table, reuse check | + `U128` evaluator or (C)'s | two tables in one loop; nested enum matches |
| certificate | `ordeal-term/v1` = canonical term (consumer must run canon to compare) | original term | original term + map; `ordeal-cert/v3`, v1/v2 untouched |
| default bytes | unchanged | unchanged | unchanged |
| what a consumer certifies | "the canonical term is unsat" | "the term is unsat" | "the term is unsat" |

### Recommendation and plan

**(C).** It removes both untrusted rewrites with the smallest proof,
adds no semantics and no evaluator, leaves every shipped theorem and
every production byte alone, and gives the consumer the original term
to compare against. (A) spends a comparable proof to keep the riskiest
piece trusted; (B) is (C) in a harder shape.

- **7a (this section):** design; decision requested.
- **7b (v0.31.0):** `kernel::check_term_dag` + `lean/TermCheck.lean`
  with the four capstones pinned in `AxiomCheck.lean`; the negative
  controls above; rivet: one `sw-req` ("the term-to-DAG translation is
  proven"), its design, verification and the VE record, in the phase
  4–6 pattern (`TR-062`/`TR-065`'s shape).
- **7c (same release):** `term::flatten`, `dag::term_map`,
  `QueryTerm` (canonical text + hash), `Solver::check_with_term`,
  `ordeal-cert/v3` writer/reader, `--with-term`; `denotation_guard`
  gains the trusted check as its positive control; the 24-fixture and
  digest acceptance.
- **7d (small, can follow):** on `sat`, replace the untrusted bit
  comparison in `check_consistent` with a proven
  `kernel::check_input_value(inp, offset, w, value: u128) -> bool`
  (`check_binding`'s twin at the DAG level, `U128` is already modelled
  there) plus a proven `var_offset(ns, node)` (`dagNin` of a prefix), so
  that the only untrusted step left between a named model value and the
  term is the name itself.
- **Not in #192:** the sliver and the front ends. After 7b–7d the trusted
  computing base on the query path is: the flattener (1:1), the names,
  and the pieces every phase has listed.

## Phase 7: what was delivered (TR-069)

Option (C), as designed, with one change the corpus forced (below).

### The kernel: `check_term_dag`

`crates/ordeal-lrat/src/kernel.rs` gains the entry point of the design
(`check_term_dag(t, tbits, troots, map, ns, bits, roots)`), written in
the Aeneas fragment: the two `dag_wf` runs, the map's length, then —
**before** the main loop, not only when a fold exists — the term encoded
by the proven `encode` and simulated by the proven `simulate` under the
all-false assignment, then the constant-valuedness table (`dag_const`),
the `seen` table, the main loop (`term_step` / `term_node_corr`, with the
outcome carried in an `Option` as `check_steps` does, because the pinned
Charon rejects an early return from a `match` arm inside a loop), and
the root correspondence (`roots_corr`, a flag-carrying loop: the same
Charon rejects more than two early returns from one loop body). Structural
equality of two nodes is spelled through constructor tags and three
fields (`node_tag`, `node_f1..3`, `node_eq`) rather than a nested match
on two enums, which Aeneas would expand to 37 × 37 arms; the three
rewrites are `map_node` (operands to images), `swap_comm` (nine
commutative operators) and `mirror` (the four comparison pairs).

**The change the corpus forced — "constant-valued", not "closed".** The
design's fold rule required the folded node's cone to read no variable.
The oracle corpus has `ite` terms whose *condition* is constant while
the dead branch reads a variable, and `eval.rs` — the evaluator behind
`canon.rs`'s folding — evaluates the condition first and only then the
selected branch (and `eval_bool` short-circuits `and` / `or` left to
right), so canonicalization folds such nodes. Rather than change `canon`
(which would move the shipped bytes), the trusted rule is the general
one: a node is **constant-valued** iff it is a constant, or an operator
over constant-valued operands, or an `ite` whose condition is
constant-valued *and known* through the branch the condition selects, or
an `and` (`or`) with a constant-valued, known operand that decides it.
"Known" is read off the same simulation (`cond_value`), and the rule
simply does not fire when the literal is out of range — it never guesses
a branch — which is what lets the proof avoid relying on a words-range
fact `encode_sound` does not expose. The untrusted `dag::term_map`
mirrors the rule.

**7d.** `var_offset(ns, node)` (a node's input offset, `dagNin` of the
prefix) and `check_input_value(inp, offset, w, value)` (the `w ≤ 128`
bits of `value` are the inputs at `offset`, LSB first) are the proven
model binding; `QueryInputs::check_consistent` now calls them, and the
v3 SAT re-check binds every advertised model value through the TERM's
variable map (`term.vars` → `term.map` → `var_offset` →
`check_input_value`).

### The untrusted side

`dag::flatten` is `DagBuilder::new(false)` over the un-canonicalized
assertions (no hash-consing; variables shared by name, constants
interned); `dag::term_map` computes the map after the fact from the two
DAGs alone: a variable by name, a constant by its bits — keeping every
equal-bits candidate, because the builder interns constants by their raw
`u128` value, so two input constants that agree on their low `w` bits
and differ above become two DAG nodes with identical bits, and only the
parent's structural lookup can tell which one the DAG used — an operator
by the structural key of its mapped image (as is, swapped, mirrored),
and, failing that, a constant-valued operator by the constant its value
interned to (every candidate kept, likewise). A wrong map is rejected by
the trusted check and the verdict degrades to `Unknown`; the denotation
guard of #240 runs the trusted check on all its 1500 cases as the map's
positive control, and the Z3 differential runs the corpus through
`check_with_term` (every decided query decided, none degraded).

`query::QueryTerm` (`ordeal-term/v1`: nodes, bits, roots, the `(name,
width, node)` map, the index map, a sha256 over the canonical text),
`TermCertificate` / `TermSatCertificate` with `recheck()`,
`Solver::check_with_term` (the trusted check runs before the verdict is
returned; a rejection degrades to `Unknown`), `smtlib::solve_str_with_term`,
`ordeal check --format json --with-term` (the `--with-query` output plus
the `term` block; `--with-query` is byte-identical to before), and
`ordeal-cert/v3` (the v2 envelope plus `term`, `recheck.min_version`
`0.31.0`; a new `format` tag because the v2 readers do not
`deny_unknown_fields` and would silently ignore the block; v1 and v2
readers refuse v3, the v3 readers refuse v1 and v2, by `format`).

### The theorems (`lean/TermCheck.lean`, ~2650 lines, axiom-clean)

```lean
/-- The syntactic correspondence is a semantic one. -/
theorem corr_values … (hc : TermCorr t ns tbits bits map cv) (hv : VarsAgree t ns map inp0 inp1) (i) :
    ∀ (hi : i < t.length), img map i ≠ NONE →
      (dagSim inp0 tbits t).getD i dDflt = (dagSim inp1 bits ns).getD (img map i).val dDflt

/-- A constant-valued node's value does not depend on the inputs. -/
theorem const_indep … (hcv : ∀ c b, c < t.length → cv c = some b → b = bval (…all-false value of c…)) (i) :
    ∀ (hi : i < t.length), (dagConst cv t).getD i false = true →
      ∀ inp inp', (dagSim inp tbits t).getD i dDflt = (dagSim inp' tbits t).getD i dDflt

theorem check_term_dag_sound … (h : kernel.check_term_dag t tbits troots map ns bits roots = ok (Ok ())) :
    ∀ inp0 inp1, VarsAgree t.val ns.val map.val inp0 inp1 → ∀ k (hk : k < troots.val.length),
      dagBool inp0 tbits.val t.val (troots.val[k]).val = dagBool inp1 bits.val ns.val (roots.val.getD k 0#usize).val

theorem check_term_unsat_sound … (ht : check_term_dag … = ok (Ok ()))
    (hq : kernel.check_query ns bits roots hints steps = ok (Ok cnf)) :
    ∀ inp0, ¬ (∀ k (hk : k < troots.val.length), dagBool inp0 tbits.val t.val (troots.val[k]).val = true)

theorem check_term_model_sound … (ht : …) (hm : kernel.check_query_model ns bits roots inp1 = ok (Ok ())) :
    ∃ inp0, VarsAgree t.val ns.val map.val inp0 inp1.val ∧
      ∀ k (hk : k < troots.val.length), dagBool inp0 tbits.val t.val (troots.val[k]).val = true

theorem term_verdicts_exclusive … (ht) (hq) (hm) : False

theorem check_input_value_sound (inp : Slice Bool) (offset w : Usize) (value : U128)
    (h : kernel.check_input_value inp offset w value = ok true) :
    ∀ k < w.val, inp.val.getD (offset.val + k) false = value.val.testBit k
```

`VarsAgree` is the design's: a mapped term variable reads the same bits
as its image (`dagNin` of a prefix being a node's offset); `pushforward`
(with `preimage`, the first term variable mapped to a DAG variable —
well-defined by the injectivity the `seen` table enforces) and `pullback`
are the two transports. The file follows the pattern of the earlier
phases: pure mirrors and `_eq` equations for the total helpers
(`node_tag_eq` … `node_const_eq`), `node_eq_sound` as the one 37 × 37
case split (over tags and fields, by `simp_all`), the per-rewrite value
lemmas (`pMapNode_val`, `pSwap_val` by `BitVec.add_comm` and friends,
`pMirror_val` by unfolding), the loop specs (`dag_const_loop_spec`,
`bits_eq_loop_spec`, `fold_bits_ok_loop_spec`, `roots_corr_loop_spec`,
`check_term_dag_loop2_spec` carrying `LoopFacts`: the per-node
correspondence, the `seen` characterization and `VarInj`),
`term_node_corr_spec` / `term_step_spec`, and `check_term_dag_accepted`
assembling `TermCorr`. No earlier theorem's statement changed;
`AxiomCheck.lean` pins the five new capstones. Two proof-engineering
facts worth recording: the value of a node is a `Sigma` whose first
component indexes the second, so operand facts are substituted with `rw`
(a simultaneous rewrite), never `simp`; and after a `step` the loop
obligation's conjunction is re-associated, so `and_intros` is used where
`QueryCheck.lean` could use a `def` invariant with `⟨_, _⟩`.

### Negative controls and acceptance

Recorded in VE-059 (`artifacts/verification-results.yaml`): the four
Lean controls (variable injectivity omitted, a wrong commutative swap, a
wrong mirror, an unchecked fold — each a one-line kernel mutation,
regenerated, the named proof fails, the source restored byte for byte),
the Rust potency control (the injectivity check made vacuous fails the
kernel, API, solver and bundle tests), the 24-fixture byte identity in
JSON and text mode against the `main` build, the four `cnf_gap_digest`
digests unchanged, the Z3 differential through `check_with_term`, and
the workspace test / clippy / fmt gates.

## The default path: every answer rests on the term check (v0.32.0, TR-070)

**Decision (maintainer, 2026-10-15):** replace, don't add. Phases 4–7
built the proven query and term checks beside the default pipeline and
left them opt-in (`check_with_query`, `check_with_term`). Through
v0.31.0 the entry points consumers actually call — `Solver::check`,
`check_with_limit`, `check_with_deadline`, `check_with_witness`, the
sliver one-shots, the CLI's default output — still validated the LRAT
proof against the solver's own CNF with `ordeal_lrat::check` and the
model with the untrusted `eval.rs`, so `canon.rs`, `dag.rs` and
`eval.rs` stayed on every default answer's trust path. v0.32.0 makes
the trusted gate the only gate.

### Design: one pipeline, projected

`Solver::solve_core(bound)` is the only pipeline (`solve_pipeline`,
`solve_witness` and the `query_verdict` / `check_with_term` layers on
top of them are gone): lower, search under the bound, then

- **`gate_unsat`**: `dag::flatten` + `dag::term_map` (untrusted
  advice) produce the term and the map; the trusted crate runs
  `check_term_dag` and then `check_query`, which re-encodes the DAG
  and checks the LRAT proof against the CNF *it* produced; the
  solver's CNF is checked equal to the re-encoding and carried. The
  proof is checked **once** — `ordeal_lrat::check` on the solver's CNF
  no longer runs on this path.
- **`gate_sat`**: the `eval.rs` self-check (kept as defence in depth),
  the CNF-level witness (`check_sat` / `check_binding`),
  `check_term_dag`, `check_query_model`, and `var_offset` /
  `check_input_value` for every advertised value through the term's
  own variable map.

The result is a `TermCheckResult`; `check` keeps its certificate or
model, `check_with_witness` the witness, `check_with_query` the query
block, `check_with_term` all of it. The opt-in entries therefore cost
nothing beyond `check` now. The CaDiCaL lane runs the same gate.
Anything the trusted crate rejects degrades to `Unknown` on every
entry point; the `debug_assert!`s that flag an ordeal bug in a debug
build stay, bypassed only by the test hook below.

### Negative control and potency

A gate that *ran* the term check but whose verdict did not *rest* on it
would be the vacuous-gate class. The control is a test-only hook,
`solver::tamper` (compiled out of every non-test build; the identity
in release), armed per thread: it corrupts one term-map entry (an
operator pointed at a different DAG node) or swaps the `Var` nodes of
the term's first two variables *before the trusted crate sees them*,
with the solver, the search, the proof and the model untouched. Then
`check`, `check_with_limit`, `check_with_deadline`,
`check_with_witness`, `check_with_query`, `check_with_term` and the
three sliver one-shots must all return `Unknown`, on UNSAT and on SAT
(the swapped variables only on SAT: a refutation does not read the
variable map, which is why the model is bound through it), and decide
again disarmed (`query_term_tests::default_check_rests_on_the_trusted_term_check`,
`default_sat_rests_on_the_trusted_binding`,
`sliver_one_shots_rest_on_the_trusted_term_check`). Potency: with the
term check skipped in the gate (`TermCertificate::recheck` /
`TermSatCertificate::recheck` replaced by the v2 recheck alone) those
three tests and `a_rejected_term_map_degrades_to_unknown_not_a_verdict`
fail (4 of 9); the source was restored byte for byte (VE-060).

### What the verdict scan found: a `term_map` gap, not a capacity limit

The trusted checks have capacity conditions (`encode_fits`,
`tseitin_fits`, `dag_wf`, the `w ≤ 128` of `check_input_value`), so
switching the default path could turn a decided verdict into
`Unknown`. A scratchpad harness ran every decided query of every
corpus through `check` and `check_with_term` on the v0.31.0 sources:
the latency and bmc corpora, `gen_corpus(0x192, 200)`,
`gen_corpus(0xC0FFEE, 1000)`, the sliver one-shots. No query was
refused for capacity — `encode_fits` admits `1.2·10^6` gates per node
at `w = 128` against `usize::MAX`, and nothing a solver produces comes
near it — but **four queries of `gen_corpus(0xC0FFEE, 1000)`** (140,
150 `sat`; 169, 216 `unsat`) were refused by `check_term_dag` with
`RootMismatch`. The cause was on the untrusted side: two input
constants with equal low bits are two DAG constant nodes (the builder
interns by the `u128` value), the DAG had built `mul(c, v)` over
**both**, and `term_map` committed a term constant's candidate at the
first parent key that hit — the wrong one, so the `bvnot` above it had
no image and the root did not correspond. v0.31.0's `check_with_term`
returned `Unknown` on those four; on the new default path that would
have been a verdict regression.

The fix (`dag::term_map`, untrusted): every term node keeps every
candidate image, each with the operand images its structural key used;
the map is resolved top-down — the DAG's roots (a new parameter) fix
the term roots' images, a chosen image fixes its operands' (exactly
what `term_node_corr` demands), and only a node nothing above it
reaches, the inside of a fold, takes its first candidate. The four
queries are accepted with the same certificate and model digests the
old `check` produced; the regression test
`term_map_resolves_equal_bits_constants_from_the_roots` (both
assertion orders, on an operator and on two roots) failed on the old
`term_map` and passes; the denotation guard's 1500 cases still pass
through the trusted check. The trusted crate is unchanged (no Lean
regeneration).

### Cost: the latency corpus within 1.25x

Release, Apple M4, best of three, the same corpus as
`benches/latency.rs`, `check` on the v0.31.0 sources against `check`
on this branch (the harness and the raw tables are in the VE-060
record):

| query | v0.31.0 `check` | v0.32.0 `check` | ratio | flatten + `term_map` | `check_term_dag` | `check_query` (of which LRAT) |
|---|---:|---:|---:|---:|---:|---:|
| srem_vc_32 | 4.652 ms | 5.889 ms | 1.27 | 0.108 | 0.111 | 1.343 (0.681) |
| urem_vc_32 | 4.187 ms | 5.365 ms | 1.28 | 0.094 | 0.091 | 1.253 (0.645) |
| layout_roundtrip_32 | 0.008 ms | 0.016 ms | 2.0 | 0.004 | 0.002 | 0.002 (0.000) |
| trap_vc_32 | 0.014 ms | 0.026 ms | 1.9 | 0.005 | 0.003 | 0.004 (0.002) |
| ult_cycle_64 | 3.355 ms | 3.519 ms | 1.05 | 0.009 | 0.007 | 1.111 (1.052) |
| shl1_eq_add_64 | 0.022 ms | 0.055 ms | 2.5 | 0.010 | 0.008 | 0.012 (0.000) |
| **total** | **12.238 ms** | **14.870 ms** | **1.21** | | | |

Where the time goes, on the two queries that dominate: `check_query`
is ≈ 1.3 ms, of which the LRAT check (which the old path paid too) is
≈ 0.65 ms, so the trusted re-encoding (`encode` + `compact` +
`tseitin` of the DAG inside the trusted crate) is ≈ 0.65 ms; `term_map`
(which encodes and simulates the term once to find the folded nodes)
≈ 0.1 ms; `check_term_dag` (which encodes and simulates it again, by
its proven API) ≈ 0.1 ms; the CNF comparison is below the timer's
resolution. On `ult_cycle_64` the LRAT check is the whole of
`check_query` and the gate adds 5%. The microsecond queries double:
the gate's fixed cost (three more encodes of a tiny DAG, the lookup
tables) is the same order as the solve. `check_with_term` now equals
`check` (14.80 ms against 14.87 ms) where it was 1.72x before. The
criterion bench (`cargo bench -p ordeal --bench latency`, which also
re-checks the certificate in its loop) tells the same story:
srem_vc_32 5.42 → 6.92 ms, urem_vc_32 5.10 → 6.45 ms, ult_cycle_64
4.28 → 4.42 ms, the three microsecond queries 1.8–2.7x, total ≈ 1.21x.
Seconds-long queries do not move: `hard_mul_6` (the 6-bit `a·(b+c) ≠
a·b + a·c`) 2.330 s → 2.331 s, `queue_overflow_k128` 2.540 s → 2.519 s
— the search dominates and the gate is linear in the DAG.

What would buy the rest, if ever needed: `term_map`'s own encode of the
term is only there to decide which operator nodes are constant-valued
(the fold rule); a cheaper closedness pass would save ≈ 0.1 ms on the
div queries, and the re-encoding inside `check_query` is the point of
the design and stays.

### Acceptance: the shipped bytes are unchanged

The release binary of this branch against the **published v0.31.0
aarch64-apple-darwin binary** (`gh release download v0.31.0`, verified
to print `ordeal 0.31.0`), over every query file in the repository —
`crates/ordeal/tests/fixtures` (incl. `differential/`),
`evidence/certs`, `fuzz/seeds/smtlib`,
`.rivet/repos/gale/proofs/ordeal-bv`: 29 files — in text, `--format
json` and `--format json --with-query` mode, sha256 of stdout + stderr
+ exit code: **87 same, 0 differ**. The four `cnf_gap_digest` digests
(latency `7b35d569…`, bmc `5c14a69e…`, `0x192` `a1d80de9…`, `0xC0FFEE`
`42d44115…`) are unchanged. No JSON field is added unless `--with-term`
is given.

### What stays trusted, on every path

The 1:1 flattening of the assertions into the term (`dag::flatten`: a
post-order, left-to-right walk with no semantic decision, which a
consumer holding the assertions re-runs and compares by hash), the
variable names, the sliver lowering (`sliver.rs`) and the SMT-LIB /
Verus front ends. `docs/formal-verification.md` states the same list.
