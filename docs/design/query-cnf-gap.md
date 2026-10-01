# Design: close the query→CNF gap — a proven re-encoder beside the checker

**Issue:** #192 · **Milestones:** v0.25.0 (phases 1 and 2), v0.26.0
(phase 3), v0.27.0 (phase 4) · **Decision:** option (b), maintainer,
2026-10-01; phase 4 ships `ordeal-cert/v2` *alongside* v1 (maintainer,
2026-10-01) · **Status:** phases 1–4 delivered (this document records all
four); phase 5 planned.

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
| lowering of derived ops | tests (exhaustive at width 8) and Z3 | unchanged | unchanged | unchanged | unchanged (still lowered to the closed core *before* the DAG; the v2 bundle carries the lowered DAG) |
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
- **v0.28.0+.** A query-level SAT check, so `eval.rs` leaves the trust
  path; the sliver; derived ops as proven DAG constructs; the SMT-LIB
  parser stays trusted, mitigated by a round trip and Z3.

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
