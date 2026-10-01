# Design: close the query→CNF gap — a proven re-encoder beside the checker

**Issue:** #192 · **Milestones:** v0.25.0 (phase 1), v0.26.0 (phase 2) ·
**Decision:** option (b), maintainer, 2026-10-01 · **Status:** phases 1
and 2 delivered (this document records both); phases 3–5 planned.

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

| Stage | Assurance before #192 | After phase 1 | After phase 2 |
|---|---|---|---|
| SMT-LIB / Verus front ends | tests and the Z3 differential | unchanged | unchanged |
| lowering of derived ops | tests (exhaustive at width 8) and Z3 | unchanged | unchanged |
| sliver (array/UF) | tests only | unchanged | unchanged |
| canon (including constant folding via `eval.rs`) | tests only | unchanged | unchanged |
| term walk | tests only | unchanged | unchanged (it now *calls* the proven rules, but is itself unproven) |
| blast rules | proven in Lean via the `blast_kernel.rs` mirror, plus a mirror/real differential (#202, #210) | mirror is now **gate-identical** to the shipped rules (XOR shape fixed; replay test, every op, widths 1..=16) | **the solver runs the proven rules** — `blast_kernel.rs` is the only implementation; the hand-written copies are deleted |
| bridge (reference arena → shipped arena replay) | — | — | new, unproven: ~100 lines in `blast/mod.rs`; pinned by the gate-identity tests and the byte-identity digests |
| AIG folding and hashing | tests only | tests only (benchmarked below) | tests only (now applied at replay time; same gates, same CNF) |
| Tseitin | randomised brute-force test | **proven** on the mirror (`tseitin_sat_preserving`), mirror pinned to `cnf.rs` clause for clause | unchanged |
| LRAT / SAT-witness check | proven, axiom-clean | unchanged; now composed with the encoder proof (`tseitin_refutes_outputs`) | unchanged |

The SAT path already re-checks the model against the query, via `eval.rs`.
The UNSAT path has no such check, and that is the gap.

## Phases (each shippable)

- **v0.25.0 — phase 1 (this document).** Make the model's XOR gate-identical
  to `aig::xor`. Prove Tseitin satisfiability preservation in Lean. Fix the
  stale `rotate_left` doc in `smtlib.rs`. Benchmark CNF size and time with
  no folding, folding only, and folding plus hashing.
- **v0.26.0 — phase 2 (delivered, below).** The shipped walk calls the
  proven rules directly, and the duplicate rule bodies are deleted.
  Acceptance: `cli_baseline` CNF and certificate bytes are unchanged.
- **v0.27.0.** A proven DAG walk, plus a proven folding/hashing pass after
  encoding. The proofs count nodes exactly, so folding can't go inside
  `push_and`. `encode_sound` is composed with `lrat_check_sound`.
- **v0.28.0.** Move the encoder into `ordeal-lrat` as `check_query`, with
  an `ordeal-cert/v2` `query` block. Derived ops become proven DAG
  constructs. Acceptance: flipping one constant bit in `query` fails the
  recheck even though the CNF and proof are untouched.
- **v0.29.0+.** A query-level SAT check, so `eval.rs` leaves the trust
  path; the sliver; the SMT-LIB parser stays trusted, mitigated by a round
  trip and Z3.

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

## Open risks (not yet verified)

- Aeneas/Charon at the pinned revision with a single translation unit
  holding both the kernel and the encoder (`regen.sh` translates one file
  per crate root). Phase 1 kept the encoder in `blast_kernel.rs` (the
  blaster's translation unit) and the proof file imports both generated
  models (`BlastKernel`, via `BlasterProof`, and `Kernel`, via `Sound`) —
  that works today because the two models live in separate namespaces of
  the same lake package. Moving the encoder *into* `ordeal-lrat` (phase 4)
  is where a single-unit translation is needed.
- The performance cost of going without hashing — measured above.
