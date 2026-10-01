# Design: close the query→CNF gap — a proven re-encoder beside the checker

**Issue:** #192 · **Milestone:** v0.25.0 (phase 1) · **Decision:** option
(b), maintainer, 2026-10-01 · **Status:** phase 1 delivered (this document
records it); phases 2–5 planned.

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

| Stage | Assurance today | After phase 1 |
|---|---|---|
| SMT-LIB / Verus front ends | tests and the Z3 differential | unchanged |
| lowering of derived ops | tests (exhaustive at width 8) and Z3 | unchanged |
| sliver (array/UF) | tests only | unchanged |
| canon (including constant folding via `eval.rs`) | tests only | unchanged |
| term walk | tests only | unchanged |
| blast rules | proven in Lean via the `blast_kernel.rs` mirror, plus a mirror/real differential (#202, #210) | mirror is now **gate-identical** to the shipped rules (XOR shape fixed; replay test, every op, widths 1..=16) |
| AIG folding and hashing | tests only | tests only (benchmarked below) |
| Tseitin | randomised brute-force test | **proven** on the mirror (`tseitin_sat_preserving`), mirror pinned to `cnf.rs` clause for clause |
| LRAT / SAT-witness check | proven, axiom-clean | unchanged; now composed with the encoder proof (`tseitin_refutes_outputs`) |

The SAT path already re-checks the model against the query, via `eval.rs`.
The UNSAT path has no such check, and that is the gap.

## Phases (each shippable)

- **v0.25.0 — phase 1 (this document).** Make the model's XOR gate-identical
  to `aig::xor`. Prove Tseitin satisfiability preservation in Lean. Fix the
  stale `rotate_left` doc in `smtlib.rs`. Benchmark CNF size and time with
  no folding, folding only, and folding plus hashing.
- **v0.26.0.** The shipped walk calls the proven rules directly, and the
  duplicate rule bodies are deleted. Acceptance: `cli_baseline` CNF and
  certificate bytes are unchanged.
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
`push_and_spec` (the appended node would become conditional) and is
deferred to phase 2, where the shipped walk starts calling the model's
rules and the question is settled by construction.

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
