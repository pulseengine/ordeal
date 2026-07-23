# Changelog

All notable changes to this project are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.16.0] - 2026-07-23

**The #97 regression fix + migration ergonomics** (TR-029, issues #97/#71/#57).
Anchored by a real consumer report: synth's srem trap VCs went <1 s (0.9.1) to
>240 s (0.12.0), turning a 41 s CI suite into a 6 h hang.

### Fixed
- **`bvsrem` VCs against multiplicative consumer models hung** (#97). v0.10.0
  rewired `lowering::bvsrem` through the restoring divider's remainder;
  consumers model `rem_s` multiplicatively (synth's `Sdiv+Mls`, loom's
  WASM-spec form), so every srem equivalence VC became a divider-vs-multiplier
  cross-circuit proof. Measured: UNKNOWN at a 15 s deadline → **UNSAT in
  5.3 ms** with the multiplicative form restored. `bvurem` stays native and
  `bvsdiv` multiplier-free; **TR-022's "no derivation instantiates a Mul"
  claim is partially retracted for `bvsrem`, deliberately** — the shape is now
  pinned in both directions by `div_rem_derivation_shapes_are_deliberate`,
  plus a VC-shape regression guard under a 10 s deadline.
  *Why the v0.10.0 gate missed it: exhaustive value tests drive constants
  (which never search) and the Z3 differential checks verdicts, not time.*

### Added
- **`Solver::check_with_deadline(timeout_ms)`** — wall-clock twin of
  `check_with_limit`; exhaustion is a conservative `Unknown`, checked at the
  per-conflict site so propagation-decided queries never abandon (#71a).
- **`Solver::prove_equiv_sliver(a, b)`** — one-call equivalence over extended
  terms with the sliver's congruence in force (#71b).
- **`sliver::eval_const(t)`** — ground-term evaluation that *refuses*
  interpretation-dependent terms via dual-fill detection, rather than silently
  returning the total-model fill (#71c). `SliverModel` gains `base_fill`.
- **LRAT-proof trimming** (#57 item 1): refutation-unreachable steps dropped at
  emission; certificates still checker-validated before `Unsat` returns.
  Measured honestly: 1–2% on current trace shapes (PHP(4,3) trims nothing) —
  real, safe, small; bigger wins await clause-DB churn or bulk re-checking.

### Moved (logged scope decisions)
Term-graph caching + the criterion benchmark (TR-009 remainder), and the
CaDiCaL-parity + Z3-benchmark measures → v0.17.0.

### Falsification
Wrong if: the srem VC-shape guard exceeds its 10 s deadline (the cross-circuit
regression returned); a deadline-bounded check ever returns a wrong verdict
instead of `Unknown`; `eval_const` returns a value for a base-array-dependent
read; or a trimmed certificate fails `recheck()` or exceeds its raw size.

## [0.15.0] - 2026-07-22

**P12 — the assurance capstone: Lean-verified bit-blaster** (FEAT-012 /
TR-027, issue #68). Every bit-blasting rule in the closed fragment now
carries an **unbounded Lean 4 proof** — the encoder joins the checker in the
formally-verified core, and the pipeline's soundness argument no longer leans
on Kani-bounded evidence.

### Added
- **All 27 rules proven against `BitVec` semantics for every width**, stated
  about the Aeneas-generated translation of the blaster model
  (`lean/BlastKernel.lean`, pinned Charon+Aeneas via `regen-blaster.sh`):
  bitwise, add/sub, all eight comparisons, eq/ne, ite, the four structural
  rules, the four shifts, the multiplier, and the divider. Six proof
  developments (~7,400 lines), total-correctness WP (no panic, no
  divergence), exact gate counts proven as length equalities.
- **The divider's w-bit trick is now a theorem.** The Rust comment's
  soundness argument — the shifted-out top bit alone decides the (w+1)-bit
  compare, and the w-bit modular difference is exact because `rem < divisor`
  bounds it below `2^w` — is machine-checked (`pDivGeStep_eq_decide`,
  `pDivRemStep_denotesBits`). Division-by-zero is proven precisely:
  quotient = `smtUDiv` (all-ones; core's `udiv` differs, `#eval`-confirmed),
  remainder = core `%` (already SMT-LIB-conformant).
- **`crates/ordeal/src/blast_kernel.rs`** — the Charon-translatable model,
  plus the **fidelity differential**: every one of the 65,536 width-8 input
  pairs through the real (strashed) blaster and the model, bit-for-bit,
  across every rule family.
- **CI gates the capstone like the checker**: the lean job builds all seven
  proof libraries and enforces an elaborator-based zero-`sorry` budget over
  every `Blaster*.lean`.

### The assurance chain (each link labeled with its actual strength)
```
shipped blaster =(exhaustive width-8 differential; bounded, test evidence)= model
model           =(Lean 4, ALL widths, zero sorry, three standard axioms)=  BitVec
```
The Kani harnesses remain as defense-in-depth; they are no longer the claim.

### Falsification
Wrong if: any `Blaster*.lean` theorem acquires a `sorry`/`sorryAx` (the CI
budget catches this); the fidelity differential finds any input where the
model and the shipped blaster disagree; a regenerated `BlastKernel.lean`
breaks a proof (CI `lake build`); or any proven rule disagrees with the Z3
differential on any query.

## [0.14.0] - 2026-07-21

**P11a — propositional SAT front-end** (FEAT-014 / TR-026, issue #67). The
certificate-as-evidence thesis at the Boolean level: decide a caller's CNF
through the same certified path as the bit-blaster, so a consistency verdict is
offline-re-checkable evidence rather than an internal solver's say-so.

### Added
- **`Solver::check_cnf(&CnfFormula) -> CheckResult`** — solve a propositional
  clause set directly, below the bit-blaster. On `Unsat` the LRAT proof is
  emitted from the CDCL trace and validated by `ordeal-lrat` **before** the
  verdict returns; the certificate is over **exactly** the submitted clauses, so
  a consumer re-checks against the formula it sent. On `Sat`, a self-checked
  `v1..vN` configuration. No term graph, no new solver theory, no new trusted op.

### Use case
A feature-model / variant consistency query (a mutual-exclusion or requires
conflict) becomes a certified `Unsat` a tool can re-validate — audit-grade
evidence for DO-178C / ISO-26262 / EU-AI-Act, the differentiator none of the
unchecked-Z3 or Kani/CBMC paths can deliver.

### Scope
This ships **piece 1 of three** from #67. The cross-repo pieces — the rivet
`ordeal-certificate` evidence artifact schema and the `rules_ordeal` hermetic
Bazel rule (a new repo) — are tracked separately in #91, scoped to v0.17.0.

### Corrections (premises that contact with the tracker falsified)
- #67 frames this as unblocking rivet#128. That issue is **closed** — rivet
  already ships its own constraint-propagation feature-model resolver with no
  SAT/ordeal dependency — so this is an *upgrade path* to certificate-backed
  variant verdicts, not an unblock.

### Falsification
Wrong if: `check_cnf` and the bit-blaster path disagree on a query expressible
both ways; a returned `Unsat` certificate fails `recheck()` against the
submitted clauses; or a `Sat` model fails to satisfy the formula.

## [0.13.0] - 2026-07-21

**P10 — equivalence & soundness toolkit** (FEAT-010 / TR-024, issue #66). A
public `prove_valid` primitive plus runnable consumer recipes, so a
certificate-checked equivalence/validity check lives in the toolchain instead of
being re-derived per incident.

### Added
- **`Solver::prove_valid(goal) -> CheckResult`** — prove a QF_BV predicate valid
  (assert its negation, run the certificate-checked pipeline). `Unsat(cert)` ⟹
  valid for every input and `cert.recheck()`-able; `Sat(model)` ⟹ a
  counterexample input; `Unknown` ⟹ conservative. Mirrors `prove_equiv`, which
  is now exactly `prove_valid(Eq a b)`.
- **`examples/consumer_recipes.rs`** — the recurring consumer shapes as one
  certificate-checked call each: a relay codec round-trip, a spar packed-field
  layout extract, a scry zext/trunc abstraction transfer (all proven valid,
  certificates re-checked), plus the sigil 64-bit varint-overflow and meld
  offset-fold **regression guards** (both refuted with real counterexamples).

### Changed
- The `trap` module's two gates now delegate to the public `Solver::prove_valid`
  rather than a private copy — one primitive, no duplication. No behaviour
  change (trap's suite is unchanged).

### Corrections (premises that contact with the tracker falsified)
- Issue #66 lists meld#338 as "a live silent miscompile". It was **closed
  2026-07-15** — meld fixed it — so its recipe is a *regression guard*, not a
  live catch. #66's other consumer references are loose pointers to the consumer
  *area*, not a specific obligation; the recipes are labelled accordingly.

### Falsification
Wrong if: `prove_valid(goal)` and `prove_equiv`/`check` disagree on the same
query; a recipe proven valid fails `cert.recheck()`; or a regression-guard
recipe (meld offset-fold, sigil varint overflow) stops producing a
counterexample.

## [0.12.0] - 2026-07-17

**P9 — Verus-VC bridge** (FEAT-009 / TR-023, issue #65). Discharge the
`by (bit_vector)` obligations **Verus itself emits** with a re-checkable
certificate — no hand transcription in the loop.

### Added
- **`ordeal verus <verus --log-all dir | file> [--cert-out DIR]`** — lifts each
  `by (bit_vector)` obligation out of a Verus SMT log and discharges it,
  writing one `.lrat` certificate per obligation (each re-checked by the trusted
  checker before its verdict is reported). Prelude dumps and ordinary quantified
  queries are **skipped, not failed**: only queries Verus marks
  `;; query spun off because: bitvector` are in the QF_BV fragment.
- **`ordeal::verus`** module — `extract`/`is_bitvector_query`, the slicer that
  lifts the bit-blast sub-query out of the surrounding quantified encoding.
- SMT-LIB reader: **`Bool`-sorted `declare-const`**, **`=>`** (n-ary,
  right-associative), and **boolean `=`** (`iff`, i.e. Verus's `<==>`). All
  expressed in the closed fragment — a `Bool` is a BV1 read as `= #b1`, `=>` is
  `Or(Not a, b)` — so **no new solver theory and no new trusted op**.

### Verified
Against the real toolchain: verus **0.2026.02.15.61aa1bf** (sha256-identical to
the release `rules_verus` pins — the exact binary gale verifies with) ran a full
verification of gale's crate (**1159 verified, 0 errors**), and `ordeal verus`
discharged **62 of 62** of its `by (bit_vector)` obligations — across
`fault_decode.rs` (17), `work.rs` (13), `executor.rs` (10), `userspace.rs` (7),
`event.rs` (6), `spinlock_validate.rs` (4), `atomic.rs` (3), `mpu.rs`,
`cpu_mask.rs` — converting gale's ASIL-D evidence for those leaves from
unchecked Z3 into an independently re-checkable, Lean-checker-backed certificate.

### Slicing is sound by construction
The slicer keeps a **contiguous tail** of Verus's query, so its assertions are a
subset of what Verus sent — and dropping assertions only makes UNSAT *harder*.
A sliced UNSAT therefore implies the obligation Verus posed holds; a mis-slice
can lose a proof, never fabricate one.

### Corrections (premises that contact with the code falsified)
- Issue #65's stated gap was "let-bindings + the bitvector idioms". Verus emits
  **zero** `let` and **zero** `define-fun`; the real gaps were a Bool constant
  (which rejected every VC on its first goal) and `=>`, plus boolean `=` found
  only by widening past the first lemma.
- The obligation count is **62**, not the issue's 54.

### Falsification
Wrong if: a lifted obligation disagrees with gale's hand-encoded transcription
of the same lemma; the slicer accepts a query Verus did not mark as a bitvector
spin-off; or a `*_mutant.smt2` discrimination file returns `unsat` instead of
`sat`.

## [0.11.0] - 2026-07-17

**P8 — symbolic-index linear-memory sliver** (FEAT-013 / TR-028, issue #70).
Unblocks loom's verifier migration off Z3. Pulled ahead of the Verus-VC bridge
because it blocks a real consumer today rather than a planned capability.

### Added
- **Symbolic BV32 indices for `select`/`store`** over `Array(BV32 → BV8)`.
  loom models linear memory as one global array and does multi-byte load/store
  as little-endian chains over a **symbolic** base address (a `local.get` or
  computed stack value). Previously a symbolic index returned
  `NonConcreteIndex` → `Unknown`, so **every loom function touching memory
  reverted** — memory-heavy modules would have gotten near-zero optimization
  the moment loom flipped its backend.
- **Array congruence** — `index_i = index_j → value_i = value_j` over each base
  array's access set (Ackermann over the index set). A base-array read is a
  unary uninterpreted function of its index, so reads must agree wherever their
  indices do.

### Changed
- `select(store(a,i,v), j)` now lowers to `ite(i = j, v, select(a,j))` when the
  aliasing is not statically decidable. **No new solver theory and no new
  trusted operation** — `Ite` and `Eq` were already in the closed fragment with
  proven rules, so `term.rs` is untouched.
- **The concrete fast path is preserved.** When both indices are constants the
  aliasing is settled statically: no `ite`, and no congruence clause (distinct
  constants never alias). A fully concrete query lowers to exactly its
  assertions, as before.

### Evidence
The read-over-write law under a symbolic index: `select(store(a,i,v),i) = v` is
UNSAT to refute; with `i ≠ j` the store is transparent; and **without** `i ≠ j`
the same equality stays **SAT** — so the encoding does not silently assume
non-aliasing. Congruence is **mutation-checked**: deleting it makes
`i = 5 ⇒ a[i] = a[5]` fail with the spurious model
`Sat([("$sel:a:#0",0), ("$sel:a:5",128), ("i",5)])` — i.e. `i = 5` while
`a[i] ≠ a[5]`. loom's own two-byte LE chain over a symbolic base round-trips.
Every `Unsat` runs the full certificate-checked pipeline. The Z3 differential
now draws concrete / symbolic / symbolic+offset indices and agrees with Z3's
**native array theory**, which performs neither the read-over-write elimination
nor the congruence: 165 oracle-feature tests, 0 failed.

### Falsification
Wrong if: a symbolic-index query disagrees with Z3's array theory; a model
satisfies `i = j` while `a[i] ≠ a[j]` for the same base array; a fully concrete
query gains an `Ite` or a congruence clause; or loom reports a memory-touching
function still reverting to `Unknown` for a symbolic base address.

## [0.10.0] - 2026-07-16

**P7 — layout & arithmetic completeness** (FEAT-008 / TR-021 + TR-022). The
foundation the consumer research named: byte-layout primitives for the wire-codec
and ABI-equivalence consumers, plus a multiplier-free div/rem family.

### Added
- **`crates/ordeal/src/layout.rs`** — `to_le_bytes` / `from_le_bytes`, pure
  `extract`/`concat` compositions over the closed fragment (no new operations).
  Byte 0 is least-significant. Paired with `prove_equiv` these turn "does this
  codec round-trip?" (relay#265) and "does this record encode that layout?"
  (spar#327) into one certificate-checked query.
- **`bvurem` is now a native fragment op** (`BvTerm::Urem`) with a proven blast
  rule (`blast_udivrem` exposes the remainder the restoring-division circuit
  already computes) and Kani harnesses at 8/32/64.

### Changed
- **The div/rem family is multiplier-free.** `lowering::bvurem` was
  `a - (a udiv b) * b` and `lowering::bvsrem` was `a - bvsdiv(a,b) * b` — each
  instantiated a multiplier. `bvsrem` is now a sign correction over the native
  `bvurem` (`(|a| urem |b| ^ sa) - sa`); `bvsdiv` was already multiplier-free.
  Verified structurally: no derivation contains a `Mul` node.
- Width **16** is now exercised by the oracle matrix (relay CCSDS/CRC-16, kiln
  `extend8/16_s`).

### Fixed
- **`trap_div(DivOp::RemS)` wrongly demanded a trap on `INT_MIN / -1`** (#72).
  Per WASM Core §4.4.1 only `idiv_s` traps on the overflow pair (its quotient
  `2^(N-1)` is unrepresentable); `irem_s(INT_MIN, -1)` is **defined and returns
  0**. The clause was gated on "is the op signed", which swept in `RemS` — so the
  library rejected **correct** `rem_s` lowerings and would have blessed
  spuriously-trapping ones. Found by synth's derived-ARM-trap gate (synth#166)
  with counterexample `dividend=0x80000000, divisor=0xFFFFFFFF`; synth's pinned
  workaround can now be dropped.
  - **Why it hid:** both sides of a trap-equivalence VC used this same builder,
    and ordeal's own test reused the implementation's `is_signed()` predicate —
    consistent wrongness is invisible to a consistency gate. The test is now
    grounded in **result definability** per the spec (computed in `i128`),
    independent of `trap_div`'s internals, and a mutation check confirms it fails
    if the bug is reintroduced.
- Z3-bridge (`oracle.rs`) coverage for the native `bvurem`, so the differential
  corpus generates and cross-checks it against Z3's operator.

### Corrections (premises that contact with the code falsified)
- `bvsdiv`/`bvsrem`/`bvurem` were **not** missing — they already existed as
  derived lowerings. The gap was **cost** (a multiplier), not capability. So this
  release promotes exactly **one** op to the trusted fragment, not three.
- Width 16 was **not** unsupported — the engine is width-parametric
  (`check_width` admits 1..=128); it was merely untested.

### Evidence
Exhaustive width-8 (all 65536 pairs): native `bvurem` vs the evaluator, and the
derived `bvurem`/`bvsdiv`/`bvsrem` vs an independent **Z3-free** SMT-LIB
reference — every sign combination, `INT_MIN/-1`, and every divide-/
remainder-by-zero case. Plus width 16/32/64, the le-bytes round-trip proven with
a `recheck()`-able certificate, and a byte-swapped reassembly caught as `Sat`
(the oracle is not vacuous).

### Falsification
Wrong if: a div/rem derivation disagrees with the SMT-LIB reference for any
input, a `Mul` node reappears in one of them, or the `le-bytes` round-trip fails
to prove for some width.

## [0.9.1] - 2026-07-11

**Phase B — float→int truncation trap classifier** (TR-020, issue #59). Completes
the trap library: the trap condition for `iN.trunc_fM_s/u` — NaN, ±∞, and
out-of-target-range — expressed as a QF_BV predicate over the **float's bits**,
so a consumer gates trunc trap-preservation with no new solver theory.

### Added — `crates/ordeal/src/trap.rs`
- `FpFmt` (F32/F64), `IntTarget` (I32/I64), and classifiers `fp_is_nan`,
  `fp_is_inf`, `fp_trunc_out_of_range`, and `trap_trunc` — the out-of-range check
  uses the IEEE **monotonic bit-order** (magnitude compares against derived
  `2^k` threshold bit-patterns, with the WASM sign asymmetry: `x == 2^(N-1)`
  traps but `x == -2^(N-1)` converts).

### Boundary (held)
No floating-point in the solver, no new operations — the float enters only as a
`BvTerm` bitvector, classified with `Extract`/`Eq`/`Ne`/`Uge`/`And`/`Or`/`Not`.
FP-value arithmetic equivalence (QF_FP) remains out of the fragment by design.

### Proof
Each classifier is verified by eval-equivalence against the **real Rust float**
WASM trunc trap predicate (range math in exact f64). **f32→i32 (signed and
unsigned) is EXHAUSTIVE** over all 2³² bit patterns; the other six
source×target×signedness variants use a structured exponent×mantissa sweep + a
±64-ULP boundary sweep; every synth#709 boundary case is an explicit assertion.
Independently clean-room-verified (own exhaustive re-run + independent threshold
constants). Consumer: synth trunc gate (#709 regression-lock).

### Falsification
Wrong if `trap_trunc(bits)` disagrees with `iN.trunc_fM_s/u`'s real-float trap
predicate for any bit pattern.

## [0.9.0] - 2026-07-11

**P6 (Phase A) — WASM trap/partiality semantics** (FEAT-007 / TR-019, issue #59).
A shared library that expresses each partial WASM op's **trap condition** as a
QF_BV predicate over its operand bits, so a verifier can prove **trap**-equivalence
— not just value-equivalence — and catch a transformation that *drops a trap*
(the root cause of loom#273/#274/#278 and synth#633/#666/#665/#642). Both
consumers adopt it: loom (loom#279) and synth's `translation_validator`
(VCR-VER-002).

### Added — `crates/ordeal/src/trap.rs`
- **Trap-condition builders** (each a `BoolTerm` over operand bits):
  - `trap_div` — ÷0 (all four div/rem) + `INT_MIN/-1` signed overflow.
  - `trap_always` — `unreachable`.
  - `trap_mem_oob(addr, size, mem_bound)` — OOB with a **caller-supplied symbolic
    `mem_bound`**, wraparound-safe.
  - `trap_call_indirect` — `bounds ∨ null-slot ∨ type`, where the type clause is
    `TypeTrap::Runtime` (runtime `Ne`) or `StaticallyDischarged` (closed-world
    tables, contributes `false`).
  - `trap_any` — Or-fold for block-local composition.
- **`DefineOrTrap`** `(value, may_trap)` wrapper and two VC helpers:
  - `trap_equivalence_vc` / `prove_trap_equivalence` — full
    `(trap ⇔ trap) ∧ (¬trap ⇒ value_eq)`.
  - `trap_condition_equivalence` / `prove_trap_condition_equivalence` — the
    **trap clause alone**, for consumers (synth memory ops) that model no op
    value; still catches a dropped bounds/null check.

### Boundary (held)
ordeal **classifies bits** — it adds **no operations** and does **no
floating-point arithmetic**. Trap-equivalence VCs are decided by the normal
certificate-checked pipeline, so `Unsat` is LRAT-validated and `recheck()`-able.
Phase B (float→int `trunc` classifier, proven against synth's #709 IEEE table)
and FP-value equivalence (QF_FP, out of the QF_BV fragment by design) are
separate.

### Falsification
Wrong if: a `trap_condition` builder ever disagrees with the WASM trap predicate
for some input (`eval` mismatch), or the VC reports a trap-dropping lowering as
`Unsat` (or a trap-preserving one as `Sat`).

## [0.8.0] - 2026-07-11

**P5 (core) — canonicalization + const-folding above the AIG** (FEAT-005 /
TR-018, issue #35). Closes a concrete, measured solver cliff by making
semantically-equal-but-structurally-different terms share an AIG node before
blasting — an untrusted preprocessing pass, so soundness is untouched.

### Added
- `crates/ordeal/src/canon.rs`: a semantics-preserving canonicalization pass
  run on every assertion before bit-blasting. It (1) orders the operands of
  commutative operators (`add`/`mul`/`and`/`or`/`xor`, `eq`/`ne`), (2) mirrors
  the "greater" comparisons to their "less" twins, and (3) constant-folds
  all-constant subterms. So `mul(a,b)` and `mul(b,a)` reduce to the **same**
  term → the same node via structural hashing.
- Kill criterion met: **synth's A5 shape** `Ne(Mul(a,b), Mul(b,a))` @ 32 now
  decides **UNSAT with a re-checkable certificate essentially instantly** (was:
  did not finish in 590 s). It is now decided by root propagation at any conflict
  budget — the v0.4.0 `check_with_limit` stopgap is no longer needed for it.

### Soundness (unchanged)
The rewrites are on the **untrusted side**: every `Unsat` is still validated by
`ordeal-lrat`, and every `Sat` model is re-evaluated against the **original**
assertions. A wrong rewrite could only make the solver slower or `Unknown`,
never unsound. Each rule is proven semantics-preserving under `eval` (the
reference) by `eval(canonicalize(t)) == eval(t)` sweeps in `canon.rs`.

### Deferred (tracked as #57)
LRAT-proof trimming, cross-pass incremental term-graph caching, and a full
criterion benchmark harness vs Z3 — none on the soundness path.

### Falsification
This release is wrong if: canonicalization ever changes a verdict — i.e. for
some query `check` disagrees with the pre-canonicalization pipeline or with the
Z3 differential, or `eval(canonicalize(t)) ≠ eval(t)` for some assignment.

## [0.7.0] - 2026-07-11

**P3 (ordeal side) — portable, independently re-checkable certificate + consumer
integration surface** (FEAT-003 / TR-017). Turns an UNSAT verdict from something
a consumer *trusts ordeal about* into a proof object a consumer *re-checks
itself* — the primitive a certifying translation validator (synth) needs, and
an adoption path for a solver-trusting rule verifier (loom).

### Added
- `Certificate` now carries the refuted DIMACS CNF (`cert.cnf`) alongside the
  LRAT proof (`cert.lrat`), and exposes **`Certificate::recheck()`** — re-runs
  the formally-verified `ordeal-lrat` checker over the `(cnf, lrat)` pair, so a
  consumer re-establishes UNSAT with **zero trust in the untrusted solver**.
  `lrat_text()` and the `CertificateError` type are public and re-exported.
- `crates/ordeal/examples/translation_validation.rs`: a runnable worked example
  mirroring synth's WASM→ARM translation-validation use case — proves correct
  lowerings (each certificate re-checked) and catches a buggy
  `i32.mul(x,3) ⇒ LSL x,#1` with a counterexample.
- `docs/consuming-ordeal.md`: new "Translation validation (synth)" section; the
  soundness contract now documents the actionable `cert.recheck()` path.

### Changed
- The `Certificate` doc's promise — "callers can independently re-check" — is
  now **true through the public API** (previously the CNF was discarded, so
  `ordeal_lrat::check` was uncallable by a consumer). No behavioural change to
  verdicts; the pipeline threads the already-computed CNF out to the caller.

### Falsification
This release is wrong if: a consumer holding an `Unsat(cert)` finds
`cert.recheck()` returns `Ok(())` for a `(cnf, lrat)` pair the standalone
`ordeal-lrat` checker rejects (or vice-versa) — i.e. the in-crate re-check and
an external LRAT checker ever disagree on the carried certificate.

### Scope (honest)
Cross-repo *adoption* is not claimed here and is owned by the consumers:
synth-verify already runs on ordeal with Z3 as a differential oracle
(synth#553); the portable-certificate upgrade is proposed on synth#667; loom
still verifies rules directly with Z3 and is invited to adopt on loom#277.

## [0.6.0] - 2026-07-11

**P4 — Kani proofs of bit-blaster correctness** (FEAT-004). Machine-checked
proofs that each bit-blasting rule equals the concrete reference semantics
(SMT-LIB QF_BV, mirroring `eval::eval_bv`/`eval_bool`) for **all** inputs — the
Z3-independent soundness evidence for the blaster.

### Added
- `crates/ordeal/src/blast/proofs.rs`: **79 Kani harnesses** — every operation
  (`add`/`sub`/`mul`/`udiv`/`and`/`or`/`xor`/`shl`/`lshr`/`ashr`/`rotr`, all 10
  comparisons, `concat`/`extract`/`zext`/`sext`/`ite`) at widths 8/32/64. Each
  asserts `word_value(blast) == r_op(inputs)` over symbolic input bits; Kani
  proves it for every assignment. Validated: every op family verifies
  `SUCCESSFUL` at width 8 (incl. the signed comparisons, sign-extend, extract).
- `.github/workflows/kani.yml`: nightly / on-demand Kani job (non-blocking)
  running the fast tier (every rule at width 8 + the structural rules).

### Changed
- `Aig`'s structural-hash cache is a **no-op under `cfg(kani)`** — the default
  `RandomState` hasher seeds from the OS RNG, which Kani cannot model. The
  un-deduped AIG simulates identically, so the proof covers the deduped
  production AIG. Production build is byte-for-byte unchanged (101 lib tests
  pass).

### Scope (honest)
The light ops (arithmetic, bitwise, shift, rotate, comparison, structural) are
Kani-tractable at 8/32/64. **64-bit `mul`/`udiv` are a compute frontier** — a
bit-blasted 64-bit multiplier is a huge SAT instance — and retain the
exhaustive-width-8 test + the Z3 differential oracle. So this release adds
proof-based soundness for the tractable majority of the op set; fully removing
Z3 awaits a tractable proof strategy for wide multiply/divide.

**Falsification statement:** this release is wrong if any enabled Kani harness
fails, or if a `r_*` reference diverges from `eval::eval_bv`/`eval_bool`.

## [0.5.1] - 2026-07-10

Soundness **drift-hardening**. No runtime code or API change — this release
strengthens the link between the v0.5.0 Lean proof and the shipped Rust.

- **Drift gap closed (verified).** Confirmed with the real Charon+Aeneas toolchain
  that the committed `lean/Kernel.lean` is **byte-identical** to the current Aeneas
  translation of `crates/ordeal-lrat/src/kernel.rs`. So `lrat_check_sound` is
  verified against the *actual shipped code*, not a stale model — closing the one
  residual gap called out in `docs/formal-verification.md`.
- **Model-drift guard operational** (#44). The `kernel-model-drift` CI workflow now
  runs on every PR (required-safe), passes in seconds when the model/kernel/regen
  script are unchanged, and on relevant changes regenerates via a cached
  Charon+Aeneas toolchain and fails on any diff. Advisory pending a warm-cache run
  before promotion to a required branch-protection check.
- Fixed a Rust 1.97 `clippy::unused_format_specs` lint (test-message format width)
  that was failing CI on the new stable toolchain.

**Falsification statement:** this release is wrong if a change to `kernel.rs` can
land on `main` with a stale `lean/Kernel.lean` and a green build once the drift
guard is a required check.

## [0.5.0] - 2026-07-08

The LRAT/RUP **checking algorithm** `kernel::check_steps` is now machine-checked
**sound** in Lean 4: if it accepts a certificate's steps against a CNF, that CNF
is unsatisfiable (`∀ σ, ¬ cnfHolds σ cnf`), proved with **zero `sorry`** over the
**Aeneas-generated** model of the Rust source (`crates/ordeal-lrat/src/kernel.rs`).
This closes issue #12 (TR-013). `#print axioms kernel.spec.lrat_check_sound`
reports **only** `propext` / `Classical.choice` / `Quot.sound` — no `sorryAx`,
no `native_decide` (axiom-clean, like the core `pure_check_sound`).

Scope and trust are stated precisely in
[docs/formal-verification.md](docs/formal-verification.md): the proof is over the
Aeneas translation (Charon+Aeneas trusted), soundness only (not completeness),
under the benign side condition `|cnf| + |steps| ≤ usize::MAX`. Certificate/DIMACS
parsing, I/O, the wasm harness and the (untrusted) solver are out of scope. No
Rust code changed; this release marks the trust-boundary milestone: the solver
stays untrusted, and the now-proven checker is trusted.

**Falsification statement:** this release is wrong if
`kernel.spec.lrat_check_sound` is found to depend on `sorryAx` (or any axiom
beyond `propext` / `Classical.choice` / `Quot.sound`), if `unsat` is not the
standard "no assignment satisfies", or if the committed `lean/Kernel.lean` does
not match `regen.sh`'s output on the shipped `kernel.rs`.

### Added
- `docs/formal-verification.md` — the precise "what is proven / what is trusted"
  trust-boundary statement.
- `kernel-model-drift` CI workflow (advisory) — re-runs `regen.sh` and fails on
  `lean/Kernel.lean` drift from the shipped `kernel.rs` (issue #44).

### Changed
- `ordeal-lrat`'s `check_steps` soundness is now machine-checked (Lean 4 /
  Aeneas); the Lean CI job is blocking and asserts a zero-`sorry` budget.

## [0.4.2] - 2026-07-03

spar's integration question (issue #38): a semantic oracle for its generated
WIT record data-type layouts — small, closed QF_BV equivalence queries, in
ordeal's existing fragment. This adds a one-call equivalence helper and a
worked example; no new fragment op, no optimization/LP surface. **Falsification
statement:** this release is wrong if `Solver::prove_equiv(a, b)` returns a
verdict that disagrees with asserting `BoolTerm::Ne(a, b)` and calling
`Solver::check` on the same terms.

### Added

- **`Solver::prove_equiv(a, b)`** — prove two same-width bitvector terms
  equivalent via the standard equivalence-as-UNSAT encoding. `Unsat` (with a
  checker-validated LRAT certificate) ⟹ equal for all inputs; `Sat` ⟹ a
  counterexample; `Unknown` (including a width mismatch) ⟹ conservative, no
  claim. Decision-only — it does not grow an optimization/LP arm.
- **`docs/consuming-ordeal.md`** — a layout/data-type equivalence section
  (pack+extract round-trip) showing the programmatic `BvTerm` graph + verdict.

## [0.4.1] - 2026-07-03

loom's v0.4.0 smoke-test (issue #34). loom asked for a text front-end so it
can drive ordeal without hand-building `BvTerm`s, and flagged that the README
still described a phase-0 skeleton. This patch ships both. **Falsification
statement:** this release is wrong if `ordeal check` returns a verdict for an
SMT-LIB2 query that disagrees with the equivalent `Solver` API call on the
same query, or if any construct inside the documented QF_BV subset is rejected
as `unsupported`.

### Added

- **SMT-LIB2 front-end — `ordeal check <file.smt2>`** (or `-`/stdin). A small
  hand-written s-expression reader (`ordeal::smtlib`, pure `std`, no new deps)
  over the QF_BV subset loom/synth emit: `declare-const`/`declare-fun`,
  `assert`, `check-sat`, `get-model`/`get-value`. Prints `sat` (+ SMT-LIB
  model), `unsat` (+ checker-validated LRAT byte count), or `unknown`. Every
  op routes through the existing closed core or `ordeal::lowering`; nothing new
  enters the fragment. Any out-of-subset construct → `unsupported: <what>`,
  exit 2. The reader lives in the library (unit-testable, wasip2-clean); the
  binary owns I/O, model formatting, and exit codes.

### Fixed

- **README staleness (loom #34)** — the status line described a "phase-0
  skeleton" returning `Unknown` for every query; corrected to the live v0.4.x
  engine and the new `check` subcommand documented in the quickstart.

## [0.4.0] - 2026-07-03

synth's burn-in asks (issue #29). Their v0.3.0 report — 34 real wasm≡arm
equivalence queries, **0 wrong verdicts, faster than Z3 on 33/34** —
identified the exact gaps blocking adoption behind synth-verify's solver
interface. This release closes asks 1–3. **Falsification statement:** this
release is wrong if `BvTerm::Ite`, any `ordeal::lowering` derived op, or any
`check_with_limit`-decided verdict disagrees with Z3 on the same query, or
if `check_with_limit` ever returns a verdict other than `Unknown` on budget
exhaustion.

### Added

- **`BvTerm::Ite(cond, then, else)`** — the bool→BV bridge (synth used `ite`
  49×). A native op with a proven bit-blasting rule (per-bit AIG mux on the
  condition literal), so it joins the closed fragment legitimately. Verified
  exhaustively at width 8 and across the Z3 differential corpus.
- **`ordeal::lowering`** — blessed derived-op constructors over the closed
  core for the ops synth emits but the fragment omits: `bvnot`, `bvneg`,
  `bvrotl`, `bvurem`, `bvsdiv`, `bvsrem`. No new blast rules (the checker
  still gates every `Unsat`); each form verified against Z3 including
  division-by-zero and `INT_MIN`/`-1` edges.
- **`Solver::check_with_limit(max_conflicts)`** — a resource-bounded check
  returning `Unknown` on budget exhaustion, preserving the conservative
  soundness contract. Makes hard shapes (synth's A5 mul-commutativity,
  previously DNF > 590 s) CI-survivable.

### Notes for consumers

- Depend on `ordeal = "0.4.0"`. `Unknown` stays conservative; only a
  certificate-checked `Unsat` authorizes a transformation.
- synth-verify's full query mix is now expressible with Z3 retained only as
  a differential oracle.

## [0.3.0] - 2026-07-02

The array/UF sliver — loom/synth can now try ordeal on their full query
mix, not just pure QF_BV. **Falsification statement:** this release is
wrong if any in-sliver query (array select/store over concrete offsets, or
uninterpreted `pure_call`) lowered by `Solver::check_sliver` yields a
verdict that disagrees with Z3's array/UF theories on the same query, or a
`Sat` model that does not re-evaluate to true.

### Added

- **`Solver::check_sliver`** — one-shot decision for extended (array/UF)
  queries. The sliver is eliminated into the closed QF_BV core and decided
  by the normal certificate-checked pipeline; out-of-sliver queries return
  `Unknown` (conservative). Soundness is unchanged — no array/UF construct
  reaches the bit-blaster; only the lowered core does.
- **`sliver` module** — the extended term language (`ArrayTerm`,
  `ExtBvTerm`, `ExtBoolTerm`) and `lower()`: eager read-over-write for
  `Array(BV32→BV8)` select/store over concrete offsets, and Ackermannization
  for uninterpreted `pure_call` congruence. Verified against Z3's array and
  UF theories across a 550-query differential corpus (zero disagreements).

### Notes for consumers (loom / synth)

- Depend on `ordeal = "0.3.0"`; `ordeal-lrat` is pulled transitively.
- Requires a Rust toolchain supporting **edition 2024** (rustc ≥ 1.85).
- Treat `Unknown` conservatively (never optimize / accept on it). Only a
  `CheckResult::Unsat` (which carries a checker-validated LRAT certificate)
  authorizes a transformation.
- Please file trials as issues on `pulseengine/ordeal` — see
  `docs/consuming-ordeal.md`.

## [0.2.0] - 2026-07-02

First public release: the QF_BV decision pipeline, oracle-verified and
certificate-checked. **Falsification statement:** this release is wrong if
any well-sorted query over the closed fragment yields a `Sat` model that
does not re-evaluate to true, an `Unsat` whose carried LRAT certificate the
`ordeal-lrat` checker rejects on re-check, or any verdict disagreeing with
Z3 on the same query.

### Added

- Verification evidence layer: `verification-execution` / `verification-verdict`
  artifacts pin each measure's executed result to CI runs (the right side of
  the V is now evidence, not plan). 47 artifacts advanced to `verified`;
  `rivet release status v0.1.0` reports **cuttable**. New CI job
  `Reproducible build` (VER-003): dependency-free assert + bit-identical
  double build. VER-004 (loom/synth call-site conformance) moved to v0.4.0
  and VER-008 (CaDiCaL parity) to v0.6.0 as logged scope decisions.

- **P2 certificate path: `Unsat` is now checker-validated.**
  - `lrat.rs` — LRAT emission from the CDCL proof trace (pure formatting of
    the RUP-ordered antecedent chains; strictly sequential ids in exactly
    the `ordeal-lrat` dialect).
  - `Solver::check` returns `CheckResult::Unsat(Certificate)` **only after
    the `ordeal-lrat` checker accepts the emitted certificate**; a rejected
    certificate degrades to `Unknown`. The certificate bytes carried in
    `Certificate::lrat` are the validated ones, re-checkable by callers.
  - Emission verified on directed UNSAT cases, PHP(4,3), and a random
    UNSAT 3-SAT corpus; mutation cases still rejected.
  - The remaining P2 obligation — the checker's formal soundness proof
    (Rust → Lean 4 via Aeneas, TR-013) — is scaffolded in `lean/README.md`
    and tracked as issue #12; until it discharges, trust rests on the
    small, dependency-free, mutation-tested Rust checker.

- **P1 engine: the full QF_BV decision pipeline** (blast → AIG → Tseitin CNF
  → own pure-Rust CDCL core → self-checked models), oracle-verified:
  - `eval.rs` — total concrete evaluator (executable SMT-LIB semantics), the
    test oracle for every blasting rule and the SAT-model self-check.
  - `aig.rs` — AIGER-convention And-Inverter Graph arena with constant
    folding and structural hashing.
  - `blast/` — per-op-family blasting rules (bitwise/eq, add/sub/comparisons,
    barrel shifts/rotate, mul/restoring-udiv, structural), each verified
    exhaustively at width 8 (65 536 operand pairs) and randomized at 32/64
    against the evaluator.
  - `cnf.rs` — Tseitin encoder (linear size), equisatisfiability-tested.
  - `sat.rs` — dependency-free CDCL (two-watched literals, first-UIP
    learning, VSIDS + phase saving, Luby restarts), deterministic and
    wasm-clean, with a proof trace whose antecedents form RUP chains so P2
    LRAT emission is a formatting step.
  - `solver.rs` — pipeline dispatcher with the op-enablement kill-criterion
    gate; `Sat` models are re-evaluated before being returned; engine-UNSAT
    is reported as `Unknown` until the P2 verified checker lands (no
    unchecked `Unsat`, ever). `Solver::validate` gives distinct
    well-sortedness errors.
  - `ordeal-lrat` — new zero-dependency crate: the RUP-only textual LRAT
    checker (the future sole trusted component), mutation-tested.
  - `oracle.rs` — real Z3 differential oracle (`z3` crate, optional,
    native-only, behind `oracle`): fragment translation, seeded corpus
    generator, and the differential harness. **Milestone: ordeal's raw
    verdicts agree with Z3 across the 300-query corpus (both SAT and UNSAT
    exercised, zero disagreements).**

### Changed

- Rivet release management adopted (requires rivet ≥ 0.23):
  - Phase artifacts renamed `FEAT-P0`…`FEAT-P5` → `FEAT-000`…`FEAT-005` so
    they are valid commit-trailer references (`Implements: FEAT-001`).
  - 33 artifacts scoped to releases via the `release:` field — v0.1.0 = P0
    (skeleton), v0.2.0 = P1, v0.3.0 = P2, v0.4.0 = P3, v0.5.0 = P4,
    v0.6.0 = P5. `rivet release status <version>` is the cuttability
    burn-down.

- Rivet artifact graph reconciled with the architecture decisions:
  - `FEAT-P0`…`FEAT-P5` now mirror ROADMAP.md's phase breakdown one-to-one
    (P0 skeleton, P1 bit-blaster + own SAT core, P2 LRAT + verified checker,
    P3 sliver + integration, P4 drop Z3 from soundness + op-by-op proofs,
    P5 performance); the rivet artifacts are the source of truth and
    ROADMAP.md is the human-readable mirror.
  - `TR-004`, `TR-011`, `ARC-005`, `ARC-008`, `VER-003`, `VER-008`, `VER-013`
    updated from the abandoned "CaDiCaL primary / varisat wasm fallback" plan
    to the decided backend story: ordeal's own pure-Rust CDCL core is primary
    on every target; CaDiCaL is an optional cfg-gated native accelerator;
    varisat is a reference only.
  - `FEAT-P0` marked `implemented` (the phase-0 skeleton is done and CI-gated).
  - Added the schema-authorable inverse links (`allocated-to`) so the
    requirement→architecture allocation is bidirectional.
- ROADMAP.md phase P4 now lists op-by-op bit-blaster verification explicitly.

### Added

- Initial project scaffold (phase-0 skeleton).
  - Cargo workspace with the `ordeal` crate (library + binary).
  - `term.rs`: the closed QF_BV fragment from loom issue #246 — `BvTerm`,
    `BoolTerm`, and `Sort` covering widths 8/32/64. The array/UF sliver is
    present only as a documented `TODO`.
  - `solver.rs`: one-shot `check-sat` interface (`Solver`, `CheckResult`,
    `Certificate`, `Model`). `check` conservatively returns `Unknown` — sound
    by construction — until the bit-blaster + SAT engine + verified LRAT
    checker land.
  - `oracle.rs`: Z3 differential-oracle stub behind the off-by-default `oracle`
    feature. The default build has zero external dependencies.
  - Minimal CLI printing the version and roadmap status notice.
  - Documentation: README, ARCHITECTURE, ROADMAP, AGENTS, CLAUDE.

[Unreleased]: https://github.com/pulseengine/ordeal/compare/v0.4.2...HEAD
[0.4.2]: https://github.com/pulseengine/ordeal/releases/tag/v0.4.2
[0.4.1]: https://github.com/pulseengine/ordeal/releases/tag/v0.4.1
[0.4.0]: https://github.com/pulseengine/ordeal/releases/tag/v0.4.0
[0.3.0]: https://github.com/pulseengine/ordeal/releases/tag/v0.3.0
[0.2.0]: https://github.com/pulseengine/ordeal/releases/tag/v0.2.0
