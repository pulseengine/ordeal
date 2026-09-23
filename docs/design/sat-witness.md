# Design: an independently re-checkable SAT witness

**Issue:** #133 · **rivet:** TR-038 · **Release:** v0.20.0 (the held cut's
last open scope beside TR-032) · **Status: PROPOSED — no code lands until
this doc is reviewed** (the #48 precedent; TR-038 is explicitly
design-gated).

## The asymmetry being closed

`Unsat` is audit-grade: the bundle carries the refuted CNF + LRAT proof,
and a consumer re-establishes the verdict via the trusted checker with
zero solver trust. `Sat` is not: the bundle carries a model that ordeal
*self-checked* at solve time, and rivet deliberately flags SAT-sourced
`verifies` links (`V-ordeal-cert-sat-is-self-checked`). For the
consumers who act on SAT — "variant consistent", "counterexample exists"
— the verdict rests on solver faith.

## What "re-checkable" must mean

A consumer re-establishes, with no trust in ordeal's solve:

1. **The carried problem is satisfied** by carried data (the mathematics).
2. **The advertised model is consistent** with that data (the bindings a
   consumer actually reads are not decoration).

## Options

### O1 — full CNF assignment, checked by the trusted crate *(recommended)*

The SAT bundle carries the **complete satisfying assignment over all CNF
variables** (inputs *and* Tseitin auxiliaries) plus the input-bit map
(which CNF variable is bit *i* of model variable *v*). `ordeal-lrat` —
the already-trusted, already-Lean-modeled crate — gains one small
function:

```
check_sat(cnf, assignment, bit_map, model) -> Result<(), SatWitnessError>
```

which verifies (a) every clause has a true literal under the assignment
(a linear scan — no search, no solver), and (b) every model binding's
value equals its bits under the assignment. Both verdict directions then
re-check **against the same carried CNF via the same trusted crate**,
and the term↔CNF faithfulness gap is carried by the same evidence in
both directions (the required Lean Blaster* proofs, Kani, and the
native↔wasm differential). Fully symmetric trust story.

TCB delta: ~30 lines of evaluation in `ordeal-lrat` (no deps, no search).
It is exactly the kind of code the existing Aeneas→Lean pipeline can
absorb; a soundness statement ("check_sat accepts ⇒ the CNF is
satisfiable — by exhibition") is near-trivial and can ride a later
release as a proof extension without blocking this one.

### O2 — term-level witness (serialize the assertions, re-evaluate)

Semantically direct (no CNF detour) but it puts a **term-language
evaluator** in the trusted base — duplicating `eval.rs` inside the trust
boundary, a far larger and faster-moving surface than O1's clause scan,
and every consumer language needs its own faithful reimplementation.
Rejected: the TCB growth is the thing this feature is supposed to avoid.

### O3 — status quo plus prose

Document the boundary harder. Rejected: the boundary is already
documented and rivet already warns; #133 exists because consumers want
the warning gone, not restated.

## Format: a versioned, backward-compatible extension

SAT bundles gain a `witness` block (assignment as a packed bit string or
integer array, the bit map, and sha256 content-addressing like the unsat
payloads) and the `recheck` block starts naming the real command. The
envelope stays `ordeal-cert/v1` with `witness` OPTIONAL — old readers
(rivet 0.31+) ignore unknown fields ONLY if their parser tolerates them;
**this must be verified against rivet's actual serde behavior before
landing** (deny_unknown_fields would force a v1.1 bump and a rivet
coordination issue first — the #67-contract discipline). Either way,
rivet's `V-ordeal-cert-sat-is-self-checked` warning is retired/downgraded
only on rivet's side once it re-runs `check_sat` — a Part-2-style
follow-up in their repo, not assumed here.

## API surface (ordeal side)

`solve_pipeline` already holds the full assignment at model-decode time;
it is currently dropped after the self-check. Plan: a `cert-bundle`-gated
companion (e.g. `Model::witness()` populated only via a new
`Solver::check_with_witness()` entry, or a `SatCertificate` alongside
`Certificate`) so the default API and `Model` struct stay untouched — no
semver break, no cost on the common path. Exact spelling is review
question 3.

## Verification criteria (TR-038, to be pinned on approval)

1. For every SAT query in the differential corpus, the emitted witness
   re-checks via `ordeal_lrat::check_sat` (and the wasm build emits a
   byte-identical witness — the #135 differential extends to it).
2. Tamper rejection: a flipped assignment bit, a truncated assignment,
   and a model binding inconsistent with the assignment are each
   rejected, before any acceptance.
3. The fuzz target's oracle extends: a fuzz-found `Sat` must re-check
   through `check_sat` (the #139 pattern, now both directions).
4. rivet ingestion demonstrated against a released rivet that consumes
   the witness (the TR-030 pattern) — or the boundary honestly kept as
   a warning until rivet ships that.

## Open questions for review

1. **O1 confirmed?** (O2/O3 rejections above.)
2. **Envelope**: optional `witness` field in v1 if rivet's reader
   tolerates unknown fields, else v1.1 + rivet coordination issue first —
   accept the verification step as a hard precondition?
3. **API spelling**: `check_with_witness()` returning a `SatCertificate`,
   vs. enriching `CheckResult::Sat` behind the feature flag?
4. **Proof follow-up**: is the Lean extension of `check_sat` (soundness
   by exhibition) v0.21.0 scope, or fold into this release and hold the
   cut longer?
