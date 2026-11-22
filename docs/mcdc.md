# MC/DC evidence for the trusted checker (`ordeal-lrat`)

Issue #279 (rivet TR-077). This is **confidence evidence**, not a behaviour
change and not a claim: nothing in `crates/` changed, and no README or
`claims.yaml` statement rests on it. It answers one question: *which of the
checker's own decisions do the accept and reject vectors we have actually
exercise independently?*

## What is measured

[`witness`](https://github.com/pulseengine/witness) (0.46.0, from the pinned
varve layer) instruments a `wasm32-wasip1` build of the row harness
`mcdc/ordeal-lrat/`, invokes every no-arg `run_row_*` export, and reconstructs
the MC/DC truth table of every decision in the module from rustc's DWARF. The
harness is a standalone crate (its own `[workspace]`, a path dependency on
`crates/ordeal-lrat`, not a member of the root workspace, so root `cargo`
commands never build it). Each row is one tiny driver that feeds one accept or
reject vector to a public checker entry point:

| entry points driven | source file(s) they reach |
| --- | --- |
| `check`, `kernel::check_steps` (text parser, RUP kernel) | `lib.rs`, `kernel.rs` |
| `check_sat`, `check_binding` | `kernel.rs` |
| `dag_wf`, `dag_nin`, `check_query`, `check_query_model` | `kernel.rs`, `blast_kernel.rs` |
| `check_term_dag`, `var_offset`, `check_input_value` | `kernel.rs` |
| `check_sliver_lowering`, `ext_wf` | `sliver_kernel.rs` |
| `flatten_tree`, `project_core`, `check_tree_model[_ext]` | `term_kernel.rs` |
| every DAG operator through `check_query` (all widths that matter: 1, 3, 4, 5) | `blast_kernel.rs` |

Rows return 1 iff the checker gave the verdict the row's name claims; a native
`cargo test --manifest-path mcdc/ordeal-lrat/Cargo.toml` pins that, so a row
cannot silently stop exercising what it says. Under `witness` only the
decisions a row reaches count.

## Run it locally

```
scripts/mcdc_gate.sh                 # ~4 min; output in target/mcdc-ordeal-lrat/
```

Needs the `wasm32-wasip1` rust target and witness (`$WITNESS`, else
`varve which witness`). The output directory holds `rollup.txt` (witness's
per-file rollup), `truth-table.json` (every ordeal-lrat decision with its
truth-table rows and gap-closing hints, verbatim from witness's `mcdc-json`),
`gaps.txt` (decisions that are not full MC/DC), `summary.txt` and
`current.txt`. CI runs the same script in `.github/workflows/mcdc.yml` and
uploads that directory as the artifact `mcdc-ordeal-lrat`.

## The ratchet

`mcdc/baseline.txt` holds, per checker source file, the number of decisions,
of decisions that are *not* full MC/DC, of gap conditions, dead conditions
and proved conditions. The gate fails (non-zero, naming the file) when, for
any `crates/ordeal-lrat/src/*.rs` file:

- the number of not-full decisions rises, or the number of uncovered
  conditions (gap + dead; witness turns a gap into "dead" when the row that
  exercised it disappears, so gap alone is not monotone) rises, or the number
  of proved conditions falls (a new uncovered decision does at least one of
  these), or
- the report is vacuous: zero ordeal-lrat decisions, a file the baseline knows
  has none, a different number of invoked rows than `rows.rs` defines, or a
  witness trace-buffer overflow (rows would be lost silently), or
- a checker source file has zero decisions in the table and is not in
  `ZERO_DECISION_WAIVERS` (`scripts/mcdc_report.py`; empty, and printed on
  every run). This fails closed for a file the baseline does not know yet:
  the printer `echo_kernel.rs` (#281) was reported as `0 decisions` and
  "MCDC GATE OK" until its rows were added, because no row called it.

A decrease prints an `IMPROVEMENT` note. The baseline is updated **by hand**
(copy `current.txt` over `mcdc/baseline.txt` in the commit that adds the
rows), never by the script. The baseline is tied to witness 0.46.0 and rustc
1.100.0 (the CI job pins both); a toolchain bump can move the numbers and is
re-baselined deliberately. The move from 1.99.1 to 1.100.0 (2026-11-21) left
every per-file count unchanged. The move from witness 0.45.0 to 0.46.0
(2026-11-22, with the covalent layer) moved 3 `term_kernel.rs` conditions
from proved to gap (proved 68 -> 65, gap 144 -> 147) and nothing else:
0.45.0 reported a short-circuit decision's unobserved last operand as proved
(witness#352), and 0.46.0 reports those decisions (lines 342, 866) as
`no_witness` instead. The lower count is the honest one. The job is not a required check, same stance as
`varve-pin`.

Negative controls, run when this landed: removing the 15 sliver call-site
rows from the harness turned the gate red naming `src/sliver_kernel.rs`, and
adding `if assignment.len() > 1000 && cnf.len() == 7 { return Err(..) }` to
`check_sat` in a scratch copy of the crate (`MCDC_ROOT` points the gate at a
scratch tree; `crates/` is never edited) turned it red naming `src/kernel.rs`
(the new branch joined an existing decision: not-full count unchanged, uncovered
conditions +3, proved conditions -3).

## Numbers

Rows: 359 (286 when the gate landed; 58 for the printer `echo_kernel.rs`,
#281, whose line is new, and which moved a few conditions of `kernel.rs` and
`sliver_kernel.rs`; 15 for the mux fold, #314, see below). Before (the 5-row spike, same summariser; its `src/lib.rs` row also
contains the spike harness's own decisions, so treat that line as an upper
bound): `kernel.rs` 17 decisions / 0 full / 23 gap conditions, `lib.rs` 8 / 0 /
15, the other three files not reached at all. After:

| file | decisions | not full MC/DC | gap conds | dead conds | proved conds |
| --- | ---: | ---: | ---: | ---: | ---: |
| `src/blast_kernel.rs` | 67 | 66 | 246 | 74 | 61 |
| `src/echo_kernel.rs` | 72 | 69 | 631 | 356 | 234 |
| `src/kernel.rs` | 101 | 91 | 370 | 461 | 175 |
| `src/lib.rs` | 9 | 6 | 15 | 2 | 16 |
| `src/sliver_kernel.rs` | 46 | 42 | 171 | 29 | 38 |
| `src/term_kernel.rs` | 39 | 35 | 144 | 5 | 68 |

The `blast_kernel.rs` line was re-baselined with the mux fold (#314,
TR-096; it was 62 / 61 / 233 / 72 / 54). The fold is new trusted code, so
the gate went red on it by design: `mux_fold` adds four decisions and
`compact_and`'s tail became a function of its own (`compact_gate`), five
decisions more in all. The 15 new rows call `mux_fold` directly on a
hand-built arena — both hits (shared operand stored first, stored second)
and one miss per source-level condition (an operand not negated, out of
range, a constant, an input; no shared operand; a shared operand whose
partners are not complements, on either side) — and drive `compact` with
the fold requested on every gate, so it is taken once and declined
elsewhere. Proved conditions rose by 7; witness reports the two `match`
decisions as `pppd` (the dead condition is the index bounds check behind
the explicit range test) and the others as `no_witness`, as it does for
61 of the 62 decisions the file had before.

(`rollup.txt` uses witness's own per-file attribution and counts a few more
or fewer decisions per file; the gate counts from `mcdc-json`, folding the
relative and absolute DWARF paths of one file together.)

## The gap rows that remain, and why

Most remaining gap rows are not missing vectors. Reading `gaps.txt` and the
`gap_closure` hints in `truth-table.json`:

- **Loop-shaped decisions.** The checker is written in the Aeneas fragment, so
  everything is `while i < n { … if … { return … } … }`. witness folds a loop
  with several early exits into one decision whose outcome is the same in
  almost every row (for example `lib.rs` `parse_deletion` / `parse_addition`:
  the `loop { let Some(token) = … ; if *token == "0" { break } … }` shape, all
  conditions are "gap", and in the truth tables of those decisions the outcome is
  the same in nearly every row, so no pair of rows can show a condition
  independently flipping it). Adding rows did not move these in this session.
- **Compiler-inserted conditions.** Indexing bounds checks (`clause[i]`,
  `words[a]`) and the overflow checks the crate turns on (#225) are branches
  to a panic that valid inputs, and the checker's own earlier validation, make
  unreachable. They show up as *dead* conditions (461 in `kernel.rs`) and as
  gap conditions inside the same decision. Reaching them would mean panicking
  the checker, which is the opposite of what a row should do.
- **Derived code.** `#[derive(PartialEq, Debug, Clone)]` on the error and node
  enums (`kernel.rs:80`, `kernel.rs:605`, `blast_kernel.rs:948`, …) is
  decisions-per-variant that the harness only touches through `==` on a few
  variants.
- **Defensive branches.** `TooLarge` capacity guards need `usize::MAX`-scale
  inputs (`encode_fits` / `tseitin_fits` are driven directly at their edges;
  `check_query` gets one oversized-variable row); the
  `lift` fallback `lines.get(step).unwrap_or(0)` and `InvalidStepLiteral`
  through the text parser are unreachable from `check` by design (the parser
  rejects those literals first), which is why `kernel::check_steps` has its
  own rows.

What this means: the table is a **lower bound on independence evidence and an
honest inventory of untested conditions**, with the ratchet making sure that
inventory cannot grow unnoticed. It is not a statement that the checker is
MC/DC-covered; the soundness argument is the Lean proof of the Aeneas model
(`docs/formal-verification.md`), not this table. Closing or waiving individual
gap rows in rivet is left to the maintainer (TR-077).
