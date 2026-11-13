#!/usr/bin/env python3
"""Summarise a witness MC/DC report for the ordeal-lrat checker and ratchet it.

Called by scripts/mcdc_gate.sh (issue #279). Reads witness's `mcdc-json`
(schema witness-mcdc/v3) and `run.json`, keeps only the decisions that belong
to the `ordeal-lrat` crate, and writes into OUTDIR:

  current.txt      per-file counts in the committed baseline's format
  summary.txt      the same, human readable, plus overall numbers
  gaps.txt         every ordeal-lrat decision that is not full MC/DC, with
                   its per-condition verdicts (p=proved g=gap d=dead)
  truth-table.json the ordeal-lrat decisions with their truth-table rows
                   and gap-closing hints, verbatim from witness

then compares current.txt with the baseline and exits non-zero if

  * the report is vacuous (no ordeal-lrat decisions, a checker source file
    that the baseline knows is missing, an unexpected row count, or the
    witness trace buffer overflowed), or
  * a checker source file has ZERO decisions in the table and is not in
    ZERO_DECISION_WAIVERS below (fail closed: a file no row reaches is
    named, whether or not the baseline knows it), or
  * for any checker source file the number of decisions that are not full
    MC/DC, or of uncovered conditions (gap + dead: witness turns a gap into
    "dead" when the row that exercised it disappears, so gap alone is not
    monotone), INCREASED, or the number of proved conditions FELL, against
    the baseline (a new uncovered decision raises the first two).

A decrease is reported as an improvement; the baseline is only ever updated
by hand (copy current.txt over mcdc/baseline.txt in the same commit as the
rows that earned it).
"""

import json
import os
import re
import sys

HEADER = "# file decisions not_full gap_conditions dead_conditions proved_conditions"

# Checker source files that may appear in the table with ZERO decisions,
# each with its reason. Any other file with zero decisions fails the gate:
# no row reaches it, so the table says nothing about it (#281: the printer
# `echo_kernel.rs` passed with "0 decisions" until rows called it). Printed
# on every run. Empty on purpose; an entry needs a reviewed reason.
ZERO_DECISION_WAIVERS = {}


def checker_file(path, names):
    """Map a DWARF source path to 'src/<name>.rs' of ordeal-lrat, else None."""
    m = re.search(r"(?:^|/)src/([A-Za-z0-9_]+\.rs)$", path)
    if not m or m.group(1) not in names:
        return None
    if path.startswith("src/") or "/crates/ordeal-lrat/src/" in path:
        return "src/" + m.group(1)
    return None


def load_baseline(path):
    base = {}
    with open(path) as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            f, *nums = line.split()
            base[f] = [int(n) for n in nums]
    return base


def main():
    mcdc_json, run_json, root, outdir, baseline_path, expected_rows = sys.argv[1:7]
    expected_rows = int(expected_rows)
    names = set(os.listdir(os.path.join(root, "crates", "ordeal-lrat", "src")))
    names = {n for n in names if n.endswith(".rs")}

    with open(mcdc_json) as fh:
        report = json.load(fh)
    with open(run_json) as fh:
        run = json.load(fh)

    errors = []

    if report.get("trace_health", {}).get("overflow"):
        errors.append("witness trace buffer overflowed: rows were lost, the table is not trustworthy")
    invoked = [n for n in run.get("invoked", []) if n.startswith("run_row_")]
    if len(invoked) != expected_rows:
        errors.append(f"witness invoked {len(invoked)} run_row_* exports, rows.rs defines {expected_rows}")

    stats = {n: dict(decisions=0, not_full=0, gap=0, dead=0, proved=0) for n in sorted("src/" + n for n in names)}
    kept = []
    gaps = []
    for d in report["decisions"]:
        f = checker_file(d["source_file"], names)
        if f is None:
            continue
        s = stats[f]
        s["decisions"] += 1
        if d["status"] != "full_mcdc":
            s["not_full"] += 1
        letters = ""
        for c in d["conditions"]:
            st = c["status"]
            if st == "gap":
                s["gap"] += 1
            elif st == "dead":
                s["dead"] += 1
            elif st == "proved":
                s["proved"] += 1
            letters += st[0]
        d = dict(d)
        d["source_file"] = f
        kept.append(d)
        if d["status"] != "full_mcdc":
            gaps.append((f, d["source_line"], d["status"], letters, len(d["truth_table"])))

    total = sum(s["decisions"] for s in stats.values())
    if total == 0:
        errors.append("the report holds ZERO ordeal-lrat decisions (vacuous gate)")

    # Fail closed: a checker file no row reaches is a failure by name.
    if ZERO_DECISION_WAIVERS:
        print("zero-decision waivers:")
        for f, why in sorted(ZERO_DECISION_WAIVERS.items()):
            print(f"  {f}: {why}")
    else:
        print("zero-decision waivers: none")
    for f, s in stats.items():
        if s["decisions"] == 0 and f not in ZERO_DECISION_WAIVERS:
            errors.append(f"{f}: ZERO decisions in the table: no run_row_* reaches this checker file "
                          f"(add rows to mcdc/ordeal-lrat/src/rows.rs, or a reviewed entry in ZERO_DECISION_WAIVERS)")
    for f in sorted(ZERO_DECISION_WAIVERS):
        if f not in stats:
            errors.append(f"{f}: waived for zero decisions but not a checker source file (stale waiver)")
        elif stats[f]["decisions"] > 0:
            errors.append(f"{f}: waived for zero decisions but the table has {stats[f]['decisions']} (stale waiver)")

    os.makedirs(outdir, exist_ok=True)
    cur_lines = [HEADER]
    for f, s in stats.items():
        cur_lines.append(f"{f} {s['decisions']} {s['not_full']} {s['gap']} {s['dead']} {s['proved']}")
    with open(os.path.join(outdir, "current.txt"), "w") as fh:
        fh.write("\n".join(cur_lines) + "\n")

    ov = report["overall"]
    with open(os.path.join(outdir, "summary.txt"), "w") as fh:
        fh.write(f"witness {report['witness_version']}, schema {report['schema']}, {len(invoked)} rows\n")
        fh.write(f"whole instrumented module (incl. std, libc, harness): {ov['decisions_total']} decisions, "
                 f"{ov['decisions_full_mcdc']} full MC/DC; the table below is ordeal-lrat's own files\n\n")
        fh.write(f"{'file':26} {'decisions':>9} {'not full':>9} {'gap':>6} {'dead':>6} {'proved':>7}\n")
        for f, s in stats.items():
            fh.write(f"{f:26} {s['decisions']:9} {s['not_full']:9} {s['gap']:6} {s['dead']:6} {s['proved']:7}\n")
        t = [sum(s[k] for s in stats.values()) for k in ("decisions", "not_full", "gap", "dead", "proved")]
        fh.write(f"{'TOTAL':26} {t[0]:9} {t[1]:9} {t[2]:6} {t[3]:6} {t[4]:7}\n")

    gaps.sort()
    with open(os.path.join(outdir, "gaps.txt"), "w") as fh:
        fh.write("# ordeal-lrat decisions that are not full MC/DC\n")
        fh.write("# file:line status conditions(p=proved g=gap d=dead) truth-table-rows\n")
        for g in gaps:
            fh.write(f"{g[0]}:{g[1]} {g[2]} {g[3]} {g[4]}\n")

    with open(os.path.join(outdir, "truth-table.json"), "w") as fh:
        json.dump(
            {
                "schema": report["schema"],
                "witness_version": report["witness_version"],
                "scope": "ordeal-lrat decisions only (crates/ordeal-lrat/src)",
                "rows_invoked": len(invoked),
                "decisions": kept,
            },
            fh,
        )

    base = load_baseline(baseline_path) if os.path.exists(baseline_path) else None
    if base is None:
        errors.append(f"no baseline at {baseline_path}")
    else:
        for f, s in stats.items():
            if f not in base:
                if s["decisions"] and (s["not_full"] or s["gap"]):
                    errors.append(f"{f}: new checker file with {s['not_full']} uncovered decisions / {s['gap']} gap conditions, not in baseline")
                continue
            b_dec, b_nf, b_gap, b_dead, b_proved = base[f][:5]
            unc, b_unc = s["gap"] + s["dead"], b_gap + b_dead
            if s["not_full"] > b_nf:
                errors.append(f"{f}: decisions without full MC/DC rose {b_nf} -> {s['not_full']} (decisions {b_dec} -> {s['decisions']}): a new uncovered decision")
            if unc > b_unc:
                errors.append(f"{f}: uncovered conditions (gap + dead) rose {b_unc} -> {unc} (gap {b_gap} -> {s['gap']}, dead {b_dead} -> {s['dead']})")
            if s["proved"] < b_proved:
                errors.append(f"{f}: proved conditions fell {b_proved} -> {s['proved']}")
            better = s["not_full"] < b_nf or unc < b_unc or s["proved"] > b_proved
            worse = s["not_full"] > b_nf or unc > b_unc or s["proved"] < b_proved
            if better and not worse:
                print(f"IMPROVEMENT {f}: not-full {b_nf} -> {s['not_full']}, gap+dead {b_unc} -> {unc}, "
                      f"proved {b_proved} -> {s['proved']} (update mcdc/baseline.txt deliberately from {outdir}/current.txt)")
        for f, row in base.items():
            if f not in stats and row[0] > 0:
                errors.append(f"{f}: in the baseline with {row[0]} decisions but no longer a checker source file")
            elif f in stats and row[0] > 0 and stats[f]["decisions"] == 0:
                errors.append(f"{f}: baseline has {row[0]} decisions, the report has none (vacuous for this file)")

    with open(os.path.join(outdir, "summary.txt")) as fh:
        print(fh.read())
    if errors:
        for e in errors:
            print(f"MCDC GATE FAIL: {e}", file=sys.stderr)
        sys.exit(1)
    print("MCDC GATE OK: no checker file regressed against the baseline")


if __name__ == "__main__":
    main()
