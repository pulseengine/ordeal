#!/usr/bin/env python3
"""check_selfhosted_fork_guard.py — no fork PR reaches a self-hosted runner.

Every job in .github/workflows/ whose runs-on names `self-hosted` must
send fork pull requests to a hosted runner, with the expression
  ${{ github.event.pull_request.head.repo.fork && 'ubuntu-latest' || fromJSON('[...self-hosted...]') }}
A plain self-hosted label (list or string) fails. The check also fails
when it finds no self-hosted job at all, so it never passes having
checked nothing; delete it if ordeal stops using self-hosted runners.
"""
import pathlib
import sys

import yaml

GUARD = "github.event.pull_request.head.repo.fork && 'ubuntu-latest' ||"
root = pathlib.Path(__file__).resolve().parent.parent
bad, seen = [], []
for wf in sorted((root / ".github" / "workflows").glob("*.yml")):
    for job, spec in (yaml.safe_load(wf.read_text()) or {}).get("jobs", {}).items():
        ro = spec.get("runs-on")
        text = " ".join(ro) if isinstance(ro, list) else str(ro or "")
        if "self-hosted" not in text:
            continue
        where = f"{wf.name}:{job}"
        seen.append(where)
        if isinstance(ro, list) or GUARD not in text:
            bad.append(where)
for w in seen:
    print(f"{'FAIL' if w in bad else 'ok  '}  {w}")
if not seen:
    sys.exit("FAIL  no self-hosted job found: this check compared nothing")
if bad:
    sys.exit(f"FAIL  {len(bad)} self-hosted job(s) without the fork guard: a fork PR would run on our runners")
print(f"{len(seen)} self-hosted job(s), each with the fork guard")
