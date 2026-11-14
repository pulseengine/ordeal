#!/usr/bin/env python3
"""check_selfhosted_fork_guard.py — no fork PR reaches a self-hosted runner.

Every job in .github/workflows/ whose runs-on names `self-hosted` must use
exactly the fail-closed form

  ${{ (github.event_name != 'pull_request' || github.event.pull_request.head.repo.full_name == github.repository) && fromJSON('[...]') || 'ubuntu-latest' }}

so the self-hosted labels are chosen only for a non-PR event or a PR whose
head repository is this one; anything else (a fork, a deleted fork whose
head.repo is null) falls to the hosted runner. Rejected:
  - a plain self-hosted label (list or string);
  - the fail-open form `head.repo.fork && 'ubuntu-latest' || [...]`, which
    picks self-hosted whenever .fork is not true, including a null head.repo;
  - any self-hosted job in a workflow triggered by pull_request_target, where
    `event_name != 'pull_request'` is true for fork PRs;
  - no self-hosted job at all, so the check never passes having compared
    nothing (delete it if ordeal stops using self-hosted runners).
"""
import pathlib
import re
import sys

import yaml

FORM = re.compile(
    r"^\$\{\{ \(github\.event_name != 'pull_request' \|\| "
    r"github\.event\.pull_request\.head\.repo\.full_name == github\.repository\) && "
    r"fromJSON\('\[[^\]]*\"self-hosted\"[^\]]*\]'\) \|\| 'ubuntu-latest' \}\}$"
)
root = pathlib.Path(__file__).resolve().parent.parent
bad, seen = {}, []
for wf in sorted((root / ".github" / "workflows").glob("*.yml")):
    doc = yaml.safe_load(wf.read_text()) or {}
    on = doc.get(True, doc.get("on")) or {}
    events = set(on) if isinstance(on, (dict, list)) else {on}
    for job, spec in (doc.get("jobs") or {}).items():
        ro = spec.get("runs-on")
        text = " ".join(map(str, ro)) if isinstance(ro, list) else str(ro or "")
        if "self-hosted" not in text:
            continue
        where = f"{wf.name}:{job}"
        seen.append(where)
        if "pull_request_target" in events:
            bad[where] = "workflow runs on pull_request_target"
        elif isinstance(ro, list) or not FORM.match(text.strip()):
            bad[where] = "runs-on is not the fail-closed same-repo form"
for w in seen:
    print(f"FAIL  {w}: {bad[w]}" if w in bad else f"ok    {w}")
if not seen:
    sys.exit("FAIL  no self-hosted job found: this check compared nothing")
if bad:
    sys.exit(f"FAIL  {len(bad)} self-hosted job(s) a fork PR could reach")
print(f"{len(seen)} self-hosted job(s), each in the fail-closed form")
