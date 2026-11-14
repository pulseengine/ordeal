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
  - any self-hosted job in a workflow with a trigger outside TRUSTED. The
    expression trusts every event that is not `pull_request`, so a trigger a
    fork can cause under another name (pull_request_target, workflow_run,
    issue_comment, pull_request_review*, ...) would reach the runner;
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
# Triggers only a maintainer or this repository's own branches can cause,
# plus pull_request, which the expression itself sends to a hosted runner
# unless the head repository is this one.
TRUSTED = {"push", "pull_request", "schedule", "workflow_dispatch", "merge_group"}
root = pathlib.Path(__file__).resolve().parent.parent
bad, seen = {}, []
wfdir = root / ".github" / "workflows"
for wf in sorted([*wfdir.glob("*.yml"), *wfdir.glob("*.yaml")]):
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
        untrusted = sorted(str(e) for e in events - TRUSTED)
        if untrusted:
            bad[where] = f"workflow trigger(s) outside the allowlist: {', '.join(untrusted)}"
        elif isinstance(ro, list) or not FORM.match(text.strip()):
            bad[where] = "runs-on is not the fail-closed same-repo form"
for w in seen:
    print(f"FAIL  {w}: {bad[w]}" if w in bad else f"ok    {w}")
if not seen:
    sys.exit("FAIL  no self-hosted job found: this check compared nothing")
if bad:
    sys.exit(f"FAIL  {len(bad)} self-hosted job(s) a fork PR could reach")
print(f"{len(seen)} self-hosted job(s), each in the fail-closed form")
