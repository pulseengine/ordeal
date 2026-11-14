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
MATRIX_REF = re.compile(r"^\$\{\{\s*(fromJSON\()?matrix\.[A-Za-z0-9_-]+\)?\s*\}\}$")
# Triggers only a maintainer or this repository's own branches can cause,
# plus pull_request, which the expression itself sends to a hosted runner
# unless the head repository is this one.
TRUSTED = {"push", "pull_request", "schedule", "workflow_dispatch", "merge_group"}


def _strings(node, path=()):
    """Yield (path, text) for every string scalar, skipping job steps."""
    if isinstance(node, dict):
        for k, v in node.items():
            if len(path) == 2 and path[0] == "jobs" and k == "steps":
                continue  # steps cannot pick the runner; outputs are caught below
            yield from _strings(v, path + (k,))
    elif isinstance(node, list):
        for i, v in enumerate(node):
            yield from _strings(v, path + (i,))
    elif isinstance(node, str):
        yield path, node


def check(wfdir):
    """Return (seen, bad). Every string mentioning `self-hosted` outside a
    step's `run` script must be a job's own runs-on in the accepted form: a
    self-hosted label in strategy.matrix, an input default, env or anywhere
    else fails closed, because the check cannot follow how it reaches
    runs-on. (A label in a repository variable, `vars.X`, is invisible to any
    file check.)"""
    bad, seen = {}, []
    for wf in sorted([*wfdir.glob("*.yml"), *wfdir.glob("*.yaml")]):
        doc = yaml.safe_load(wf.read_text()) or {}
        on = doc.get(True, doc.get("on")) or {}
        events = set(on) if isinstance(on, (dict, list)) else {on}
        untrusted = sorted(str(e) for e in events - TRUSTED)
        for path, text in _strings({k: v for k, v in doc.items() if k is not True and k != "on"} | {"on": on}):
            if "self-hosted" not in text:
                continue
            is_runs_on = len(path) >= 3 and path[0] == "jobs" and path[2] == "runs-on"
            where = f"{wf.name}:{path[1]}" if is_runs_on else f"{wf.name}:{'.'.join(map(str, path))}"
            if where in seen:
                continue
            seen.append(where)
            ro = doc["jobs"][path[1]]["runs-on"] if is_runs_on else None
            if not is_runs_on:
                bad[where] = "self-hosted label outside a job's runs-on (matrix, input, env, ...): not checkable"
            elif untrusted:
                bad[where] = f"workflow trigger(s) outside the allowlist: {', '.join(untrusted)}"
            elif isinstance(ro, list) or not FORM.match(str(ro).strip()):
                bad[where] = "runs-on is not the fail-closed same-repo form"
        # A runner computed at run time (needs outputs, inputs, vars, github)
        # cannot be checked from the file: only the accepted form or a plain
        # matrix reference (whose values the walk above checks) may be an
        # expression.
        for job, spec in (doc.get("jobs") or {}).items():
            ro = spec.get("runs-on")
            text = str(ro or "")
            if "${{" not in text or FORM.match(text.strip()) or MATRIX_REF.match(text.strip()):
                continue
            where = f"{wf.name}:{job}"
            if where not in seen:
                seen.append(where)
            bad[where] = "runs-on is computed at run time; only the fail-closed form or matrix.* is checkable"
    return seen, bad


GOOD = ("${{ (github.event_name != 'pull_request' || "
        "github.event.pull_request.head.repo.full_name == github.repository) && "
        "fromJSON('[\"self-hosted\",\"linux\",\"x64\",\"light\"]') || 'ubuntu-latest' }}")
FAIL_OPEN = ("${{ github.event.pull_request.head.repo.fork && 'ubuntu-latest' || "
             "fromJSON('[\"self-hosted\",\"linux\",\"x64\",\"light\"]') }}")


def self_test():
    """Each rule in both directions over planted workflows: a rule seen only
    to pass is indistinguishable from one that cannot fail."""
    import tempfile

    def wf(on, runs_on):
        return yaml.safe_dump({"on": on, "jobs": {"a": {"runs-on": runs_on, "steps": []}}})

    cases = [
        # (name, filename, workflow text, expect failure)
        ("good form, every trusted trigger -> holds", "x.yml",
         wf(["push", "pull_request", "schedule", "workflow_dispatch", "merge_group"], GOOD), False),
        ("good form in a .yaml file -> holds", "x.yaml", wf(["push"], GOOD), False),
        ("plain label list -> fails", "x.yml", wf(["push"], ["self-hosted", "linux", "x64", "light"]), True),
        ("plain label string -> fails", "x.yml", wf(["push"], "self-hosted"), True),
        ("fail-open fork form -> fails", "x.yml", wf(["push", "pull_request"], FAIL_OPEN), True),
        ("unguarded job in a .yaml file -> fails", "x.yaml", wf(["push"], ["self-hosted"]), True),
        ("no self-hosted job -> fails", "x.yml", wf(["push"], "ubuntu-latest"), True),
        ("self-hosted runner from strategy.matrix -> fails", "x.yml", yaml.safe_dump({
            "on": ["push", "pull_request"],
            "jobs": {"a": {"strategy": {"matrix": {"runner": ['["self-hosted","linux"]', '"ubuntu-latest"']}},
                           "runs-on": "${{ fromJSON(matrix.runner) }}", "steps": []}}}), True),
        ("self-hosted label in an input default -> fails", "x.yml", yaml.safe_dump({
            "on": {"workflow_dispatch": {"inputs": {"r": {"default": "self-hosted"}}}},
            "jobs": {"a": {"runs-on": "${{ inputs.r }}", "steps": []}}}), True),
        ("runner from a needs output -> fails", "x.yml", yaml.safe_dump({
            "on": ["push"],
            "jobs": {"pick": {"runs-on": "ubuntu-latest", "steps": [{"run": "echo r=x >> $GITHUB_OUTPUT"}]},
                     "a": {"needs": "pick", "runs-on": "${{ needs.pick.outputs.r }}", "steps": []},
                     "b": {"runs-on": GOOD, "steps": []}}}), True),
        ("hosted matrix runner beside a good self-hosted job -> holds", "x.yml", yaml.safe_dump({
            "on": ["push"],
            "jobs": {"m": {"strategy": {"matrix": {"os": ["ubuntu-latest", "macos-latest"]}},
                           "runs-on": "${{ matrix.os }}", "steps": []},
                     "b": {"runs-on": GOOD, "steps": [{"name": "mentions self-hosted"}]}}}), False),
        ("self-hosted only inside a step script -> no job to check, fails as empty", "x.yml", yaml.safe_dump({
            "on": ["push"],
            "jobs": {"a": {"runs-on": "ubuntu-latest", "steps": [{"run": "echo self-hosted"}]}}}), True),
    ] + [
        (f"good form under {t} -> fails", "x.yml", wf(["push", t], GOOD), True)
        for t in ("pull_request_target", "workflow_run", "issue_comment",
                  "pull_request_review", "workflow_call")
    ]
    bad_cases = 0
    print("check_selfhosted_fork_guard self-test")
    for name, fname, text, expect_fail in cases:
        with tempfile.TemporaryDirectory() as d:
            wfdir = pathlib.Path(d)
            (wfdir / fname).write_text(text)
            seen, bad = check(wfdir)
            failed = bool(bad) or not seen
        ok = failed == expect_fail
        bad_cases += not ok
        print(f"  [{'ok  ' if ok else 'FAIL'}] {name}")
    print(f"  {len(cases) - bad_cases}/{len(cases)} cases hold")
    return 1 if bad_cases else 0


def main():
    if "--self-test" in sys.argv:
        sys.exit(self_test())
    root = pathlib.Path(__file__).resolve().parent.parent
    seen, bad = check(root / ".github" / "workflows")
    for w in seen:
        print(f"FAIL  {w}: {bad[w]}" if w in bad else f"ok    {w}")
    if not seen:
        sys.exit("FAIL  no self-hosted job found: this check compared nothing")
    if bad:
        sys.exit(f"FAIL  {len(bad)} self-hosted job(s) a fork PR could reach")
    print(f"{len(seen)} self-hosted job(s), each in the fail-closed form")


if __name__ == "__main__":
    main()
