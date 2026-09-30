#!/usr/bin/env python3
"""check_release_order.py — structural guard for #186 (TR-053).

Fails unless, in the release workflows:
  1. release.yml has a `gate` job that runs `rivet validate`,
     `rivet release status` and the on-main / CI-success check;
  2. every other job in release.yml depends (transitively) on `gate`;
  3. no step that signs, attests or publishes lives in `gate`;
  4. crates.io publishing is reachable only through release.yml's
     `publish-crates-io` job, which needs `create-release`
     (publish-to-crates-io.yml has no push/tag trigger).
"""
import sys

import yaml

REL = ".github/workflows/release.yml"
PUB = ".github/workflows/publish-to-crates-io.yml"
errors = []

rel = yaml.safe_load(open(REL))
jobs = rel.get("jobs", {})
gate = jobs.get("gate")
if not gate:
    errors.append("release.yml has no `gate` job")
else:
    runs = "\n".join(s.get("run", "") for s in gate.get("steps", []))
    for needle in ("rivet validate", "rivet release status", "merge-base --is-ancestor", "actions/workflows/ci.yml/runs"):
        if needle not in runs:
            errors.append(f"gate job does not run `{needle}`")
    for s in gate.get("steps", []):
        text = (s.get("run", "") + " " + s.get("uses", "")).lower()
        if any(k in text for k in ("cosign sign", "attest", "cargo publish", "gh release create", "gh release upload")):
            errors.append(f"gate job contains a publishing/signing step: {s.get('name')}")


def needs(name):
    n = jobs[name].get("needs", [])
    return [n] if isinstance(n, str) else list(n)


def reaches_gate(name, seen=()):
    if name == "gate":
        return True
    return any(reaches_gate(d, seen + (name,)) for d in needs(name) if d not in seen and d in jobs)


for name in jobs:
    if name != "gate" and not reaches_gate(name):
        errors.append(f"release.yml job `{name}` can run before `gate`")

pubjob = jobs.get("publish-crates-io")
if not pubjob or "create-release" not in needs("publish-crates-io"):
    errors.append("release.yml has no `publish-crates-io` job that needs `create-release`")
elif not str(pubjob.get("uses", "")).endswith("publish-to-crates-io.yml"):
    errors.append("`publish-crates-io` does not call publish-to-crates-io.yml")

pub = yaml.safe_load(open(PUB))
on = pub.get("on", pub.get(True, {}))  # PyYAML reads the bare key `on` as True
if "push" in on:
    errors.append("publish-to-crates-io.yml still triggers on push (publishes around the gate)")
if "workflow_call" not in on:
    errors.append("publish-to-crates-io.yml is not a reusable workflow")

for e in errors:
    print(f"FAIL  {e}")
if errors:
    sys.exit(1)
print("PASS  release order: gate -> build -> sign/attest/release -> crates.io")
