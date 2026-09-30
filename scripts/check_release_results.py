#!/usr/bin/env python3
"""check_release_results.py <version> <mapped-junit.xml> — #203 release gate.

The mapped JUnit comes from the tagged commit's own CI run on main
(scripts/junit_to_rivet.py over cargo-nextest's JUnit). Fails unless:
  1. no mapped result is a failure or error;
  2. every measure in the release scope whose steps run a default-features
     `cargo test` has at least one CI result and all of them pass, unless
     it is listed in scripts/junit_to_rivet.skip.
So a release's test evidence comes from the run on the tagged commit, not
from a hand-written verdict.
"""
import json
import subprocess
import sys
import xml.etree.ElementTree as ET  # input is our own CI's nextest output
from pathlib import Path

MEASURES = {"sw-verification", "unit-verification", "sw-integration-verification"}

version, xml_path = sys.argv[1], sys.argv[2]
root = Path(__file__).resolve().parent.parent

results = {}
for tc in ET.parse(xml_path).getroot().iter("testcase"):
    aid = tc.get("classname")
    ok = not any(c.tag in ("failure", "error") for c in tc)
    results.setdefault(aid, []).append((tc.get("name"), ok))

skipped_ids = set()
skip_file = root / "scripts" / "junit_to_rivet.skip"
if skip_file.exists():
    for line in skip_file.read_text().splitlines():
        parts = line.split("#", 1)[0].split()
        if len(parts) == 2:
            skipped_ids.add(parts[1])

errors = []
for aid, rs in sorted(results.items()):
    for name, ok in rs:
        if not ok:
            errors.append(f"{aid}: CI result FAILED: {name}")

scope = json.loads(subprocess.check_output(
    ["rivet", "list", "--release", version, "--format", "json", "--full"],
    cwd=root, stderr=subprocess.DEVNULL))
arts = scope.get("artifacts", scope) if isinstance(scope, dict) else scope
checked = 0
for a in arts:
    if a.get("type") not in MEASURES:
        continue
    steps = str((a.get("fields") or {}).get("steps", ""))
    if "cargo test" not in steps or a["id"] in skipped_ids:
        continue
    checked += 1
    rs = results.get(a["id"], [])
    if not rs:
        errors.append(f"{a['id']}: in {version} scope, cites cargo test, but has no CI result "
                      f"(add `// rivet: verifies {a['id']}` to the tests it runs)")
    elif all(ok for _, ok in rs):
        print(f"ok    {a['id']}: {len(rs)} CI result(s), all pass")

for e in errors:
    print(f"FAIL  {e}")
print(f"{version}: {checked} in-scope measure(s) checked against CI results")
sys.exit(1 if errors else 0)
