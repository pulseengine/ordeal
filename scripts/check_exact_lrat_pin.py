#!/usr/bin/env python3
"""check_exact_lrat_pin.py — #189 guard.

ordeal's dependency on ordeal-lrat (the TRUSTED checker) must be an exact
`=X.Y.Z` requirement equal to the workspace version. With a caret
requirement a consumer's resolver can pair the solver with a different
checker patch release than the one it was released and tested with
(reproduced: ordeal =0.16.0 resolved ordeal-lrat 0.16.1).
"""
import json
import subprocess
import sys

meta = json.loads(subprocess.check_output(["cargo", "metadata", "--no-deps", "--format-version", "1"]))
pkgs = {p["name"]: p for p in meta["packages"]}
ver = pkgs["ordeal"]["version"]
deps = [d for d in pkgs["ordeal"]["dependencies"] if d["name"] == "ordeal-lrat" and d.get("kind") is None]
if not deps:
    sys.exit("FAIL  ordeal has no normal dependency on ordeal-lrat")
req = deps[0]["req"]
if req != f"={ver}":
    sys.exit(f"FAIL  ordeal -> ordeal-lrat requirement is '{req}', expected '={ver}'")
print(f"PASS  ordeal -> ordeal-lrat pinned exactly: {req}")
