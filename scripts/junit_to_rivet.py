#!/usr/bin/env python3
"""junit_to_rivet.py — map nextest JUnit results onto rivet measures (#203).

Usage: junit_to_rivet.py <nextest-junit.xml> <out.xml>

Test functions declare what they verify with a line comment:

    // rivet: verifies VER-050        (directly above a test fn, or its
    #[test]                             #[test]/doc lines)
    fn check_cnf_sat_gate_...() {}

A marker whose next code line is not a `fn` (for example at the top of a
file) covers every test in that file.

The output is JUnit XML with one <testcase> per (test, artifact) pair and
`classname` set to the artifact ID. `rivet import-results --format junit`
then records a result for that artifact. Unmarked tests are left out: they
still gate CI through cargo, but they are not evidence for any measure.

Fails (exit 1) if a marker in src/ or tests/ matches no test case: a marker
that points at nothing would be vacuous evidence, which is the #187 class.
Markers in examples/ and benches/ are not tests and are not mapped.
Markers listed in scripts/junit_to_rivet.skip (file + ID, each with the
reason and the job that runs them instead) are reported as SKIP.
"""
import re
import sys
import xml.etree.ElementTree as ET
from pathlib import Path

MARK = re.compile(r"^\s*//\s*rivet:\s*verifies\s+([A-Z][A-Z0-9]*-\d+)")
FN = re.compile(r"^\s*(?:pub(?:\([^)]*\))?\s+)?(?:async\s+)?fn\s+([A-Za-z_][A-Za-z0-9_]*)")
SKIP = re.compile(r"^\s*(#\[|///|//!|//|$)")


def markers(root: Path):
    """Yield (suite, module_prefix, fn_name_or_None, artifact_id, where)."""
    for crate in sorted((root / "crates").iterdir()):
        name = crate.name
        for sub in ("src", "tests"):
            base = crate / sub
            if not base.is_dir():
                continue
            for f in sorted(base.rglob("*.rs")):
                rel = f.relative_to(base).with_suffix("")
                if sub == "tests":
                    suite, prefix = f"{name}::{rel.parts[0]}", ""
                else:
                    parts = [p for p in rel.parts if p not in ("lib", "main")]
                    if parts and parts[-1] == "mod":
                        parts = parts[:-1]
                    suite, prefix = name, "::".join(parts)
                lines = f.read_text().splitlines()
                for i, line in enumerate(lines):
                    m = MARK.match(line)
                    if not m:
                        continue
                    fn = None
                    for nxt in lines[i + 1 : i + 15]:
                        if MARK.match(nxt) or SKIP.match(nxt):
                            continue
                        fm = FN.match(nxt)
                        fn = fm.group(1) if fm else None
                        break
                    yield suite, prefix, fn, m.group(1), f"{f.relative_to(root)}:{i + 1}"


def main():
    src, out = sys.argv[1], sys.argv[2]
    root = Path(__file__).resolve().parent.parent
    tree = ET.parse(src)
    cases = []  # (suite, testcase element)
    for suite in tree.getroot().iter("testsuite"):
        for tc in suite.iter("testcase"):
            cases.append((suite.get("name"), tc))

    out_root = ET.Element("testsuites", tree.getroot().attrib)
    out_suite = ET.SubElement(out_root, "testsuite", {"name": "rivet-measures",
                                                      "timestamp": tree.getroot().get("timestamp", "")})
    skips = set()
    skip_file = root / "scripts" / "junit_to_rivet.skip"
    if skip_file.exists():
        for line in skip_file.read_text().splitlines():
            parts = line.split("#", 1)[0].split()
            if len(parts) == 2:
                skips.add((parts[0], parts[1]))
    dead, mapped = [], 0
    for suite, prefix, fn, aid, where in markers(root):
        if (where.rsplit(":", 1)[0], aid) in skips:
            print(f"SKIP  {where}: `verifies {aid}` (listed in junit_to_rivet.skip)")
            continue
        hits = []
        for sname, tc in cases:
            n = tc.get("name", "")
            if sname != suite:
                continue
            if prefix and not (n == prefix or n.startswith(prefix + "::")):
                continue
            if fn and not (n == fn or n.endswith("::" + fn)):
                continue
            hits.append(tc)
        if not hits:
            dead.append(f"{where}: `verifies {aid}` ({fn or 'whole file'}) matched no test case")
            continue
        for tc in hits:
            new = ET.SubElement(out_suite, "testcase", dict(tc.attrib))
            new.set("classname", aid)
            new.set("name", f"{tc.get('name')} [{aid}]")
            for child in tc:
                new.append(child)
            mapped += 1
    out_suite.set("tests", str(mapped))
    ET.ElementTree(out_root).write(out, encoding="utf-8", xml_declaration=True)
    print(f"mapped {mapped} (test, artifact) results")
    for d in dead:
        print(f"FAIL  {d}")
    sys.exit(1 if dead else 0)


if __name__ == "__main__":
    main()
