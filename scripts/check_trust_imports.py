#!/usr/bin/env python3
"""Require the trust audit to import every repository Lean source module."""
from pathlib import Path
import re
import subprocess
import sys

root = Path(__file__).resolve().parent.parent
excluded = {
    "TraceableAgency/Audit/TrustBoundary.lean",
    "TraceableAgency/Audit/TrustBoundaryImports.lean",
}
paths = subprocess.check_output(
    ["rg", "--files", "--hidden", "--no-ignore", "--glob", "*.lean",
     "--glob", "!.lake/**", "--glob", "!.git/**"], cwd=root, text=True
).splitlines()
expected = {p[:-5].replace("/", ".") for p in paths if p not in excluded}
source = (root / "TraceableAgency/Audit/TrustBoundaryImports.lean").read_text()
actual = re.findall(r"^import\s+([A-Za-z0-9_.]+)\s*$", source, re.MULTILINE)
missing, extra = expected - set(actual), set(actual) - expected
if missing or extra or len(actual) != len(set(actual)):
    print("ERROR: trust-audit import inventory is incomplete or stale", file=sys.stderr)
    print("Missing:", sorted(missing), file=sys.stderr)
    print("Extra:", sorted(extra), file=sys.stderr)
    sys.exit(1)
print(f"Trust-audit imports cover all {len(expected)} project source modules.")
