#!/usr/bin/env python3
"""Require final declarations and permit only Lean's three standard axioms."""
from pathlib import Path
import re
import sys

allowed = {"propext", "Classical.choice", "Quot.sound"}
required = {
    "RudinABC.uniformIntegerRudin_of_abcAtQuarter",
    "RudinABC.uniformIntegerRudin_of_classicalABC",
    "RudinABC.rudin_of_classicalABC",
    "RudinABC.formalConjectures_abc_implies_rudin",
    "RudinABC.abcAtQuarter_iff_realQuarter",
}
content = Path(sys.argv[1]).read_text()
found = set()
for line in content.splitlines():
    match = re.fullmatch(r"'([^']+)' depends on axioms: \[([^\]]*)\]", line)
    if match:
        name, entries = match.groups()
        found.add(name)
        bad = {s.strip() for s in entries.split(",") if s.strip()} - allowed
        if bad:
            raise SystemExit(f"{name}: unexpected axioms {sorted(bad)}")
    pure = re.fullmatch(r"'([^']+)' does not depend on any axioms", line)
    if pure:
        found.add(pure.group(1))
missing = required - found
if missing:
    raise SystemExit(f"Missing final axiom audit: {sorted(missing)}")
print(f"Checked {len(found)} declaration audits: only standard Lean axioms")
