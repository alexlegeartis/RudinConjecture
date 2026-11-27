#!/usr/bin/env python3
"""Lexical check for proof admissions, excluding Lean comments."""
from pathlib import Path
import re

def uncomment(text: str) -> str:
    out = []
    depth = 0
    i = 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif not depth and text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        else:
            ch = text[i]
            out.append(ch if not depth or ch == "\n" else " ")
            i += 1
    if depth:
        raise ValueError("Unclosed Lean comment")
    return "".join(out)

files = [Path("RudinABC.lean"), *sorted(Path("RudinABC").glob("*.lean")),
         *sorted(Path("integration").glob("*.lean"))]
forbidden = re.compile(r"\b(?:sorry|admit|sorryAx|native_decide|axiom|unsafe)\b")
for f in files:
    code = uncomment(f.read_text())
    for n, line in enumerate(code.splitlines(), 1):
        if bad := forbidden.search(line):
            raise SystemExit(f"{f}:{n}: forbidden token {bad.group(0)}")
print(f"Checked {len(files)} Lean source files: no admissions, axioms, or native_decide")
