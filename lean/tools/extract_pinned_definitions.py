#!/usr/bin/env python3
"""Extract the four theorem-free definitions from the pinned DeepMind sources."""
from __future__ import annotations
import argparse
import hashlib
from pathlib import Path
import re
import urllib.request

PIN = "ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8"
PATH_PREFIX = "FormalConjectures/Wikipedia"
FILES = {
    "ABC.lean": (
        "e05d9ee80f0e05233958028176323b94341eececc0defd9449b8ddeb11dbca88",
        "ABC",
        ("def radical ",),
    ),
    "RudinsConjecture.lean": (
        "08b044e68fcfa73d98b311fd2d4dbc8a48d51bd2fb582c421aca1b915fd5c19b",
        "RudinsConjecture",
        ("noncomputable abbrev Q ", "def IsNontrivial ", "noncomputable def Qmax "),
    ),
}
HEADER = f""" /-
Copyright 2025–2026 The Formal Conjectures Authors.
The definitions below are copied verbatim under Apache-2.0 from
google-deepmind/formal-conjectures at {PIN}.
No proof stubs are included. See https://www.apache.org/licenses/LICENSE-2.0.
-/
import RudinABC.Statements
import RudinABC.ABC
""".lstrip()

def extract(raw: bytes, hints: tuple[str, ...]) -> list[str]:
    text = raw.decode("utf-8")
    found = []
    for hint in hints:
        match = re.search(r"^" + re.escape(hint) + r".*?(?=\n\n)", text, re.S | re.M)
        if match is None:
            raise ValueError(f"missing pinned declaration: {hint}")
        found.append(match.group(0))
    return found

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-dir", type=Path,
                        help="directory containing the two exact upstream .lean files (default: fetch pinned)")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", type=Path)
    args = parser.parse_args()
    sections = [HEADER.rstrip()]
    for name, (digest, namespace, hints) in FILES.items():
        if args.source_dir is None:
            url = f"https://raw.githubusercontent.com/google-deepmind/formal-conjectures/{PIN}/{PATH_PREFIX}/{name}"
            with urllib.request.urlopen(url, timeout=30) as stream:
                raw = stream.read()
        else:
            raw = (args.source_dir / name).read_bytes()
        computed = hashlib.sha256(raw).hexdigest()
        if computed != digest:
            raise ValueError(f"{name}: pin mismatch ({computed})")
        definitions = extract(raw, hints)
        sections.append(f"namespace {namespace}\n\n" + "\n\n".join(definitions) + f"\n\nend {namespace}")
    output = "\n\n".join(sections) + "\n"
    if args.check:
        if args.check.read_text() != output:
            raise ValueError(f"{args.check}: definition mismatch")
        print(f"Exact upstream definitions matched ({PIN})")
    elif args.output:
        args.output.write_text(output)
    else:
        print(output, end="")

if __name__ == "__main__":
    main()
