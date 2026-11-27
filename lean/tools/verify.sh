#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
if [[ "${1:-}" == --clean ]]; then lake clean rudin_abc; shift; fi
if [[ $# -ne 0 ]]; then echo "Usage: tools/verify.sh [--clean]" >&2; exit 2; fi
python3 tools/check_sources.py
lake --wfail build RudinABC
audit="$(mktemp)"
trap 'rm -f "$audit"' EXIT
lake env lean RudinABC/Audit.lean | tee "$audit"
python3 tools/check_axioms.py "$audit"
