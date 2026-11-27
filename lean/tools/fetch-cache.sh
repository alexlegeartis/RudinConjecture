#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
mapfile -t modules < <(sed -n 's/^import \(Mathlib\.[[:alnum:]_.]*\)$/\1/p' RudinABC/*.lean | sort -u)
if [[ "${#modules[@]}" -eq 0 ]]; then echo "No Mathlib imports found" >&2; exit 1; fi
lake exe cache get "${modules[@]}"
