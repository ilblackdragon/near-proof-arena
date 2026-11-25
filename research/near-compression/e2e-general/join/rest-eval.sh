#!/usr/bin/env bash
# E2E-M14 (lane E): evaluate the state commitment of T1's engine cuts (`RestEval.lean`).
#   rest-eval.sh CASE_DIR IN_JSON OUT_JSON
# IN_JSON: {"keys": [hex …] (lane B's leaf order), "ws": {"c1": hex, …} (optional)}.
# One file = the imports, then `StViewE.lean`, `StateW.lean`, `RestI.lean`, `RestEval.lean` (their
# import lines dropped), run with `lake env lean --run` in lane B's package (`m5a/lean`, built).
# Prints the axioms lines of the appended files; exit 1 on an elaboration error.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
PKG=${M5A_PKG:-$HERE/../m5a/lean}
T=${TMPDIR:-/tmp}/RestEval.$$.lean
{ { echo "import StateM5a.StNone"; echo "import NearSpecV3.E2E.ViewSer"; echo "import Lean.Data.Json"
    grep -h '^import ' "$HERE/StViewE.lean" "$HERE/StateW.lean"; } | sort -u
  for f in StViewE StateW RestI RestEval; do grep -hv '^import ' "$HERE/$f.lean"; done; } > "$T"
out=$(cd "$PKG" && lake env lean --run "$T" "$(realpath "$1")" "$(realpath "$2")" "$(realpath -m "$3")" 2>&1) || rc=$?
rm -f "$T"
echo "$out" | grep -E "RestEval|RestI|error|sorry" | grep -v "Classical.choice, Quot.sound\]$" || true
if echo "$out" | grep -qE "error|sorryAx" || [ "${rc:-0}" != 0 ]; then echo "$out" | tail -20; exit 1; fi
