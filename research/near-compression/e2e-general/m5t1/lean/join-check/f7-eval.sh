#!/usr/bin/env bash
# F-7: evaluate the preimages lane F's SE opening rows hash (`F7Eval.lean`), on T1's engine cuts.
#   f7-eval.sh CASE_DIR IN_JSON OUT_JSON      (IN_JSON: {"keys": [hex …]}, as join/rest-eval.sh)
# One file = the imports, then lane E's StViewE / StateW / RestI / RestEval (import lines and
# RestEval's `main` dropped) and F7Eval.lean; run with `lake env lean --run` in lane B's package.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
J=$HERE/../../../join
PKG=${M5A_PKG:-$HERE/../../../m5a/lean}
T=${TMPDIR:-/data/illia/nearproof-deps/tmp-laneF}/F7Eval.$$.lean
mkdir -p "$(dirname "$T")"
{ { echo "import StateM5a.StNone"; echo "import NearSpecV3.E2E.ViewSer"; echo "import Lean.Data.Json"
    grep -h '^import ' "$J/StViewE.lean" "$J/StateW.lean"; } | sort -u
  for f in StViewE StateW RestI; do grep -hv '^import ' "$J/$f.lean"; done
  grep -v '^import ' "$J/RestEval.lean" | sed '/^def main/,$d'
  grep -hv '^import ' "$HERE/F7Eval.lean"; } > "$T"
out=$(cd "$PKG" && lake env lean --run "$T" "$(realpath "$1")" "$(realpath "$2")" "$(realpath -m "$3")" 2>&1) || rc=$?
rm -f "$T"
if echo "$out" | grep -qE "error|sorryAx" || [ "${rc:-0}" != 0 ]; then echo "$out" | tail -20; exit 1; fi
echo "f7-eval: wrote $3"
