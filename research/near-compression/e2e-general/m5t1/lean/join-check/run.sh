#!/usr/bin/env bash
# F-5 / F-7: check lane F's STATE instances against lane E's `join/StViewE.lean`, `join/StateW.lean`
# and (F-7) `join/RestI.lean` (not lake modules): one file = lane F's imports + their imports, then
# StViewE, StateW, RestI (import lines dropped), StateSE (F-5) and SeStepI (F-7); elaborated in lane
# F's package environment (`M5T1`, which requires lane B's `StateM5a`). Prints the axioms lines;
# exit 1 on error.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
J=$HERE/../../../join
T=${TMPDIR:-/data/illia/nearproof-deps/tmp-laneF}/StateSEJoin.$$.lean
mkdir -p "$(dirname "$T")"
{ echo "import M5T1.SeC"; grep -h '^import ' "$J/StViewE.lean" "$J/StateW.lean" | sort -u
  grep -hv '^import ' "$J/StViewE.lean"; grep -hv '^import ' "$J/StateW.lean"; grep -hv '^import ' "$J/RestI.lean"
  cat "$HERE/StateSE.lean" "$HERE/SeStepI.lean"; } > "$T"
out=$(cd "$HERE/.." && lake env lean "$T" 2>&1 || true)
rm -f "$T"
echo "$out" | grep -E "StateSE|SeStepI|error|sorry" || true
if echo "$out" | grep -qE "error|sorryAx"; then exit 1; fi
