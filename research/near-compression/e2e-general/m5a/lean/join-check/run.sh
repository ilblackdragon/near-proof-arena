#!/usr/bin/env bash
# B-T1: check lane B's `FitsReach` (stOfI form, lane E's D-a) against lane E's `StViewE.lean` (not a lake module):
# concatenate it with lane E's `join/StateW.lean` (D-c), `join/RestI.lean` (D-d), `FitsReachK.lean` and (B-T4)
# `StNoneE.lean` (`stD .none` of `stViewE`, kernel-evaluated) and elaborate in lane B's package environment.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
T=${TMPDIR:-/data/illia/nearproof-deps/laneB-tmp}/FitsReachJoin.$$.lean
mkdir -p "$(dirname "$T")"
{ echo "import StateM5a.StNone"; cat "$HERE/../../../join/StViewE.lean" "$HERE/../../../join/StateW.lean" "$HERE/../../../join/RestI.lean" "$HERE/FitsReachK.lean" "$HERE/StNoneE.lean"; } > "$T"
( cd "$HERE/.." && lake env lean "$T" ) | grep -E "fitsReach|StateW|RestI|StNoneE|sorry|error" || true
rm -f "$T"
