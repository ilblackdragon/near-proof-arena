#!/usr/bin/env bash
# E2E-D D-8: heights census of every D0a-compatible honest chunk of the d1/d2/d3 corpora
# (meta.json: kind honest, in_d0, expected_rel_d0). statedump --heights-only (no re-check, no
# traces): heights.json + pubmsgs.json per chunk; a chunk whose render fails is listed as FAIL.
# usage: census_d8.sh OUT [JOBS] [CPUS]
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d8}
export SD=$D/target-sd/release/examples/statedump AIR=$ROOT/examples/np-udr-stark-v2/source/near-air-v3.json
export O=${1:?out}; J=${2:-8}; C=${3:-8-15}
mkdir -p "$O"
[ -x "$SD" ] || { echo "no statedump at $SD"; exit 1; }
one() {
  k=$1; c=$2; n=${k}_$(basename "$c")
  [ -f "$O/$n/heights.json" ] && return 0
  if timeout 600 "$SD" d0a "$AIR" "$c" "$O/$n" --heights-only > "$O/$n.log" 2>&1; then rm -f "$O/$n.log"; else echo "FAIL $n"; fi
}
export -f one
python3 "$HERE/census_list.py" > "$O/list.txt" || exit 1
echo "candidates $(wc -l < "$O/list.txt")"
taskset -c "$C" xargs -P "$J" -L 1 bash -c 'one "$0" "$1"' < "$O/list.txt"
echo "CENSUS_DONE ok=$(ls -d "$O"/*/ | wc -l) fail=$(ls "$O"/*.log 2>/dev/null | wc -l)"
