#!/usr/bin/env bash
# E2E-D D-8: coverage check of a class set over the census. For every chunk of assign.json: the
# re-checked dump at its class (statedump --class: every classical constraint re-checked at the
# class heights) and the PQ driver's class-admits (TAPE pad, logs, tight heights, the base prover's
# precheck: every constraint and bus balance). Dumps are deleted after the check.
# usage: cover_d8.sh CLASS_DIR OUT [JOBS] [CPUS]     prints COVER_DONE ok=.. fail=..
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d8}
export SD=$D/target-sd/release/examples/statedump P=${PROVER:-$D/target/release/nearproof-chunk-e2e}
export AIR=$ROOT/examples/np-udr-stark-v2/source/near-air-v3.json
export CL=${1:?class dir} O=${2:?out}; J=${3:-8}; C=${4:-8-15}
mkdir -p "$O"
one() {
  n=$1; k=$2; src=$3
  [ -f "$O/$n.ok" ] && return 0
  t=$O/tmp-$n; rm -rf "$t"
  if ! RAYON_NUM_THREADS=1 timeout 1800 "$SD" d0a "$AIR" "$src" "$t" --class="$CL/$k.json" > "$O/$n.log" 2>&1; then
    echo "COVER_FAIL $n $k statedump: $(grep -h -A1 panicked "$O/$n.log" | tail -1 | cut -c1-200)"; rm -rf "$t"; return 0
  fi
  if RAYON_NUM_THREADS=1 "$P" class-admits "$CL/$k.json" "$AIR" "$t" >> "$O/$n.log" 2>&1; then
    grep -h "grown" "$O/$n.log" | sed "s/^/$n /" > "$O/$n.ok"; echo "COVER_OK $n $k"
  else
    echo "COVER_FAIL $n $k admits: $(grep -h CLASS_ADMITS_FAIL "$O/$n.log" | cut -c1-200)"
  fi
  rm -rf "$t"
}
export -f one
python3 - "$CL/assign.json" > "$O/jobs.txt" <<'EOF' || exit 1
import json, sys
a = json.load(open(sys.argv[1]))
src = {}
for l in open(a['census'] + '/list.txt'):
    k, p = l.split()
    src[k + '_' + p.rstrip('/').split('/')[-1]] = p
for c, k in a['assign'].items():
    print(c, k, src[c])
EOF
# ONLY=FILE: restrict to the chunk names listed in FILE (a sample run)
if [ -n "${ONLY:-}" ]; then grep -F -w -f "$ONLY" "$O/jobs.txt" > "$O/jobs.sel" || true; mv "$O/jobs.sel" "$O/jobs.txt"; fi
taskset -c "$C" xargs -P "$J" -L 1 bash -c 'one "$0" "$1" "$2"' < "$O/jobs.txt" >> "$O/cover.txt"
ok=0; fail=0
while read -r n k _; do if [ -f "$O/$n.ok" ]; then ok=$((ok + 1)); else fail=$((fail + 1)); echo "NOT_COVERED $n $k"; fi; done < "$O/jobs.txt"
echo "COVER_DONE ok=$ok fail=$fail jobs=$(wc -l < "$O/jobs.txt")"
