#!/usr/bin/env bash
# perf-profile the independent verifier on one core. usage: perf_verify.sh RUN_DIR CASE_DIR OUT_DIR [BINARY]
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-zk}
R=${1:?run dir}; CASE=${2:?case}; O=${3:?out}
B=${4:-$D/target/release/nearproof-chunk-e2e}
mkdir -p "$O"
export RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-1}
${PERF:-sudo -n -E perf} record -e cycles:u -F 499 -g -o "$O/perf.data" -- taskset -c "${CPUSET:-15}" "$B" verify \
  "$ROOT/examples/np-udr-stark-v2/source/near-air-v3.json" "$CASE/claim.bin" \
  "$D/target-classical/release/examples/statepublic" "$R/SETUP.json" "$(cat "$R/SETUP.sha256")" "$R/FINAL.bundle" 2>&1 | tail -3
sudo -n perf report -f -i "$O/perf.data" --no-children --sort comm,dso,symbol --stdio 2>/dev/null | grep -v "^#" | grep "%" | grep -v "^ *|" | grep -v -- "--" | head -45 > "$O/top.txt"
sudo -n perf report -f -i "$O/perf.data" --children --sort symbol --stdio 2>/dev/null | grep -v "^#" | grep "%" | grep -v "^ *|" | grep -v -- "--" | head -80 > "$O/children.txt"
cat "$O/top.txt"
