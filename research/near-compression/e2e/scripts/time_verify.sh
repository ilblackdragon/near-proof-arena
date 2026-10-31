#!/usr/bin/env bash
# Time the independent verifier on a run directory. usage: time_verify.sh RUN_DIR THREADS CPUSET [BINARY] [CASE]
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-zk}
R=${1:?run dir}; T=${2:?threads}; CPUS=${3:?cpuset}
B=${4:-$D/target/release/nearproof-chunk-e2e}
CASE=${5:-$(python3 -c "import json,sys;d=json.load(open(sys.argv[1]));print([p for p in d['inputs'] if p.endswith('claim.bin')][0].rsplit('/',1)[0])" "$R/RUN.json")}
AIR=$ROOT/examples/np-udr-stark-v2/source/near-air-v3.json
SP=$D/target-classical/release/examples/statepublic
export RAYON_NUM_THREADS=$T
/usr/bin/time -f "wall_s=%e max_rss_kb=%M" taskset -c "$CPUS" "$B" verify "$AIR" "$CASE/claim.bin" "$SP" "$R/SETUP.json" "$(cat "$R/SETUP.sha256")" "$R/FINAL.bundle"
