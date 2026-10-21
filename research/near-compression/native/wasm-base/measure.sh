#!/usr/bin/env bash
# Measurements for results/pq-wasm-base: real proofs of the hash-loop workload at several lengths
# (marginal cost per op), the pinned 2^24 shape, KATs, difftest and the tamper suite.
# Usage: measure.sh <scratch> <logdir>.  Runs under the heavy wrapper, 8 threads, nice 10.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
S=${1:?scratch}; LOG=${2:?logdir}
mkdir -p "$S" "$LOG"
TOOL=$HERE/../../wasm-base-lean/.lake/build/bin/wasmbase-tool
# shellcheck source=bin.sh
. "$HERE/bin.sh"
BIN=$(resolve_bin) || exit 1
RUN="nice -n 10 env HEAVY_MEM=20G taskset -c 8-15 /data/illia/nearproof-deps/bin/heavy"
export RAYON_NUM_THREADS=8
python3 "$HERE/programs/gen.py" "$S/progs" 16 64 256 >/dev/null
prep() { "$TOOL" prep "$S/progs/$1.wasm" main 1000000000000000 > "$S/progs/$1.prep.json"
  read -r nl nc <<<"$(python3 -c "import json;d=json.load(open('$S/progs/$1.prep.json'));print(len(d['localTags']),d.get('ngl',0))")"
  [ -f "$S/air-$nl-g$nc.json" ] || "$TOOL" air "$nl" "$nc" > "$S/air-$nl-g$nc.json"; echo "$S/air-$nl-g$nc.json"; }
for n in 16 64 256; do
  air=$(prep hashloop$n)
  /usr/bin/time -v $RUN "$BIN" prove "$air" "$S/progs/hashloop$n.prep.json" small > "$LOG/prove-hashloop$n-small.log" 2>&1
done
air=$(prep hashloop64)
/usr/bin/time -v $RUN "$BIN" prove "$air" "$S/progs/hashloop64.prep.json" pinned > "$LOG/prove-hashloop64-pinned.log" 2>&1
air=$(prep ctrl)
$RUN "$BIN" prove "$air" "$S/progs/ctrl.prep.json" small > "$LOG/prove-ctrl-small.log" 2>&1
echo done
