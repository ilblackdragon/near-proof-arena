#!/usr/bin/env bash
# Prover-work scaling without grinding (WASMBASE_POW=0; query count unchanged by z only through
# the target, see README): hash loop at 64/256/1024 iterations, small shape.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
S=${1:?scratch}; LOG=${2:?logdir}
mkdir -p "$S" "$LOG"
TOOL=$HERE/../../wasm-base-lean/.lake/build/bin/wasmbase-tool
# shellcheck source=bin.sh
. "$HERE/bin.sh"
BIN=$(resolve_bin) || exit 1
RUN="nice -n 10 env HEAVY_MEM=20G taskset -c 8-15 /data/illia/nearproof-deps/bin/heavy"
export RAYON_NUM_THREADS=8 WASMBASE_POW=0
python3 "$HERE/programs/gen.py" "$S/progs" 64 256 1024 >/dev/null
for n in 64 256 1024; do
  "$TOOL" prep "$S/progs/hashloop$n.wasm" main 1000000000000000 > "$S/progs/hashloop$n.prep.json"
  read -r nl nc <<<"$(python3 -c "import json;d=json.load(open('$S/progs/hashloop$n.prep.json'));print(len(d['localTags']),d['ncode'])")"
  [ -f "$S/air-$nl-$nc.json" ] || "$TOOL" air "$nl" "$nc" > "$S/air-$nl-$nc.json"
  for rep in 1 2; do
    /usr/bin/time -v $RUN "$BIN" prove "$S/air-$nl-$nc.json" "$S/progs/hashloop$n.prep.json" small > "$LOG/prove-hashloop$n-small-z0-r$rep.log" 2>&1
  done
done
echo done
