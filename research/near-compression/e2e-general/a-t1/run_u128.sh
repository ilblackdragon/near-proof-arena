#!/usr/bin/env bash
# A-T1 item 1: the write-coverage KAT (u128kat.wat) on the segment AIR with HOSTB's write pair.
#   run_u128.sh <work_dir> [K]
# Needs fresh `wasmbase-tool` and release prover (see env.sh); AIR_PATCH=1 applies the JSON mirror
# of the Lean change (only before the Lean HostBK change is built).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
. /data/illia/nearproof-deps/e2e-laneA/at1/env.sh
WD=${1:?work dir}; K=${2:-20}
mkdir -p "$WD"; cd "$WD"
wasm-tools parse "$HERE/u128kat.wat" -o u128kat.wasm
$T prepM2 u128kat.wasm run 1000000000000000 > u128.prep.json
python3 -c "import json;p=json.load(open('u128.prep.json'));[print('HOST',h['hid'],h['args'],h.get('wr')) for h in p['hosts']];print('steps',p['steps'],p['status'],p['stack'])"
$T airSegMP 0 0 > airSeg0.json
if [ -n "${AIR_PATCH:-}" ]; then python3 "$HERE/patch_air_json.py" airSeg0.json airSeg.json; else cp airSeg0.json airSeg.json; fi
NL=$(python3 -c "import json;p=json.load(open('u128.prep.json'));print(len(p['localTags']),p['ngl'])")
$T airM2 $NL > airM2.json
$CAP SEG_TABLES=1 $B segcheck airSeg.json airM2.json u128.prep.json "$K" > segcheck.log 2>&1 || true
grep -E 'PRECHECK|SEGCHECK|panick|FAIL' segcheck.log | head -20
if [ -n "${PROVE:-}" ]; then
  $CAP $B segprove airSeg.json airM2.json u128.prep.json "$K" > segprove.log 2>&1 || true
  grep -E 'PARAMS|PROOF|SEGPROVE|panick' segprove.log
fi
if [ -n "${TAMPER:-}" ]; then
  $CAP $B segtamper airSeg.json airM2.json u128.prep.json "$K" "$TAMPER" > "segtamper-s$TAMPER.log" 2>&1 || true
  grep -E 'HONEST|REJECT|ACCEPT|TAMPER|panick' "segtamper-s$TAMPER.log" | tail -60
fi
