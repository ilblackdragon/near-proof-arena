#!/usr/bin/env bash
# E2E M4c (lane A, sub-lane NV): non-vacuity of the AIR relations lane A's soundness theorems assume.
#
#   nonvacuity.sh <work_dir> [refill_prep.json]
#
# Dumps honest traces from the native prover (`segdump` / `dump`, native/wasm-base/src/dump.rs) and
# runs the kernel-proved-sound Lean checkers on them (`wasmbase-tool holds`,
# wasm-base-lean/WasmBase/Check/{HoldsCheck,PremCheck,TraceDump}.lean).  A line
#   RESULT <relation> (<air> <nloc> <ngl>): SATISFIED
# is printed exactly when the Boolean checker returned true, which by `checkHolds_sound` /
# `checkHoldsX_sound` / `checkSeg_sound` means the dumped trace satisfies the relation.
#
# Traces: the corpus refill call `3b1ad423.run` (96 steps, host calls, a register refill; prepared
# with `wasmbase-tool prepM2`, as in M4/M4b) cut every 30 steps into 4 segments, for both
# `wasmBaseSegAir` and `wasmBaseSegAirMP`; the same call un-cut for `wasmBaseM2Air`/`M2rAir`/`M3Air`;
# KAT programs (native/wasm-base/programs/gen.py) for the older AIRs (base/host/reg/hash/if*).
#
# Needs: `lake build wasmbase-tool` (wasm-base-lean) and the prover built with the dump commands
# (`cargo build --release` in native/wasm-base, or WASMBASE_BIN).  Run inside a memory-capped scope.
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
W=${1:?work dir}
REFILL=${2:-/data/illia/nearproof-deps/e2e-laneA/m2mut/refill.json}
TOOL=${WASMBASE_TOOL:-$HERE/../../wasm-base-lean/.lake/build/bin/wasmbase-tool}
BIN=${WASMBASE_BIN:-$HERE/../../native/wasm-base/target/release/nearproof-wasm-base}
G0=1000000000000000
mkdir -p "$W"; cd "$W"
export RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-4}
sha256sum "$REFILL"

# 1. dumps
"$TOOL" airSeg 0 0 > airSeg.json
"$TOOL" airSegMP 0 0 > airSegMP.json
"$TOOL" airM2 5 1 > airM2-5-1.json
"$TOOL" airM2r 5 1 > airM2r-5-1.json
"$TOOL" airM3 5 1 > airM3-5-1.json
"$BIN" segdump airSeg.json airM2-5-1.json "$REFILL" 30 seg > segdump-seg.log 2>&1 || echo "SEGDUMP seg FAILED"
"$BIN" segdump airSegMP.json airM2-5-1.json "$REFILL" 30 segmp > segdump-segmp.log 2>&1 || echo "SEGDUMP segMP FAILED"
for k in M2 M2r M3; do
  "$BIN" dump air$k-5-1.json "$REFILL" refill.$k.bin > dump-refill.$k.log 2>&1 || echo "DUMP refill $k FAILED"
done
python3 "$HERE/../../native/wasm-base/programs/gen.py" progs > /dev/null
dumpkat() {  # <program> <prep command> <air command> <tag>
  local n=$1 pc=$2 k=$3 inp nloc ngl
  inp=$(python3 -c "import json;print(json.load(open('progs/$n.json')).get('input',''))")
  [ -f "$n.$pc.json" ] || "$TOOL" "$pc" "progs/$n.wasm" main $G0 "$inp" > "$n.$pc.json"
  read -r nloc ngl <<<"$(python3 -c "import json;d=json.load(open('$n.$pc.json'));print(len(d['localTags']),d.get('ngl',0))")"
  "$TOOL" "$k" "$nloc" "$ngl" > "$n.$k.json"
  "$BIN" dump "$n.$k.json" "$n.$pc.json" "$n.$k.bin" > "$n.$k.dump.log" 2>&1 || echo "DUMP $n $k FAILED"
  echo "$nloc $ngl" > "$n.$k.dims"
}
for n in fib10 hashloop8; do dumpkat $n prep air; done
for n in fib10 hostkat8 hostctxreg hashloop8; do for k in airH airR airX; do dumpkat $n prep $k; done; done
for n in fib10 hostkat8 hostctxreg; do for k in airIfH airIfR; do dumpkat $n prepIf $k; done; done
dumpkat fib10 prepIf airIf

# 2. checks
for i in 0 1 2 3; do
  "$TOOL" holds seg 0 0 seg-$i.bin
  "$TOOL" holds segMP 0 0 segmp-$i.bin
done
"$TOOL" holds m2 5 1 refill.M2.bin
"$TOOL" holds m2r 5 1 refill.M2r.bin
"$TOOL" holds m3 5 1 refill.M3.bin
chk() {  # <air name> <program> <air command> [second AIR name]
  local d; read -r d < "$2.$3.dims"
  if [ -n "${4:-}" ]; then "$TOOL" holds "$1" $d "$2.$3.bin" "$4" $d; else "$TOOL" holds "$1" $d "$2.$3.bin"; fi
}
for n in fib10 hashloop8; do chk base $n air; done
for n in fib10 hostkat8 hostctxreg hashloop8; do chk host $n airH base; chk reg $n airR; chk hash $n airX; done
for n in fib10 hostkat8 hostctxreg; do chk ifHost $n airIfH; chk ifReg $n airIfR; done
chk if fib10 airIf
echo "NONVACUITY DONE"
