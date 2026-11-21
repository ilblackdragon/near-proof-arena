#!/usr/bin/env bash
# E2E-D M8 prototype, lane A input: T1's Wasm call (lane A's T1 prep, read-only copy) cut into
# segments by lane A's own prover (native/wasm-base on main, built against lane A's backend copy:
# no lane-A source is changed), each segment's trace dumped (`segdump`, M4c format "NPTD").
# The dumps are then proved under the verifier's backend by `nearproof-chunk-e2e m8-prove-a`.
#   usage: m8_laneA.sh WORK [K]     (K = steps per segment, default 13: T1's 26-step call -> 2 segments)
set -euo pipefail
W=$(cd "$(dirname "$0")/../../../.." && pwd)
O=${1:?work dir}; K=${2:-13}
mkdir -p "$O"
TOOL=${WASMBASE_TOOL:-/data/illia/nearproof/research/near-compression/wasm-base-lean/.lake/build/bin/wasmbase-tool}
PREP=${T1_PREP:-/data/illia/nearproof-deps/e2e-laneA/T1tape/prep.json}
export PATH="$HOME/.cargo/bin:$PATH"
CARGO_TARGET_DIR="$O/target" taskset -c "${CPUSET:-4-7}" cargo build --release -j 4 \
  --manifest-path "$W/research/near-compression/native/wasm-base/Cargo.toml" > "$O/build.log" 2>&1 || { tail -20 "$O/build.log"; exit 1; }
B=$O/target/release/nearproof-wasm-base
cp "$PREP" "$O/t1.prep.json"
"$TOOL" airSegMP 0 0 > "$O/airSeg.json"
"$TOOL" airM2 1 0 > "$O/airM2.json"
cd "$O"
RAYON_NUM_THREADS=4 SEG_TABLES=1 taskset -c "${CPUSET:-4-7}" "$B" segcheck airSeg.json airM2.json t1.prep.json "$K" > segcheck.log 2>&1 || { tail -20 segcheck.log; exit 1; }
grep -q "SEGCHECK OK" segcheck.log || { echo "segcheck failed"; exit 1; }
RAYON_NUM_THREADS=4 taskset -c "${CPUSET:-4-7}" "$B" segdump airSeg.json airM2.json t1.prep.json "$K" "$O/seg" > segdump.log 2>&1 || { tail -20 segdump.log; exit 1; }
grep -hE "^DUMP|SEGCHECK OK|SEGDUMP OK" segcheck.log segdump.log
sha256sum t1.prep.json airSeg.json airM2.json seg-*.bin > inputs.sha256
echo M8_LANEA_DUMPS_OK
