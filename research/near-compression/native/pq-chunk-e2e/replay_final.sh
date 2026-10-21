#!/usr/bin/env bash
# Replay identical, trusted input for thread/allocation experiments, with all final checks.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-chunk-perf}
SOURCE=$(realpath "${1:?usage: replay_final.sh SOURCE OUT [LEVEL]}")
OUT=$(realpath -m "${2:?output directory}")
LEVEL=${3:-5}
mkdir -p "$(dirname "$OUT")"
mkdir "$OUT"
for f in BASE.proof BASE.vk.json hint.bin "L$LEVEL.proof" "L$LEVEL.vk.json" "L$LEVEL.state.json"; do
  cp "$SOURCE/$f" "$OUT/$f"
done
python3 - "$SOURCE" "$OUT" <<'PYMETA'
import hashlib,json,pathlib,sys
source,out=map(pathlib.Path,sys.argv[1:])
files=list(out.glob('*'))+[source/'SETUP.json',source/'FINAL.bundle']
(out/'INPUTS.json').write_text(json.dumps({str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},indent=2)+'\n')
PYMETA
AIR=$ROOT/examples/np-udr-stark-v2/source/near-air-v3.json
CASE=$ROOT/oracle/fixtures/v3/public-d0a/d0/00-h10004-s3
K=$ROOT/research/near-compression/final-soundness
B=${PROVER_BINARY:-$D/target/release/nearproof-chunk-e2e}
REF=${REFERENCE_BINARY:-$SOURCE/profiles/base/executable}
C=$SOURCE/profiles/public/executable
mkdir "$OUT/tools"
cp --reflink=auto "$B" "$OUT/tools/prover"
cp --reflink=auto "$REF" "$OUT/tools/reference"
cp --reflink=auto "$C" "$OUT/tools/statepublic"
chmod +x "$OUT/tools/"*
B=$OUT/tools/prover
REF=$OUT/tools/reference
C=$OUT/tools/statepublic
python3 - "$OUT" <<'PYTOOLS'
import hashlib,json,pathlib,sys
out=pathlib.Path(sys.argv[1])
(out/'TOOLS.json').write_text(json.dumps({p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (out/'tools').iterdir()},indent=2)+'\n')
PYTOOLS
export HEAVY_MEM=${HEAVY_MEM:-32G} RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-8}
run() {
  local stage=$1
  shift
  taskset -c "${CPUSET:-8-15,24-31}" /data/illia/nearproof-deps/bin/heavy \
    python3 "$HERE/profile.py" run "$OUT/profiles/$stage" -- "$@"
}
run prove "$B" replay-final "$AIR" "$SOURCE/public" "$OUT" "$K/calc/dkt_certs_o2.json" "$K/lean/DKTCertsO2_big.keys" "$LEVEL" > "$OUT/prove.log" 2>&1
# Verify with the ORIGINAL executable and independently pinned ORIGINAL setup.
run verify "$REF" verify "$AIR" "$CASE/claim.bin" "$C" "$SOURCE/SETUP.json" "$(cat "$SOURCE/SETUP.sha256")" "$OUT/FINAL.bundle" > "$OUT/verify.log" 2>&1
cmp "$SOURCE/SETUP.json" "$OUT/SETUP.json"
cmp "$SOURCE/FINAL.bundle" "$OUT/FINAL.bundle"
run negatives python3 "$HERE/test_packet.py" "$REF" "$AIR" "$CASE/claim.bin" "$C" "$OUT" > "$OUT/negatives.log" 2>&1
python3 - "$OUT/RESULT.json" <<'PY'
import json,sys
r=json.load(open(sys.argv[1])); assert r['bundle_bytes']<300000, r
print('REPLAY_IDENTICAL_AND_VERIFIED', r['bundle_bytes'])
PY
