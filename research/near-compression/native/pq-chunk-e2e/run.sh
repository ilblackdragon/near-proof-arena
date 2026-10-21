#!/usr/bin/env bash
# OUT contains intermediate proofs, trusted setup, final packet, and verifier evidence.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-chunk-e2e}
OUT=$(realpath -m "${1:?usage: run.sh OUT [CASE]}")
CASE=${2:-$ROOT/oracle/fixtures/v3/public-d0a/d0/00-h10004-s3}
AIR=$ROOT/examples/np-udr-stark-v2/source/near-air-v3.json
B=$D/target/release/nearproof-chunk-e2e
C=$D/target-classical/release/examples
K=$ROOT/research/near-compression/final-soundness
mkdir -p "$OUT"
shopt -s nullglob dotglob
existing=("$OUT"/*)
if ((${#existing[@]})); then
  echo "OUT must be empty; use a new directory to avoid stale success artifacts" >&2
  exit 2
fi
shopt -u nullglob dotglob
# A long run must survive rebuilds/cleanup of external Cargo target directories.
mkdir "$OUT/tools"
cp --reflink=auto "$B" "$OUT/tools/prover"
cp --reflink=auto "$C/statedump" "$C/statepublic" "$OUT/tools/"
B=$OUT/tools/prover
C=$OUT/tools
python3 - "$OUT" "$ROOT" "$AIR" "$CASE/claim.bin" "$B" "$C/statepublic" "$HERE/Cargo.lock" <<'PYMETA'
import hashlib,json,pathlib,subprocess,sys
out,root,*inputs=sys.argv[1:]
metadata={'git_head':subprocess.check_output(['git','-C',root,'rev-parse','HEAD'],text=True).strip(),
          'inputs':{p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest() for p in inputs}}
pathlib.Path(out,'RUN.json').write_text(json.dumps(metadata,indent=2)+'\n')
PYMETA
export HEAVY_MEM=${HEAVY_MEM:-32G} RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-8}
# Profiling is part of every stage, including verification and rejection tests.
run() {
  local stage=$1
  shift
  taskset -c "${CPUSET:-8-15,24-31}" /data/illia/nearproof-deps/bin/heavy \
    python3 "$HERE/profile.py" run "$OUT/profiles/$stage" -- "$@"
}
run dump "$C/statedump" d0a "$AIR" "$CASE" "$OUT/dump" > "$OUT/dump.log" 2>&1
run public "$C/statepublic" "$AIR" "$CASE/claim.bin" "$OUT/dump/hint.bin" "$OUT/public" > "$OUT/public.log" 2>&1
cmp "$OUT/public/pubs.bin" "$OUT/dump/pubs.bin"
cmp "$OUT/public/pubmsgs.json" "$OUT/dump/pubmsgs.json"
run base "$B" base "$AIR" "$OUT/dump" "$OUT" "$K/calc/dkt_certs_o2.json" "$K/lean/DKTCertsO2_big.keys" > "$OUT/base.log" 2>&1
run probe "$B" probe "$OUT" > "$OUT/probe.log" 2>&1
run chain "$B" chain "$AIR" "$OUT/public" "$OUT" "$K/calc/dkt_certs_o2.json" "$K/lean/DKTCertsO2_big.keys" > "$OUT/chain.log" 2>&1
# The operator pins SETUP.sha256 from this trusted run, not from an untrusted proof sender.
run verify "$B" verify "$AIR" "$CASE/claim.bin" "$C/statepublic" "$OUT/SETUP.json" "$(cat "$OUT/SETUP.sha256")" "$OUT/FINAL.bundle" > "$OUT/verify.log" 2>&1
run negatives python3 "$HERE/test_packet.py" "$B" "$AIR" "$CASE/claim.bin" "$C/statepublic" "$OUT" > "$OUT/negative-packet.log" 2>&1
python3 - "$OUT/RESULT.json" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
print(json.dumps(r,indent=2))
if not r['under_300000']:
    raise SystemExit('Verified, but misses the 300,000-byte total-packet target')
PY
