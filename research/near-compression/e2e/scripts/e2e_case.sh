#!/usr/bin/env bash
# One chunk end to end: witness -> public inputs -> base proof -> L1..Ln -> FINAL -> fresh-process
# verify, with per-stage profiles (CPU samples, RSS). Reuses DUMP/BASE from SRC if given.
# usage: e2e_case.sh OUT CASE_DIR [SRC_RUN_WITH_BASE]
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d}
OUT=$(realpath -m "${1:?OUT}")
CASE=$(realpath "${2:?CASE}")
SRC=${3:-}
AIR=$ROOT/examples/np-udr-stark-v2/source/near-air-v3.json
K=$ROOT/research/near-compression/final-soundness
P=$ROOT/research/near-compression/native/pq-chunk-e2e
mkdir -p "$OUT"
[ -z "$(ls -A "$OUT")" ] || { echo "OUT must be empty" >&2; exit 2; }
mkdir "$OUT/tools"
cp --reflink=auto "$D/target/release/nearproof-chunk-e2e" "$OUT/tools/prover"
cp --reflink=auto "$D/target-classical/release/examples/statedump" "$D/target-classical/release/examples/statepublic" "$OUT/tools/"
B=$OUT/tools/prover; C=$OUT/tools
export NEARPROOF_CHAIN_GEOM=${NEARPROOF_CHAIN_GEOM:-ns19lb6} NEARPROOF_TAPE_EVAL=${NEARPROOF_TAPE_EVAL:-1}
export HEAVY_MEM=${HEAVY_MEM:-32G} RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-16}
python3 - "$OUT" "$ROOT" "$AIR" "$CASE/claim.bin" "$CASE/witness.bin" "$B" "$C/statepublic" "$C/statedump" "$P/Cargo.lock" <<'PYMETA'
import hashlib,json,os,pathlib,subprocess,sys
out,root,*inputs=sys.argv[1:]
meta={'git_head':subprocess.check_output(['git','-C',root,'rev-parse','HEAD'],text=True).strip(),
      'env':{k:os.environ.get(k) for k in ['NEARPROOF_CHAIN_GEOM','NEARPROOF_TAPE_EVAL','NEARPROOF_ZK','CPUSET','RAYON_NUM_THREADS','HEAVY_MEM']},
      'inputs':{p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest() for p in inputs}}
pathlib.Path(out,'RUN.json').write_text(json.dumps(meta,indent=2)+'\n')
PYMETA
run() {
  local stage=$1; shift
  local s; s=$(date +%s.%N)
  taskset -c "${CPUSET:-8-15,24-31}" /data/illia/nearproof-deps/bin/heavy \
    python3 "$P/profile.py" run "$OUT/profiles/$stage" -- "$@"
  echo "STAGE $stage wall_s=$(echo "$(date +%s.%N) - $s" | bc)" >> "$OUT/STAGES.txt"
}
if [ -n "$SRC" ]; then
  cp -r "$SRC/dump" "$SRC/public" "$OUT/"
  cp "$SRC/BASE.proof" "$SRC/BASE.vk.json" "$SRC/hint.bin" "$SRC/base.log" "$OUT/"
  echo "REUSED dump public base from $SRC" >> "$OUT/STAGES.txt"
  run validate-base "$B" validate-base "$AIR" "$OUT/public" "$OUT" > "$OUT/validate-base.log" 2>&1
else
  run dump "$C/statedump" d0a "$AIR" "$CASE" "$OUT/dump" > "$OUT/dump.log" 2>&1
  run public "$C/statepublic" "$AIR" "$CASE/claim.bin" "$OUT/dump/hint.bin" "$OUT/public" > "$OUT/public.log" 2>&1
  cmp "$OUT/public/pubs.bin" "$OUT/dump/pubs.bin"
  cmp "$OUT/public/pubmsgs.json" "$OUT/dump/pubmsgs.json"
  run base "$B" base "$AIR" "$OUT/dump" "$OUT" "$K/calc/dkt_certs_o2.json" "$K/lean/DKTCertsO2_big.keys" > "$OUT/base.log" 2>&1
fi
run chain "$B" chain "$AIR" "$OUT/public" "$OUT" "$K/calc/dkt_certs_o2.json" "$K/lean/DKTCertsO2_big.keys" > "$OUT/chain.log" 2>&1
# fresh process, trusted pin from this run (integration only; an operator pins independently)
run verify "$B" verify "$AIR" "$CASE/claim.bin" "$C/statepublic" "$OUT/SETUP.json" "$(cat "$OUT/SETUP.sha256")" "$OUT/FINAL.bundle" > "$OUT/verify.log" 2>&1
cat "$OUT/RESULT.json"
