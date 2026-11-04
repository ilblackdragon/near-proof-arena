#!/usr/bin/env bash
# E2E-D milestone D-8 (2026-11-04): a production base-class set over the corpus census, coverage,
# and >= 2 chunks per class proved against one tree setup (arity 4, the D-8 default).
#  1. classes: classes_d8.py over the census (census_d8.sh) -> $D/classes8/{S,M,L}.json + assign.json
#  2. coverage: cover_d8.sh (every census chunk re-cut at its class, re-checked, admitted)
#  3. bases: two members per class (the largest and the median by natural committed cells), dumped
#     at the class (statedump --class), base-proved at the class shape (NEARPROOF_BASE_CLASS)
#  4. trees: arity 4 (default), depth 1; the setup made by class S's first member over the class
#     dirs (S1 M1 L1), confirmed by S2 M2 L2 (review-D6 F5); the other five chunks proved against
#     that setup (must reproduce it byte for byte); fresh-process negatives on two of them.
# Sequential; bases at 10 threads, trees at 8; <= 40 GB.  usage: run_d8.sh [STEPS]
#   env: LEAF_PARAMS (NEARPROOF_TREE_LEAF_PARAMS for every tree run; default ns20lb2 = the D-8 leaf lever)
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d8}
export NEARPROOF_PQ_DEPS=$D PROVER=${PROVER:-$D/target/release/nearproof-chunk-e2e}
SD=$D/target-sd/release/examples/statedump
SP=/data/illia/nearproof-deps/pq-e2e-d/e2e/d1_00-h10006-s3/tools/statepublic
AIR=$ROOT/examples/np-udr-stark-v2/source/near-air-v3.json
K=$ROOT/research/near-compression/final-soundness
CL=$D/classes8; BB=$D/b8
export NEARPROOF_TREE_LEAF_PARAMS=${LEAF_PARAMS:-ns20lb2}
# one leaf geometry per setup: class L's leaf (a base at n_stack 22) needs NvAir 2^20 / program 2^19
export NEARPROOF_TREE_LEAF_GEOM=${LEAF_GEOM:-20,19}
die() { echo "RUN_D8_FAILED $*"; exit 1; }
members() { python3 "$HERE/pick_members_d8.py" "$CL/assign.json"; }
base() { # CLASS NAME CASE_DIR
  local k=$1 n=$2 src=$3 R=$BB/$2
  [ -f "$R/BASE.proof" ] && { echo "BASE $n class=$k (exists)"; return 0; }
  mkdir -p "$BB/dumps" "$BB/public"; rm -rf "$BB/dumps/$n" "$R"; mkdir -p "$R"
  RAYON_NUM_THREADS=10 taskset -c 8-15,24-25 "$SD" d0a "$AIR" "$src" "$BB/dumps/$n" --class="$CL/$k.json" > "$BB/dumps/$n.log" 2>&1 || die "statedump $n: $(tail -2 "$BB/dumps/$n.log")"
  [ -d "$BB/public/$n" ] || "$SP" "$AIR" "$src/claim.bin" "$BB/dumps/$n/hint.bin" "$BB/public/$n" > "$BB/public/$n.log" 2>&1 || die "statepublic $n"
  cmp -s "$BB/public/$n/pubs.bin" "$BB/dumps/$n/pubs.bin" || die "public mismatch $n"
  ln -sfn "$BB/public/$n" "$R/public"
  cp "$src/claim.bin" "$R/claim.bin"
  RAYON_NUM_THREADS=10 HEAVY_MEM=40G NEARPROOF_ZK=1 NEARPROOF_TAPE_EVAL=1 NEARPROOF_CHAIN_GEOM=ns19lb6 NEARPROOF_BASE_CLASS="$CL/$k.json" \
    taskset -c 8-15,24-25 /data/illia/nearproof-deps/bin/heavy /usr/bin/time -v \
    "$PROVER" base "$AIR" "$BB/dumps/$n" "$R" "$K/calc/dkt_certs_o2.json" "$K/lean/DKTCertsO2_big.keys" > "$R/base.log" 2>&1 || die "base $n rc=$? $(grep -h -A2 panicked "$R/base.log" | head -3 | tr '\n' ' ')"
  grep -q BASE_CLASS_HEIGHTS_OK "$R/base.log" || die "base $n: no BASE_CLASS_HEIGHTS_OK"
  echo "BASE $n class=$k $(grep -h 'BASE_CLASS_TAPE_PAD\|BASE_CLASS_HEIGHTS_OK\|BASE_VERIFIED\|Elapsed\|Maximum resident' "$R/base.log" | tr '\n' ' ')"
  rm -rf "$BB/dumps/$n"
}
for s in ${1:-1 2 3 4}; do case $s in
1) python3 "$HERE/classes_d8.py" "$D/census" "$CL" --cuts "${CUTS:-0.5,0.95}" > "$CL.txt" || die classes; cat "$CL.txt" ;;
2) "$HERE/cover_d8.sh" "$CL" "$D/cover" 8 8-15 | tee "$D/cover.txt"; grep -q "fail=0 " "$D/cover.txt" || die "coverage has failures" ;;
3) members | while read -r k n src; do base "$k" "$n" "$src" || exit 1; done || die bases ;;
4)
  mapfile -t M < <(members)
  declare -A C1 C2; ORDERK=()
  for l in "${M[@]}"; do set -- $l; if [ -z "${C1[$1]:-}" ]; then C1[$1]=$BB/$2; ORDERK+=("$1"); else C2[$1]=$BB/$2; fi; done
  CLASS_DIRS=""; CONFIRM=""
  for k in "${ORDERK[@]}"; do CLASS_DIRS+="${C1[$k]} "; [ -n "${C2[$k]:-}" ] && CONFIRM+="${C2[$k]} "; done
  export CLASS_DIRS NEARPROOF_TREE_CONFIRM="$CONFIRM"
  S1=${C1[${ORDERK[0]}]}
  "$HERE/run_tree.sh" tree8 - 1 "$S1" "$S1/claim.bin" || die "tree $S1"
  SETUP=$D/tree8/$(basename "$S1")/SETUP.json
  for k in "${ORDERK[@]}"; do for c in ${C1[$k]} ${C2[$k]:-}; do
    [ "$c" = "$S1" ] && continue
    "$HERE/run_tree.sh" tree8 - 1 "$c" "$c/claim.bin" "$SETUP" || die "tree $c"
  done; done
  A=${C2[${ORDERK[0]}]:-$S1}; Bm=${C2[${ORDERK[1]}]:-${C1[${ORDERK[1]}]}}
  for p in "$S1 $Bm" "$Bm $S1"; do set -- $p
    python3 "$HERE/tree_negatives.py" "$D/tree8/$(basename "$1")" "$1/claim.bin" "$2/claim.bin" "$D/tree8/$(basename "$2")" > "$D/tree8/$(basename "$1")/negatives.txt" 2>&1 || die "negatives $1"
    tail -1 "$D/tree8/$(basename "$1")/negatives.txt"
  done
  ;;
esac; done
echo D8_DONE
