#!/usr/bin/env bash
# E2E-D milestone D-9 (2026-11-04/05): one leaf geometry per family under one wrap setup; every
# layer at the 274-bit per-round target on one chunk; a random corpus throughput sample.
#  1. prod: the production setup (arity 4, depth 1, leaf families auto: S + M at their own leaf
#     geometry, L at its own), made by class S's first D-8 member over the D-8 class dirs (S1 M1 L1,
#     confirmed by S2 M2 L2); M1 and L1 proved against it (must reproduce it byte for byte);
#     fresh-process negatives S1 <-> L1 (the two families); tree-audit (S2 M2 L2 regenerate the roots)
#  2. r274: NEARPROOF_RBR_ALL=274 (base, leaves, P_2, wrap): bases of S1 and S2 at 274, a one-class
#     setup (class S) made by S1, confirmed by S2; soundness of every vk recorded
#  3. sample: pick_sample_d9.py (seeded, 6 S / 2 M / 2 L, not the D-8 members): each chunk dumped
#     at its class, base-proved, then tree-proved against the production setup (fixed: must
#     reproduce it), verified 3x in fresh processes; wall time per stage in sample/TIMES.tsv
# Sequential; bases at 10 threads, trees at 8; <= 40 GB. Exits 1 on the first failure.
# usage: run_d9.sh [STEPS]   (default: 1 2 3; 2base: only step 2's bases; env BASE_CPUS / BASE_THREADS
#   for the base proofs, default 8-15,24-25 / 10)
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d9}
export NEARPROOF_PQ_DEPS=$D PROVER=${PROVER:-$D/target/release/nearproof-chunk-e2e}
# statedump (target-sd vanished twice on this host, not by these scripts: D-9 builds it in sdbuild)
SD=${SD:-$D/sdbuild/release/examples/statedump}
SP=/data/illia/nearproof-deps/pq-e2e-d/e2e/d1_00-h10006-s3/tools/statepublic
AIR=$ROOT/examples/np-udr-stark-v2/source/near-air-v3.json
K=$ROOT/research/near-compression/final-soundness
CL=$D/classes8; B8=$D/b8
export NEARPROOF_TREE_LEAF_PARAMS=${LEAF_PARAMS:-ns20lb2} NEARPROOF_TREE_LEAF_FAMILIES=${LEAF_FAMILIES:-auto}
unset NEARPROOF_TREE_LEAF_GEOM NEARPROOF_RBR_ALL
die() { echo "RUN_D9_FAILED $*"; exit 1; }
members() { python3 "$HERE/pick_members_d8.py" "$CL/assign.json"; }
# base CLASS NAME CASE_DIR OUT_ROOT: dump at the class, statepublic, base proof at the class shape
base() {
  local k=$1 n=$2 src=$3 BB=$4 R=$4/$2
  [ -f "$R/BASE.proof" ] && { echo "BASE $n class=$k (exists)"; return 0; }
  mkdir -p "$BB/dumps" "$BB/public"; rm -rf "$BB/dumps/$n" "$R"; mkdir -p "$R"
  local t0; t0=$(date +%s)
  RAYON_NUM_THREADS=${BASE_THREADS:-10} taskset -c "${BASE_CPUS:-8-15,24-25}" "$SD" d0a "$AIR" "$src" "$BB/dumps/$n" --class="$CL/$k.json" > "$BB/dumps/$n.log" 2>&1 || die "statedump $n: $(tail -2 "$BB/dumps/$n.log")"
  [ -d "$BB/public/$n" ] || "$SP" "$AIR" "$src/claim.bin" "$BB/dumps/$n/hint.bin" "$BB/public/$n" > "$BB/public/$n.log" 2>&1 || die "statepublic $n"
  cmp -s "$BB/public/$n/pubs.bin" "$BB/dumps/$n/pubs.bin" || die "public mismatch $n"
  local t1; t1=$(date +%s)
  ln -sfn "$BB/public/$n" "$R/public"
  cp "$src/claim.bin" "$R/claim.bin"
  RAYON_NUM_THREADS=${BASE_THREADS:-10} HEAVY_MEM=40G NEARPROOF_ZK=1 NEARPROOF_TAPE_EVAL=1 NEARPROOF_CHAIN_GEOM=ns19lb6 NEARPROOF_BASE_CLASS="$CL/$k.json" \
    taskset -c "${BASE_CPUS:-8-15,24-25}" /data/illia/nearproof-deps/bin/heavy /usr/bin/time -v \
    "$PROVER" base "$AIR" "$BB/dumps/$n" "$R" "$K/calc/dkt_certs_o2.json" "$K/lean/DKTCertsO2_big.keys" > "$R/base.log" 2>&1 || die "base $n rc=$? $(grep -h -A2 panicked "$R/base.log" | head -3 | tr '\n' ' ')"
  grep -q BASE_CLASS_HEIGHTS_OK "$R/base.log" || die "base $n: no BASE_CLASS_HEIGHTS_OK"
  local t2; t2=$(date +%s)
  printf '%s\t%s\t%s\t%s\n' "$n" "$k" $((t1 - t0)) $((t2 - t1)) > "$R/BASE_TIMES.tsv"
  echo "BASE $n class=$k dump_s=$((t1 - t0)) base_s=$((t2 - t1)) $(grep -h 'BASE_CLASS_TAPE_PAD\|BASE_CLASS_HEIGHTS_OK\|Maximum resident' "$R/base.log" | tr '\n' ' ')"
  rm -rf "$BB/dumps/$n"
}
# the D-8 class dirs: C1[k] (first member), C2[k] (second), class order
declare -A C1 C2; ORDERK=()
while read -r k n _; do
  if [ -z "${C1[$k]:-}" ]; then C1[$k]=$B8/$n; ORDERK+=("$k"); else C2[$k]=$B8/$n; fi
done < <(members)
CLASS_DIRS_PROD=""; CONFIRM_PROD=""
for k in "${ORDERK[@]}"; do CLASS_DIRS_PROD+="${C1[$k]} "; CONFIRM_PROD+="${C2[$k]:-} "; done
S1=${C1[S]}; PSETUP=$D/tree9/$(basename "$S1")/SETUP.json
for s in ${1:-1 2 3}; do case $s in
1)
  export CLASS_DIRS=$CLASS_DIRS_PROD NEARPROOF_TREE_CONFIRM=$CONFIRM_PROD
  "$HERE/run_tree.sh" tree9 - 1 "$S1" "$S1/claim.bin" || die "tree $S1"
  for c in "${C1[M]}" "${C1[L]}"; do
    "$HERE/run_tree.sh" tree9 - 1 "$c" "$c/claim.bin" "$PSETUP" || die "tree $c"
  done
  L1=${C1[L]}
  for p in "$S1 $L1" "$L1 $S1"; do set -- $p
    python3 "$HERE/tree_negatives.py" "$D/tree9/$(basename "$1")" "$1/claim.bin" "$2/claim.bin" "$D/tree9/$(basename "$2")" > "$D/tree9/$(basename "$1")/negatives.txt" 2>&1 || die "negatives $1"
    tail -1 "$D/tree9/$(basename "$1")/negatives.txt"
  done
  # tree-audit over both families' runs (each regenerates its own family's C_2 and the wrap over
  # its root); the class leaf roots from the second members (S2 M2 L2)
  # shellcheck disable=SC2086
  "$HERE/audit_d9.sh" "$D/tree9/$(basename "$S1")" $CONFIRM_PROD || die "audit S1"
  # shellcheck disable=SC2086
  SETUP=$PSETUP "$HERE/audit_d9.sh" "$D/tree9/$(basename "$L1")" $CONFIRM_PROD || die "audit L1"
  ;;
2|2base)
  export NEARPROOF_RBR_ALL=274
  for n in "$S1" "${C2[S]}"; do
    nm=$(basename "$n"); src=$(members | awk -v n="$nm" '$2 == n {print $3}')
    base S "$nm" "$src" "$D/b274"
  done
  [ "$s" = 2base ] && { unset NEARPROOF_RBR_ALL; continue; }
  export CLASS_DIRS="$D/b274/$(basename "$S1")" NEARPROOF_TREE_CONFIRM="$D/b274/$(basename "${C2[S]}")"
  OUT_ROOT=$D "$HERE/run_tree.sh" t274 - 1 "$D/b274/$(basename "$S1")" "$D/b274/$(basename "$S1")/claim.bin" || die "tree 274"
  unset NEARPROOF_RBR_ALL
  ;;
2control)
  # the 268-bit control for step 2's base time: S1's base at the pinned target, same threads as
  # the 274 bases (BASE_CPUS / BASE_THREADS)
  nm=$(basename "$S1"); src=$(members | awk -v n="$nm" '$2 == n {print $3}')
  base S "$nm" "$src" "$D/b268c"
  ;;
3base)
  # the sample's base proofs only (SAMPLE_CLASSES: e.g. "S M", default all), so they can run on
  # spare CPUs while a tree runs (L bases peak at 24 GB: not next to a tree)
  mkdir -p "$D/sample"
  [ -f "$D/sample/PICK.txt" ] || python3 "$HERE/pick_sample_d9.py" "$CL/assign.json" "$D/census" > "$D/sample/PICK.txt"
  while read -r k n src; do
    case " ${SAMPLE_CLASSES:-S M L} " in *" $k "*) base "$k" "$n" "$src" "$D/bs" < /dev/null ;; esac
  done < "$D/sample/PICK.txt"
  ;;
3)
  [ -f "$PSETUP" ] || die "no production setup $PSETUP (step 1)"
  export CLASS_DIRS=$CLASS_DIRS_PROD NEARPROOF_TREE_CONFIRM=$CONFIRM_PROD
  mkdir -p "$D/sample"
  [ -f "$D/sample/PICK.txt" ] || python3 "$HERE/pick_sample_d9.py" "$CL/assign.json" "$D/census" > "$D/sample/PICK.txt"
  cat "$D/sample/PICK.txt"
  while read -r k n src; do base "$k" "$n" "$src" "$D/bs" < /dev/null; done < "$D/sample/PICK.txt"
  while read -r k n src; do
    t0=$(date +%s)
    "$HERE/run_tree.sh" sample - 1 "$D/bs/$n" "$D/bs/$n/claim.bin" "$PSETUP" < /dev/null || die "tree $n"
    echo "SAMPLE_TREE $n class=$k tree_s=$(( $(date +%s) - t0 ))"
  done < "$D/sample/PICK.txt"
  ;;
*) die "unknown step $s" ;;
esac; done
echo D9_DONE
