#!/usr/bin/env bash
# E2E-D (D-5 .. D-8): one tree-wrap run on one chunk, then fresh-process verification and the
# soundness report of every vk involved. Fails (exit 1) on any error (review-D6 F3).
# usage: run_tree.sh TAG ARITY DEPTH CHUNK_DIR CLAIM [SETUP.json]   (ARITY - = the default, 4: D-8)
#   env: CLASS_DIRS (one base dir per template class, class order), NEARPROOF_TREE_CONFIRM (more base
#   dirs of those classes), OUT_ROOT, PROVER, NEARPROOF_TREE_TEMPLATE (base | chain), CPUSET.
# Sequential, <= 8 threads by default.
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d8}
B=${PROVER:-$D/target/release/nearproof-chunk-e2e}
K=$ROOT/research/near-compression/final-soundness
AIR=$ROOT/examples/np-udr-stark-v2/source/near-air-v3.json
TAG=$1; A=$2; DEP=$3; CH=$4; CLAIM=$5; FIX=${6:-}
export RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-8} HEAVY_MEM=${HEAVY_MEM:-40G}
export NEARPROOF_CHAIN_GEOM=ns19lb6 NEARPROOF_TAPE_EVAL=1 NEARPROOF_ZK=1 NEARPROOF_ZK_FINAL=6
export NEARPROOF_TREE_GEOM=${NEARPROOF_TREE_GEOM:-ns20lb5}
die() { echo "RUN_TREE_FAILED $*"; exit 1; }
R=${OUT_ROOT:-$D}/$TAG/$(basename "$CH")
rm -rf "$R"; mkdir -p "$R"
echo "LOAD_BEFORE $(cut -d' ' -f1-3 /proc/loadavg)"
SETUP_ENV=(); [ -n "$FIX" ] && SETUP_ENV=(NEARPROOF_TREE_SETUP="$FIX")
# shellcheck disable=SC2086
env "${SETUP_ENV[@]}" taskset -c "${CPUSET:-8-15}" /data/illia/nearproof-deps/bin/heavy /usr/bin/time -v \
  "$B" tree-prove "$AIR" "$CH/public" "$R" "$CH" "$K/calc/dkt_certs_o2.json" "$K/lean/DKTCertsO2_big.keys" "$A" "$DEP" $CLASS_DIRS \
  > "$R/prove.log" 2>&1 || die "tree-prove rc=$? ($R/prove.log: $(grep -h -A2 panicked "$R/prove.log" | head -3 | tr '\n' ' '))"
echo "TREE $(basename "$CH") $(grep -h 'TREE_FIXED_SETUP_IDENTICAL\|TREE_CHUNK_CLASS\|Maximum resident' "$R/prove.log" | tr '\n' ' ')"
if [ -n "$FIX" ]; then cmp "$FIX" "$R/SETUP.json" || die "setup differs from $FIX"; fi
for i in 1 2 3; do
  RAYON_NUM_THREADS=1 taskset -c "${VERIFY_CPU:-8}" "$B" tree-verify "$AIR" "$CLAIM" "$R/SETUP.json" "$(cat "$R/SETUP.sha256")" "$R/WRAP.bundle" > "$R/verify$i.log" 2>&1 \
    || die "tree-verify rc=$? $(tail -1 "$R/verify$i.log")"
  grep -h "VERIFY_PROFILE_MS\|INDEPENDENT_TREE_VERIFY_OK" "$R/verify$i.log"
done
# soundness of the wrap vk (SETUP.json), the tree vks, and every class's base vk (review-D6 F3)
VKS=("$R/SETUP.json" "$R/LEAF.vk.json" "$R/NODE.vk.json")
for c in $CLASS_DIRS; do VKS+=("$c/BASE.vk.json"); done
"$B" soundness "${VKS[@]}" > "$R/soundness.txt" 2>&1 || die "soundness rc=$?"
grep -c SOUNDNESS_BITS "$R/soundness.txt" | grep -qx "${#VKS[@]}" || die "soundness report incomplete"
echo "LOAD_AFTER $(cut -d' ' -f1-3 /proc/loadavg)"
echo "TREE_RUN_OK $R"
