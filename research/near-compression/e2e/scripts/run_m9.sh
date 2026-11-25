#!/usr/bin/env bash
# E2E-D M9: the heterogeneous T1 tree over real leaves only (lanes G, B, F, A), arity 4, depth 2.
#   run_m9.sh STAGE WORK     stages: import | spec | check | swap | tree | verify
#   import  m9_import.sh (every lane's saved leaf, verified natively, INFO.json)
#   spec    m9_spec.py (record regions, templates, free / dropped cells, native chain)
#   check   M8_CHECK_ONLY=1: the driver's native chain + leaf program probes, no proof
#   swap    M9_SWAP_STUB=0,5,7: each of INIT / RT_RESUME / FINAL replaced by a stub exposing the same
#           statement; P_2 with the run's template set must refuse it (M8_REUSE=WORK/tree reuses the leaves)
#   tree    m8-tree (leaves, P_2, PAD_N, P_*, wrap), every prover under `heavy` (HEAVY_MEM, default 20G),
#           streamed commitments (NEARPROOF_STREAM_COMMIT=1), M8_REUSE=$REUSE if set
#   verify  m8-verify in fresh processes (3x, 1 core) + m8_negatives.py + m9_negatives.py
# env: PROVER, CPUSET (4-11), THREADS (8), HEAVY_MEM (20G), REUSE
set -euo pipefail
. "$(cd "$(dirname "$0")" && pwd)/env_d9.sh"
P=${PROVER:-/data/illia/nearproof-deps/tmp-laneD/drv4/release/nearproof-chunk-e2e}
S=$(cd "$(dirname "$0")" && pwd)
STAGE=${1:?stage}; O=${2:?work dir}
mkdir -p "$O"
C=${CPUSET:-4-11}; TH=${THREADS:-8}
CERTS=$K/calc/dkt_certs_o2.json; EXCL=$K/lean/DKTCertsO2_big.keys
export NEARPROOF_CHAIN_GEOM=ns19lb6 NEARPROOF_TAPE_EVAL=1 NEARPROOF_ZK=1 NEARPROOF_ZK_FINAL=6 NEARPROOF_TREE_GEOM=ns20lb5
export NEARPROOF_STREAM_COMMIT=${NEARPROOF_STREAM_COMMIT:-1} NEARPROOF_MEMPROF=${NEARPROOF_MEMPROF:-1}
die() { echo "RUN_M9_FAILED $*"; exit 1; }
heavy() { HEAVY_MEM=${HEAVY_MEM:-20G} RAYON_NUM_THREADS=$TH /data/illia/nearproof-deps/bin/heavy /usr/bin/time -v taskset -c "$C" "$@"; }
case $STAGE in
  import) PROVER=$P "$S/m9_import.sh" "$O" || die import ;;
  spec) python3 "$S/m9_spec.py" "$O" "${ARITY:-4}" "${DEPTH:-2}" > "$O/spec.txt" || die spec; cat "$O/spec.txt" ;;
  check) M8_CHECK_ONLY=1 heavy "$P" m8-tree "$O/spec.json" "$O/tree-check" "$CERTS" "$EXCL" > "$O/check.log" 2>&1 || die "check ($(grep -h -A2 panicked "$O/check.log" | head -3 | tr '\n' ' '))"
         grep -hE "M8_CHAIN_OK|M8_LEAF_PROBE|M8_LEAF_GEOM|Maximum resident" "$O/check.log"; rm -rf "$O/tree-check" ;;
  swap) M9_SWAP_STUB=${SWAP:-0,5,7} M8_REUSE=${REUSE:-$O/tree} heavy "$P" m8-tree "$O/spec.json" "$O/tree-swap" "$CERTS" "$EXCL" > "$O/swap.log" 2>&1 || die "swap ($(grep -h -A2 panicked "$O/swap.log" | head -3 | tr '\n' ' '))"
        grep -hE "M9_|M8_REUSE|Maximum resident|Elapsed" "$O/swap.log"; grep -q M9_SWAP_STUB_ALL_REFUSED "$O/swap.log" || die "a stub was accepted"; rm -rf "$O/tree-swap" ;;
  tree) if [ -n "${REUSE:-}" ]; then export M8_REUSE=$REUSE; fi; heavy "$P" m8-tree "$O/spec.json" "$O/tree" "$CERTS" "$EXCL" > "$O/tree.log" 2>&1 || die "tree rc=$? ($(grep -h -A2 panicked "$O/tree.log" | head -3 | tr '\n' ' '))"
        grep -hE "M8_CHAIN_OK|M8_TEMPLATE_SET|M8_LEAF_GEOM|M8_NODE_GEOM|M8_WRAP_NEGATIVE|Maximum resident|Elapsed" "$O/tree.log" ;;
  verify)
    T=$O/tree; PIN=$(cat "$T/SETUP.sha256"); : > "$O/verify.txt"
    for r in 1 2 3; do
      RAYON_NUM_THREADS=1 /usr/bin/time -v taskset -c "${C%%-*}" "$P" m8-verify "$T/SETUP.json" "$PIN" "$T/WRAP.bundle" > "$O/verify$r.log" 2>&1 || die "verify $r"
      grep -hE "VERIFY_PROFILE_MS|INDEPENDENT_HTREE_VERIFY_OK|Maximum resident" "$O/verify$r.log" | tee -a "$O/verify.txt"
    done
    python3 "$S/m8_negatives.py" "$P" "$T" "$O/neg" | tee "$O/negatives.txt"
    grep -q "M8_NEGATIVES_ALL_REJECTED" "$O/negatives.txt" || die "a negative was accepted"
    python3 "$S/m9_negatives.py" "$P" "$T" "$O/neg9" | tee "$O/negatives9.txt"
    grep -q "M9_NEGATIVES_ALL_REJECTED" "$O/negatives9.txt" || die "an M9 negative was accepted" ;;
  *) die "unknown stage $STAGE" ;;
esac
echo "RUN_M9_STAGE_OK $STAGE"
