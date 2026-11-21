#!/usr/bin/env bash
# E2E-D M8 prototype: a heterogeneous tree over T1-shaped segments.
#   run_m8.sh STAGE WORK      stages (in order): a | b | spec | tree | verify | all
#   a      lane A: T1's Wasm call cut into segments by lane A's prover (m8_laneA.sh), each segment
#          proved under the verifier's backend at the stack's base configuration (m8-prove-a)
#   b      lane B: T1's M5b state dump (lane B's tracegen.py on lane B's T1 state.json, AIR from
#          main's m5a-tool airb 5), proved the same way (m8-prove-b)
#   spec   the tree spec (m8_spec.py): record layout, templates INIT / WASM / STATE / FINAL, S
#   tree   m8-tree (leaves, P_2, P_*, PAD, wrap)
#   verify m8-verify in fresh processes (3x) + negatives (tampered statement / proof / pin)
# env: CPUSET (default 4-11), THREADS (8), GEOM (template geometry, ns18lb7), ARITY / DEPTH (4 / 2)
set -euo pipefail
. "$(cd "$(dirname "$0")" && pwd)/env_d9.sh"
D=/data/illia/nearproof-deps/pq-e2e-m8
P=$D/target/release/nearproof-chunk-e2e
S=$(cd "$(dirname "$0")" && pwd)
STAGE=${1:?stage}; O=${2:?work dir}
mkdir -p "$O"
C=${CPUSET:-4-11}; TH=${THREADS:-8}
CERTS=$K/calc/dkt_certs_o2.json; EXCL=$K/lean/DKTCertsO2_big.keys
die() { echo "RUN_M8_FAILED $*"; exit 1; }
run() { RAYON_NUM_THREADS=$TH /usr/bin/time -v taskset -c "$C" "$@"; }
stage_a() {
  CPUSET=$C "$S/m8_laneA.sh" "$O/laneA" "${K_STEPS:-13}" || die "lane A dumps"
  for f in "$O"/laneA/seg-*.bin; do
    i=$(basename "$f" .bin); i=${i#seg-}
    run "$P" m8-prove-a "$O/laneA/airSeg.json" "$f" "$O/tmpl/wasm$i" "$CERTS" "$EXCL" "${GEOM:-ns18lb7}" > "$O/tmpl-wasm$i.log" 2>&1 || die "m8-prove-a $i"
    grep -h M8_TEMPLATE_PROVED "$O/tmpl-wasm$i.log"
  done
}
stage_b() {
  B=$O/laneB; mkdir -p "$B"
  M5A=$W/research/near-compression/e2e-general/m5a
  cp "${T1_STATE:-/data/illia/nearproof-deps/e2e-m5a6/b1/state.json}" "$B/state.json"
  "${M5A_TOOL:-/data/illia/nearproof/research/near-compression/e2e-general/m5a/lean/.lake/build/bin/m5a-tool}" airb 5 "$B/m5a.json" "$B/names.json" > "$B/air.txt"
  WANT=$(python3 -c "import json,sys; print(json.load(open(sys.argv[1]))['post_root'])" "$B/state.json")
  GOT=$("${M5A_TOOL:-/data/illia/nearproof/research/near-compression/e2e-general/m5a/lean/.lake/build/bin/m5a-tool}" apply "$B/state.json")
  [ "$GOT" = "$WANT" ] || die "lane B spec oracle: $GOT != $WANT"
  python3 "$M5A/tracegen.py" "$B/state.json" "$B/names.json" "$B/dump" > "$B/gen.txt" || die "lane B tracegen"
  cat "$B/gen.txt"
}
stage_b_prove() {
  B=$O/laneB
  run "$P" m8-prove-b "$B/m5a.json" "$B/dump" "$O/tmpl/state" "$CERTS" "$EXCL" "${GEOM:-ns18lb7}" > "$O/tmpl-state.log" 2>&1 || die "m8-prove-b"
  grep -h M8_TEMPLATE_PROVED "$O/tmpl-state.log"
}
stage_spec() {
  python3 "$S/m8_spec.py" "$O" "${ARITY:-4}" "${DEPTH:-2}" > "$O/spec.txt" || die "spec"
  cat "$O/spec.txt"
}
stage_tree() {
  run "$P" m8-tree "$O/spec.json" "$O/tree" "$CERTS" "$EXCL" > "$O/tree.log" 2>&1 || die "m8-tree rc=$? ($(grep -h -A2 panicked "$O/tree.log" | head -3 | tr '\n' ' '))"
  grep -hE "M8_CHAIN_OK|M8_TEMPLATE_SET|M8_LEAF_GEOM|M8_NODE_GEOM|M8_WRAP_NEGATIVE" "$O/tree.log"
}
stage_verify() {
  T=$O/tree; PIN=$(cat "$T/SETUP.sha256")
  : > "$O/verify.txt"
  for r in 1 2 3; do
    RAYON_NUM_THREADS=1 /usr/bin/time -v taskset -c "${C%%-*}" "$P" m8-verify "$T/SETUP.json" "$PIN" "$T/WRAP.bundle" > "$O/verify$r.log" 2>&1 || die "verify $r"
    grep -hE "VERIFY_PROFILE_MS|INDEPENDENT_HTREE_VERIFY_OK|Maximum resident" "$O/verify$r.log" | tee -a "$O/verify.txt"
  done
  python3 "$S/m8_negatives.py" "$P" "$T" "$O/neg" | tee "$O/negatives.txt"
  grep -q "M8_NEGATIVES_ALL_REJECTED" "$O/negatives.txt" || die "a negative was accepted"
}
case $STAGE in
  a) stage_a ;; b) stage_b; stage_b_prove ;; b-dump) stage_b ;; b-prove) stage_b_prove ;; spec) stage_spec ;; tree) stage_tree ;; verify) stage_verify ;;
  all) stage_a; stage_b; stage_b_prove; stage_spec; stage_tree; stage_verify ;;
  *) die "unknown stage $STAGE" ;;
esac
echo "RUN_M8_STAGE_OK $STAGE"
