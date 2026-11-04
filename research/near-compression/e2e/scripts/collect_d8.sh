#!/usr/bin/env bash
# Collect the D-8 runs (pq-e2e-d8) into results/zk/d8/ (small files only; proofs and setups stay in
# the deps tree, hashed in manifest.sha256).
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d8}
O=$HERE/../results/zk/d8
mkdir -p "$O/classes" "$O/tree8" "$O/leaf"
# census + classes + coverage
python3 "$HERE/census_stats_d8.py" "$D/census" > "$O/classes/census_stats.txt"
cp "$D/classes8.txt" "$O/classes/classes.txt"
cp "$D"/classes8/{S,M,L}.json "$O/classes/"
python3 - "$D/classes8/assign.json" > "$O/classes/assign_summary.json" <<'EOF'
import json, sys, collections
a = json.load(open(sys.argv[1]))
print(json.dumps({'census': a['census'], 'headroom': a['headroom'], 'cuts': a['cuts'], 'classes': a['classes'],
                  'members': dict(collections.Counter(a['assign'].values())), 'uncovered': a['uncovered'],
                  'assign': a['assign']}, indent=0))
EOF
[ -f "$D/cover.txt" ] && cp "$D/cover.txt" "$O/classes/cover_done.txt"
if [ -d "$D/cover" ]; then
  cat "$D"/cover/*.ok 2>/dev/null | awk '{$1=""; print}' | sort | uniq -c > "$O/classes/cover_growth.txt"
  ls "$D"/cover/*.ok | wc -l > "$O/classes/cover_ok_count.txt"
  grep -h COVER_FAIL "$D/cover/cover.txt" > "$O/classes/cover_fail.txt" 2>/dev/null || true
fi
# base proofs
for b in "$D"/b8/d1_*/; do
  n=$(basename "$b"); grep -h "BASE_CLASS_TAPE_PAD\|BASE_CLASS_HEIGHTS_OK\|BASE_VERIFIED\|PRECHECK\|CELLS\|BASE_PROOF\|Elapsed\|Maximum resident" "$b/base.log" > "$O/classes/$n.base.txt"
  (cd "$b" && sha256sum BASE.proof BASE.vk.json TAPE_PAD.json) >> "$O/classes/$n.base.txt"
done
# trees
for r in "$D"/tree8/*/; do
  [ -f "$r/RESULT.json" ] || continue
  t="$O/tree8/$(basename "$r")"; mkdir -p "$t"
  for f in RESULT.json NEGATIVES.json SETUP.sha256 soundness.txt negatives.txt audit.txt audit_negative_swapped_vk.txt; do [ -f "$r/$f" ] && cp "$r/$f" "$t/"; done
  (cd "$r" && sha256sum SETUP.json WRAP.bundle WRAP.proof ./*.vk.json) > "$t/manifest.sha256"
  grep -h "TREE_PARAMS\|TREE_LEAF_PARAMS\|TREE_SHAPE\|TREE_TEMPLATE\|TREE_CHUNK_CLASS\|TREE_PAD_LEAF\|TREE_LEAF\|TREE_NODE\|TREE_PAD_NODE\|WRAP_SHAPE_PIN\|WRAP_NEGATIVE\|TREE_FIXED_SETUP_IDENTICAL\|Maximum resident\|Elapsed" "$r/prove.log" | cut -c1-600 > "$t/prove_summary.txt"
  cat "$r"/verify*.log 2>/dev/null | grep -h "VERIFY_PROFILE_MS\|INDEPENDENT_TREE_VERIFY_OK" > "$t/verify.txt"
done
# leaf measurements
for l in "$D"/leafab/leaf-* "$D"/leafL/leaf-*; do
  [ -f "$l/prove.log" ] || continue
  grep -h "TREE_LEAF_PARAMS\|TREE_TEMPLATE\|NV_QCOST\|NV_PHASE\|TREE_LEAF 0\|TREE_LEAF_ONLY_DONE\|Maximum resident\|Elapsed" "$l/prove.log" | cut -c1-400 > "$O/leaf/$(basename "$(dirname "$l")")-$(basename "$l").txt"
done
cp "$D/leafab.log" "$O/leaf/leafab.log"; cp "$D/leafL.log" "$O/leaf/leafL.log"
# constraint-level tests (tests_d8.sh)
mkdir -p "$O/tests"
for f in review_d7_mixup_debug tree_d7_shapes_debug agg-tree; do
  [ -f "$D/tests/$f.log" ] && grep -h "REVIEW_D7\|TREE_D7\|test result\|Elapsed\|Maximum resident" "$D/tests/$f.log" | cut -c1-300 > "$O/tests/$f.txt"
done
echo "COLLECTED $O"
