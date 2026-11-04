#!/usr/bin/env bash
# Collect the D-7 runs (pq-e2e-d7) into results/zk/d7/ (small files only: results, logs' summary
# lines, manifests; proofs and setups stay in the deps tree, hashed in manifest.sha256).
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d7}
O=$HERE/../results/zk/d7
mkdir -p "$O"
for r in "$D"/tree-a*/*/; do
  [ -f "$r/RESULT.json" ] || continue
  t="$O/$(basename "$(dirname "$r")")/$(basename "$r")"; mkdir -p "$t"
  for f in RESULT.json NEGATIVES.json SETUP.sha256 soundness.txt negatives.txt; do [ -f "$r/$f" ] && cp "$r/$f" "$t/"; done
  (cd "$r" && sha256sum SETUP.json WRAP.bundle WRAP.proof ./*.vk.json) > "$t/manifest.sha256"
  grep -h "TREE_PARAMS\|TREE_TEMPLATE\|TREE_CHUNK_CLASS\|TREE_PAD_LEAF\|TREE_LEAF\|TREE_NODE\|TREE_PAD_NODE\|TREE_STAR_PROBE\|WRAP_SHAPE_PIN\|WRAP_NEGATIVE\|TREE_FIXED_SETUP_IDENTICAL\|Maximum resident\|Elapsed" "$r/prove.log" | cut -c1-600 > "$t/prove_summary.txt"
  cat "$r"/verify*.log 2>/dev/null | grep -h "VERIFY_PROFILE_MS\|INDEPENDENT_TREE_VERIFY_OK" > "$t/verify.txt"
done
[ -f "$D/tree-a2d3-A2-templates/prove.log" ] && grep -h "TREE_CHUNK_CLASS\|TREE_TEMPLATES_MATCH_FIXED_SETUP\|TREE_TEMPLATE " "$D/tree-a2d3-A2-templates/prove.log" > "$O/a2d3-A2-templates.txt"
# base shape classes
mkdir -p "$O/classes"
cp "$D"/bclass/{A,B,A0,B0}.json "$D"/bclass/{A,B}.shapes.txt "$O/classes/" 2>/dev/null
for b in "$D"/bclass/d1_*/; do
  n=$(basename "$b"); grep -h "BASE_CLASS_HEIGHTS_OK\|BASE_VERIFIED\|PRECHECK\|Elapsed\|Maximum resident" "$b/base.log" > "$O/classes/$n.base.txt"
  (cd "$b" && sha256sum BASE.proof BASE.vk.json) >> "$O/classes/$n.base.txt"
done
for c in "$D"/bclass/dumps/*.log; do grep -h "statedump:" "$c" > "$O/classes/statedump-$(basename "$c")" 2>/dev/null || true; done
python3 "$D/work/classgroups.py" "$D/bclass/scan" > "$O/classes/classgroups.txt"
cp "$D/work/classgroups.py" "$HERE/classgroups.py"
for f in test-d7.log test-agg.log; do [ -f "$D/work/$f" ] && grep -h "TREE_D7\|test result\|Elapsed\|Maximum resident\|panicked" "$D/work/$f" > "$O/${f%.log}.txt"; done
echo "COLLECTED $O"
