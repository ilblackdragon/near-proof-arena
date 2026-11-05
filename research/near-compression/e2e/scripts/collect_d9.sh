#!/usr/bin/env bash
# Collect the D-9 runs (pq-e2e-d9) into results/zk/d9/ (small files only; proofs and setups stay in
# the deps tree, hashed in manifest.sha256), then write results/zk/d9/SHA256SUMS.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d9}
O=$HERE/../results/zk/d9
mkdir -p "$O"
tree_dir() { # RUN_DIR OUT_DIR
  local r=$1 t=$2
  [ -f "$r/RESULT.json" ] || return 0
  mkdir -p "$t"
  for f in RESULT.json NEGATIVES.json SETUP.sha256 soundness.txt negatives.txt audit.txt; do [ -f "$r/$f" ] && cp "$r/$f" "$t/"; done
  (cd "$r" && sha256sum SETUP.json WRAP.bundle WRAP.proof ./*.vk.json) > "$t/manifest.sha256"
  grep -h "TREE_PARAMS\|TREE_LEAF_PARAMS\|TREE_SHAPE\|TREE_LEAF_FAMIL\|TREE_TEMPLATE\|TREE_CLASS_KEY\|TREE_CHUNK_CLASS\|TREE_PAD_LEAF\|TREE_LEAF\|TREE_FAMILY\|TREE_NODE\|TREE_PAD_NODE\|WRAP_SHAPE_PIN\|WRAP_NEGATIVE\|TREE_FIXED_SETUP_IDENTICAL\|Maximum resident\|Elapsed" "$r/prove.log" | cut -c1-600 > "$t/prove_summary.txt"
  cat "$r"/verify*.log | grep -h "VERIFY_PROFILE_MS\|INDEPENDENT_TREE_VERIFY_OK" > "$t/verify.txt"
}
base_dir() { # BASE_DIR OUT_FILE
  local b=$1
  { grep -h "BASE_CLASS_TAPE_PAD\|BASE_CLASS_HEIGHTS_OK\|BASE_VERIFIED\|PRECHECK\|CELLS\|BASE_PROOF\|Elapsed\|Maximum resident" "$b/base.log"
    [ -f "$b/BASE_TIMES.tsv" ] && cat "$b/BASE_TIMES.tsv"
    (cd "$b" && sha256sum BASE.proof BASE.vk.json TAPE_PAD.json); } > "$2"
}
# 1. production setup (families) + negatives + audits
for r in "$D"/tree9/*/; do tree_dir "$r" "$O/tree9/$(basename "$r")"; done
# 2. every layer at the 274-bit per-round target
for r in "$D"/t274/*/; do tree_dir "$r" "$O/t274/$(basename "$r")"; done
mkdir -p "$O/t274"
for b in "$D"/b274/d1_*/; do [ -f "$b/BASE.proof" ] && base_dir "$b" "$O/t274/$(basename "$b").base.txt"; done
for b in "$D"/b268c/d1_*/; do [ -f "$b/BASE.proof" ] && base_dir "$b" "$O/t274/$(basename "$b").base268-control.txt"; done
# 3. throughput sample
if [ -d "$D/sample" ]; then
  mkdir -p "$O/sample"
  cp "$D/sample/PICK.txt" "$O/sample/"
  for r in "$D"/sample/*/; do tree_dir "$r" "$O/sample/$(basename "$r")"; done
  for b in "$D"/bs/d*/; do [ -f "$b/BASE.proof" ] && base_dir "$b" "$O/sample/$(basename "$b").base.txt"; done
  [ -f "$D/sample/TIMES.tsv" ] && cp "$D/sample/TIMES.tsv" "$O/sample/"
fi
# tests, tamper fixtures, run logs
mkdir -p "$O/tests"
for f in tree_d9_wrap_set_debug agg-tree; do
  [ -f "$D/tests9/$f.log" ] && grep -h "TREE_D9\|test result\|Elapsed\|Maximum resident" "$D/tests9/$f.log" | cut -c1-300 > "$O/tests/$f.txt"
done
cp "$D/tests9.log" "$O/tests/tests_d9.txt"
if [ -d "$D/tamper9" ]; then
  mkdir -p "$O/tamper"
  for f in control vkweak padkeys; do [ -f "$D/tamper9/$f.txt" ] && cp "$D/tamper9/$f.txt" "$O/tamper/$f.audit.txt"; done
  grep -h "TREE_CLASS_KEY\|panicked\|base vk differs" "$D/tamper9/base0.log" | cut -c1-300 > "$O/tamper/base0.prove.txt"
  [ -f "$D/tamper9.txt" ] && cp "$D/tamper9.txt" "$O/tamper/tamper_d9.txt"
fi
for f in run_d9_1.log run_d9_2.log run_d9_3.log run_d9_bases.log; do [ -f "$D/$f" ] && cut -c1-400 "$D/$f" > "$O/${f%.log}.txt"; done
"$HERE/sha256sums.sh" write "$O"
"$HERE/sha256sums.sh" check "$O"
echo "COLLECTED $O"
