#!/usr/bin/env bash
# Copy the D-5 run summaries into the repo (no proofs, no setups: their sha256 are in manifest).
# usage: collect_tree.sh SRC_DIR DEST_DIR      e.g. pq-e2e-d5/tree-a2d1 results/zk/tree-a2d1
set -euo pipefail
SRC=$1; DST=$2
mkdir -p "$DST"
for r in "$SRC"/*/; do
  c=$(basename "$r"); o=$DST/$c; mkdir -p "$o"
  for f in RESULT.json SETUP.sha256 NEGATIVES.json soundness.txt; do [ -f "$r/$f" ] && cp "$r/$f" "$o/"; done
  grep -hE "TREE_|WRAP_|FINAL_SHAPE_PIN|NV_GEN profile|Maximum resident|Elapsed|User time|INDEPENDENT|VERIFY_PROFILE|panicked" "$r/prove.log" 2>/dev/null | cut -c1-2000 > "$o/prove_summary.txt" || true
  (cd "$r" && sha256sum SETUP.json *.bundle *.proof *.vk.json 2>/dev/null) > "$o/manifest.sha256" || true
done
ls -R "$DST" | head -40
