#!/usr/bin/env bash
# E2E-D D-6: copy the shape-floored class chains' summaries into the repo (no proofs; sha256 only).
# usage: collect_classes.sh CLASS_ROOT DEST_DIR [RUN_LOG]
set -euo pipefail
SRC=$1; DST=$2
mkdir -p "$DST"
for r in "$SRC"/*/; do
  c=$(basename "$r"); o=$DST/$c; mkdir -p "$o"
  for f in RESULT.json SETUP.sha256; do [ -f "$r/$f" ] && cp "$r/$f" "$o/"; done
  grep -hE "SHAPE_FLOOR|_ANCHOR|_VERIFIED|FINAL_SHAPE_PIN|FINAL_PINNED|FINAL_PHASE|Maximum resident|Elapsed" "$r/chain.log" 2>/dev/null | cut -c1-600 > "$o/chain_summary.txt" || true
  (cd "$r" && sha256sum SETUP.json FINAL.bundle L4.proof L4.vk.json BASE.proof BASE.vk.json 2>/dev/null) > "$o/manifest.sha256" || true
done
[ $# -ge 3 ] && cp "$3" "$DST/run_classes.log"
ls -R "$DST" | head -20
