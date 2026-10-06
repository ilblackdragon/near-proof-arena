#!/bin/bash
# R1 calibration sweep (docs/research/recursion-r1-cost.md §3).
# usage: calib.sh <tag> "<S list>" <log_h> <widths> [k]
#   runs r1calib seg for each S (one at a time, CPUs 8-15, 8 rayon threads,
#   under the heavy wrapper), then the deployed-model Lean verifier
#   (np-lean-verify) on the proof; appends a TSV row per run to
#   results/<tag>.tsv. Peak RSS from /usr/bin/time -v.
# env: R1CALIB (binary), LV (np-lean-verify), WORK (scratch dir), HEAVY_MEM.
set -u
here="$(cd "$(dirname "$0")" && pwd)"
tag=$1; Ss=$2; logh=$3; widths=$4; k=${5:-8}
B=${R1CALIB:?set R1CALIB to the built r1calib binary}
LV=${LV:?set LV to an np-lean-verify binary}
WORK=${WORK:?set WORK to a scratch dir}
out="$here/results/$tag.tsv"
[ -f "$out" ] || printf "S\tlog_h\twidths\tk\tproof_B\tprove_s\trust_verify_s\tlean_verify_ms\tpeak_rss_MB\tood\tfinals\ttables\tcells\n" > "$out"
for S in $Ss; do
  d="$WORK/$tag-S$S"; rm -rf "$d"; mkdir -p "$d"
  RAYON_NUM_THREADS=8 HEAVY_MEM=${HEAVY_MEM:-20G} taskset -c 8-15 /data/illia/nearproof-deps/bin/heavy \
    /usr/bin/time -v "$B" seg "$S" "$logh" "$widths" --k "$k" --out "$d" >"$d/seg.out" 2>"$d/seg.err"
  line=$(grep '^seg ' "$d/seg.out")
  [ -z "$line" ] && { echo "S=$S failed: $(tail -3 $d/seg.err)"; continue; }
  get() { echo "$line" | grep -o "$1=[^ ]*" | head -1 | cut -d= -f2 | tr -d 'sB'; }
  rss=$(grep "Maximum resident" "$d/seg.err" | awk '{print int($6/1024)}')
  lv=$(taskset -c 8-15 "$LV" "$d/air.json" "$d/pub.bin" "$d/claim.bin" "$d/proof.bin" 2>&1 >/dev/null | grep -o 'wall [0-9]*' | awk '{print $2}')
  acc=$(taskset -c 8-15 "$LV" "$d/air.json" "$d/pub.bin" "$d/claim.bin" "$d/proof.bin" 2>/dev/null)
  printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "$S" "$logh" "$widths" "$k" \
    "$(echo "$line" | grep -o 'proof=[0-9]*' | cut -d= -f2)" "$(get prove)" "$(get verify_rust)" "${lv}${acc:+ }${acc}" \
    "$rss" "$(get ood)" "$(get finals)" "$(get tables)" "$(get cells)" | tee -a "$out"
  rm -f "$d/proof.bin.keep"
done
