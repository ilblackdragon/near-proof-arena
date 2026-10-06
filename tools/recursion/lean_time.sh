#!/bin/bash
# Re-time the deployed Lean verifier model (np-lean-verify) on stored proofs, one core,
# min of 3 runs; one TSV row per proof with the AIR shape features.
# usage: lean_time.sh <out.tsv> <air.json> <pub.bin> <claim.bin> <proof.bin> <label>
set -u
out=$1 air=$2 pub=$3 cl=$4 pf=$5 label=$6
: "${LV:?set LV}" "${R1CALIB:?set R1CALIB}" ; CPU=${CPU:-9}
[ -f "$out" ] || printf "label\tproof_B\tlean_ms_min\tntables\tood\tconstraints\taux\tquot\twidth\n" > "$out"
best=999999999
for r in 1 2 3; do
  ms=$(taskset -c $CPU "$LV" "$air" "$pub" "$cl" "$pf" 2>&1 >/dev/null | grep -o 'wall [0-9]*' | awk '{print $2}')
  [ -n "$ms" ] && [ "$ms" -lt "$best" ] && best=$ms
done
read nt ood cons aux quot w < <("$R1CALIB" shape "$air" | python3 -c "
import sys,json
t=[json.loads(l) for l in sys.stdin]
print(len(t), sum(2*x['width']+2*x['aux']+x['quot'] for x in t), sum(x['constraints'] for x in t), sum(x['aux'] for x in t), sum(x['quot'] for x in t), sum(x['width'] for x in t))")
printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "$label" "$(stat -c%s "$pf")" "$best" "$nt" "$ood" "$cons" "$aux" "$quot" "$w" | tee -a "$out"
