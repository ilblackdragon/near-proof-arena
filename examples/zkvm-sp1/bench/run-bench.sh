#!/usr/bin/env bash
# Local measurement (NOT judge-measured): bench/run-bench.sh <out-dir> <params.bin> <work-dir> <case-dir>...
# For each case: prove (wall, peak RSS), claim == expected, proof bytes, verify x5 (median wall, peak RSS).
set -uo pipefail
OUT=$1; PARAMS=$2; WORK=$3; shift 3
mkdir -p "$WORK"
"$OUT/prepare" --params "$PARAMS" --out "$WORK/public" 2>/dev/null || { echo "prepare failed"; exit 2; }
echo -e "case\treceipts\twitness_bytes\tprove_s\tprove_peak_rss_mb\tclaim_ok\tproof_bytes\tverify_ms_median\tverify_peak_rss_mb\tloadavg1"
for c in "$@"; do
  name=$(basename "$c")
  want="$c/expected_claim.bin"; [ -f "$want" ] || want="$c/claim.bin"
  n=$(python3 -c "import struct,sys;b=open('$c/request.bin','rb').read();i=0
def by():
  global i;l=struct.unpack_from('<I',b,i)[0];i+=4+l
by();by();i+=4;by();i+=8+8+16+8+32;print(struct.unpack_from('<I',b,i)[0])")
  wb=$(python3 -c "import struct;b=open('$c/witness.bin','rb').read();i=4+struct.unpack_from('<I',b,0)[0]+32+1;m=struct.unpack_from('<I',b,i)[0];i+=4;t=0
for _ in range(m):
  l=struct.unpack_from('<I',b,i)[0];i+=4+l;t+=l
print(t)")
  load=$(cut -d' ' -f1 /proc/loadavg)
  /usr/bin/time -f "%e %M" -o "$WORK/$name.ptime" "$OUT/prove" --public "$WORK/public" --request "$c/request.bin" --witness "$c/witness.bin" \
      --claim-out "$WORK/$name.claim" --proof-out "$WORK/$name.proof" > "$WORK/$name.prove.log" 2>&1
  read pw prss < "$WORK/$name.ptime"
  ok=false; cmp -s "$WORK/$name.claim" "$want" && ok=true
  pb=$(stat -c %s "$WORK/$name.proof" 2>/dev/null || echo 0)
  vts=()
  for i in 1 2 3 4 5; do
    /usr/bin/time -f "%e %M" -o "$WORK/$name.vtime" "$OUT/verify" --public "$WORK/public" --claim "$WORK/$name.claim" --proof "$WORK/$name.proof" 2>/dev/null
    rc=$?; [ $rc -eq 0 ] || ok="false(verify rc=$rc)"
    read vw vrss < "$WORK/$name.vtime"; vts+=("$vw")
  done
  vmed=$(printf '%s\n' "${vts[@]}" | sort -n | sed -n 3p)
  echo -e "$name\t$n\t$wb\t$pw\t$((prss/1024))\t$ok\t$pb\t$(python3 -c "print(int(float('$vmed')*1000))")\t$((vrss/1024))\t$load"
done
