#!/usr/bin/env bash
# Per-workload benchmark of the np-udr-stark NEAR prover against the
# challenge caps (prove ≤ 600 s, RAM ≤ 16 GiB, proof ≤ 8 MiB, verify ≤ 10 s).
#
#   bench/near-bench.sh <cases-dir>... 
#
# Each <cases-dir> holds case directories with request.bin, witness.bin and
# expected_claim.bin (oracle `gen --fixtures-layout` output, e.g.
# oracle/fixtures/public/cases). For each case: `prove` (8 threads, under the
# heavy wrapper, /usr/bin/time -v), claim == expected_claim, Rust reference
# verify, and — if conformance/.lake/build/bin/np-lean-verify exists — the
# compiled Lean verifier (accept + wall time). One TSV line per case.
set -u
here="$(cd "$(dirname "$0")/.." && pwd)"
src="$here/source"
HEAVY=${HEAVY:-/data/illia/nearproof-deps/bin/heavy}
export RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-8}
prove="$src/target/release/prove"
npudr="$src/target/release/npudr"
lv="$here/conformance/.lake/build/bin/np-lean-verify"
air="$src/near-air.json"
work=$(mktemp -d)
pubdir="$work/public"; mkdir -p "$pubdir"
cp "${PUBLIC_BIN:-$here/../../oracle/fixtures/public/params.bin}" "$pubdir/public.bin"
printf "case\tn\tprove_s\tmaxrss_MB\tproof_B\tclaim\trust_verify\tlean_verify\tlean_ms\n"
for root in "$@"; do
  for d in "$root"/*/; do
    c=$(basename "$d")
    [ -f "$d/request.bin" ] || continue
    rm -f "$work/claim.bin" "$work/proof.bin"
    $HEAVY /usr/bin/time -v -o "$work/time" "$prove" --public "$pubdir" --request "$d/request.bin" \
      --witness "$d/witness.bin" --claim-out "$work/claim.bin" --proof-out "$work/proof.bin" 2>"$work/err" >/dev/null
    rc=$?
    secs=$(grep "Elapsed (wall" "$work/time" | awk '{print $NF}' | awk -F: '{ if (NF==2) print $1*60+$2; else print $1*3600+$2*60+$3 }')
    rss=$(grep "Maximum resident" "$work/time" | awk '{printf "%.0f", $NF/1024}')
    if [ $rc -ne 0 ]; then printf "%s\t-\t%s\t%s\tFAIL(%s)\t-\t-\t-\t-\n" "$c" "$secs" "$rss" "$(tail -1 "$work/err")"; continue; fi
    n=$(stat -c %s "$work/proof.bin")
    cl=$(cmp -s "$work/claim.bin" "$d/expected_claim.bin" && echo ok || echo DIFF)
    rv=$("$npudr" verify "$air" "$pubdir/public.bin" "$work/claim.bin" "$work/proof.bin" | head -1)
    lvr=-; lms=-
    if [ -x "$lv" ]; then
      lvr=$(HEAVY_MEM=4G $HEAVY "$lv" "$air" "$pubdir/public.bin" "$work/claim.bin" "$work/proof.bin" 2>"$work/lerr")
      lms=$(grep -o 'wall [0-9]* ms' "$work/lerr" | awk '{print $2}')
    fi
    nr=$(python3 -c "import sys,struct;b=open('$d/request.bin','rb').read();o=0
def s(o):return o+4+struct.unpack_from('<I',b,o)[0]
o=s(s(0));o+=4;o=s(o);o+=8+8+16+8+32;print(struct.unpack_from('<I',b,o)[0])")
    printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "$c" "$nr" "$secs" "$rss" "$n" "$cl" "$rv" "$lvr" "$lms"
  done
done
rm -rf "$work"
