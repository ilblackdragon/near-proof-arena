#!/usr/bin/env bash
# nearcore per-outcome observables for the pinned d1run / d2corpus.v2 corpora (W01): one
# `observe-d1` / `observe-d2` run per chain (oracle/v3-successor/src/d12obs.rs), PAR at a time.
#   ORACLE=… CORPORA=/data/illia/nearproof-deps/corpora OUT=… PAR=4 tools/d3/observe_d12.sh d1|d2 [CHAINS…]
set -euo pipefail
dom="$1"; shift
ORACLE="${ORACLE:?set ORACLE to near-arena-oracle-v3-successor}"
CORPORA="${CORPORA:-/data/illia/nearproof-deps/corpora}"
OUT="${OUT:?set OUT}"
PAR="${PAR:-4}"
HEAVY="${HEAVY:-/data/illia/nearproof-deps/bin/heavy}"
case "$dom" in
  d1) corpus="$CORPORA/d1run"; default_chains="$(seq 0 11)";;
  d2) corpus="$CORPORA/d2corpus.v2"; default_chains="$(seq 0 13)";;
  *) echo "usage: $0 d1|d2 [CHAINS…]" >&2; exit 2;;
esac
chains="${*:-$default_chains}"
mkdir -p "$OUT/$dom"
export ORACLE corpus OUT dom HEAVY
for i in $chains; do echo "$i"; done | xargs -P "$PAR" -I{} sh -c '
  i={}; o="$OUT/$dom"
  [ -f "$o/observe-$(printf %02d "$i").json" ] && exit 0
  RAYON_NUM_THREADS=8 HEAVY_MEM=24G timeout 14400 "$HEAVY" "$ORACLE" "observe-$dom" --corpus "$corpus" --chain "$i" \
    --out "$o" --scratch "$OUT/scratch-$dom-$i" > "$o/chain-$i.log" 2>&1 \
    && rm -rf "$OUT/scratch-$dom-$i" || echo "chain $i failed (see $o/chain-$i.log)" >&2
'
