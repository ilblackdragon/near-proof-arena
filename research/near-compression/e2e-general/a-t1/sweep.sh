#!/usr/bin/env bash
# T1 (d3tiny.run): segcheck at every cut size 1..26, then segprove at K=8 and K=26 (one segment)
. /data/illia/nearproof-deps/e2e-laneA/at1/env.sh
cd /data/illia/nearproof-deps/e2e-laneA/at1/t1
for k in $(seq 1 26); do
  if $CAP $B segcheck airSeg.json airM2.json t1.prep.json $k > sc-$k.log 2>&1; then r=$(grep -c 'PRECHECK OK' sc-$k.log); echo "K=$k rc=0 precheck_ok=$r $(grep SEGCHECK sc-$k.log)"; else echo "K=$k FAIL $(tail -2 sc-$k.log | tr '\n' ' ')"; fi
done
for k in 8 26; do
  $CAP $B segprove airSeg.json airM2.json t1.prep.json $k > sp-$k.log 2>&1; echo "PROVE K=$k rc=$?"; grep -E 'PROOF|VERIFY|bytes|prove|SEGPROVE' sp-$k.log | tail -8
done
