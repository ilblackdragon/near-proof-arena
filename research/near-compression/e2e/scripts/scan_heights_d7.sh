#!/usr/bin/env bash
# D-7: heights census of d1 chunks (statedump compact; keep heights.json + log, drop traces)
. "$(cd "$(dirname "$0")" && pwd)/env_d7.sh"
SD=$D/target-sd/release/examples/statedump
O=$D/bclass/scan; mkdir -p $O
one() {
  c=$1; n=$(basename $c)
  [ -f $O/$n/heights.json ] && return
  timeout 300 $SD d0a $AIR $c $O/$n > $O/$n.log 2>&1; echo "$n rc=$?"
  rm -f $O/$n/*.bin
}
export -f one; export SD AIR O
ls -d $CORP/d1run/d1/00-h100* $CORP/d1run/d1/00-h101* 2>/dev/null | head -${N:-80} | taskset -c 8-11 xargs -P 4 -I{} bash -c 'one {}'
echo SCAN_DONE
