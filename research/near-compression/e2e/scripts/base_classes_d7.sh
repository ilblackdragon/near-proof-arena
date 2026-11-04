#!/usr/bin/env bash
# D-7 (review-D6 F1): pinned base shape classes over real D0a chunks.
#   class A = {d1_00-h10006-s3 (chunk 1 of D-4..D-6), d1_00-h10013-s1}
#   class B = {d1_00-h10013-s2, d1_00-h10025-s0, d1_00-h10026-s0, d1_00-h10027-s0, d1_00-h10029-s0}
# (groups found by work/classgroups.py over 26 scanned d1 chunks). Class logs = max of the members'
# compact logs; every member re-cut at those logs (statedump --class, re-checked); tight heights = max
# over the re-cut members, bucketed to 1/8 of 2^log. Base proofs at the class shape for two members
# of each class (two independent base proofs per class: review-D6 F5); the other members of B are
# checked to be admitted (re-cut dump succeeds, tights within the class).
# usage: classes.sh [STEPS]   (0 = classes + dumps + public; 1.. = base proofs)
. "$(cd "$(dirname "$0")" && pwd)/env_d7.sh"
set -uo pipefail
export RAYON_NUM_THREADS=10 HEAVY_MEM=40G NEARPROOF_ZK=1 NEARPROOF_TAPE_EVAL=1 NEARPROOF_CHAIN_GEOM=ns19lb6
SD=$D/target-sd/release/examples/statedump
SP=$E/$C1/tools/statepublic
O=$D/bclass; mkdir -p $O/dumps0 $O/dumps $O/public
A_M="00-h10006-s3 00-h10013-s1"
B_M="00-h10013-s2 00-h10025-s0 00-h10026-s0 00-h10027-s0 00-h10029-s0"
mkclass() { # NAME MEMBERS...
  local n=$1; shift
  local d0=() d1=()
  for c in "$@"; do
    [ -f $O/dumps0/$c/heights.json ] || $SD d0a $AIR $CORP/d1run/d1/$c $O/dumps0/$c > $O/dumps0/$c.log 2>&1
    d0+=($O/dumps0/$c)
  done
  $P base-class ${n}0 3 $O/${n}0.json $AIR "${d0[@]}" | tee $O/${n}0.txt
  for c in "$@"; do
    rm -rf $O/dumps/$c
    $SD d0a $AIR $CORP/d1run/d1/$c $O/dumps/$c --class=$O/${n}0.json > $O/dumps/$c.log 2>&1 || { echo "STATEDUMP_CLASS_FAIL $c"; tail -2 $O/dumps/$c.log; }
    d1+=($O/dumps/$c)
  done
  $P base-class $n 3 $O/$n.json $AIR "${d1[@]}" | tee $O/$n.txt
  $P base-shape $AIR "${d1[@]}" | sed "s#$O/dumps/##" > $O/$n.shapes.txt
}
prove() { # MEMBER CLASS [SUFFIX]
  local c=$1 R=$O/d1_$1${3:-}
  rm -rf $R; mkdir -p $R
  [ -d $O/public/$c ] || $SP $AIR $CORP/d1run/d1/$c/claim.bin $O/dumps/$c/hint.bin $O/public/$c > $O/public/$c.log 2>&1
  cmp -s $O/public/$c/pubs.bin $O/dumps/$c/pubs.bin || echo "PUBLIC_MISMATCH $c"
  ln -sfn $O/public/$c $R/public
  NEARPROOF_BASE_CLASS=$O/$2.json taskset -c 8-15,24-25 /data/illia/nearproof-deps/bin/heavy /usr/bin/time -v \
    $P base $AIR $O/dumps/$c $R $K/calc/dkt_certs_o2.json $K/lean/DKTCertsO2_big.keys > $R/base.log 2>&1
  echo "BASE d1_$c${3:-} class=$2 rc=$? $(grep -h 'BASE_CLASS_HEIGHTS_OK\|BASE_VERIFIED\|PRECHECK\|panicked\|Elapsed\|Maximum resident' $R/base.log | tr '\n' ' ')"
}
for s in ${1:-0 1 2 3 4}; do case $s in
0) mkclass A $A_M; mkclass B $B_M;;
1) prove 00-h10006-s3 A;;
2) prove 00-h10013-s1 A;;
3) prove 00-h10025-s0 B;;
4) prove 00-h10027-s0 B;;
esac; done
echo CLASSES_DONE
