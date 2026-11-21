#!/usr/bin/env bash
# E2E-D D-9: the review-D8 tamper fixtures (/data/illia/nearproof-deps/review-d8/tamper) as negative
# tests of the M1 / M2 fixes. Each must be REJECTED:
#  vkweak : class 0 vk with every AIR-0 constraint removed, base_vk_sha256 updated  -> tree-audit fails
#  padkeys: class 0 TAPE pad key (56,5) -> (57,5) in the setup                      -> tree-audit fails
#  base0  : an honest class-S base dir whose TAPE_PAD.json has the same key swap    -> tree-prove refuses
#           it as a class dir (TREE_CLASS_KEY_REBUILT never printed, a panic naming the class)
# and the untampered D-8 setup must PASS the class-level audit (control).
# usage: tamper_d9.sh OUTDIR   (8 CPUs 8-15)
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d9}
P=${PROVER:-$D/target/release/nearproof-chunk-e2e}
K=$ROOT/research/near-compression/final-soundness
AIR=$ROOT/examples/np-udr-stark-v2/source/near-air-v3.json
FX=${FIXTURES:-/data/illia/nearproof-deps/review-d8/tamper}
O=$1; mkdir -p "$O"
HONEST=$D/b8/d1_09-h10150-s3
export CPUSET=8-15 RAYON_NUM_THREADS=8
fail=0
# control: the D-8 setup + its class vks (class level; version 5)
rm -rf "$O/control"; mkdir -p "$O/control"
cp /data/illia/nearproof-deps/pq-e2e-d8/tree8/d1_10-h10075-s0/SETUP.json /data/illia/nearproof-deps/pq-e2e-d8/tree8/d1_10-h10075-s0/CLASS*.BASE.vk.json "$O/control/" 2>/dev/null \
  || cp "$D"/auditv5/d8/SETUP.json "$D"/auditv5/d8/CLASS*.BASE.vk.json "$O/control/"
if "$HERE/audit_d9.sh" "$O/control" "$HONEST" > "$O/control.txt"; then echo "CONTROL_ACCEPTED (expected)"; else echo "CONTROL_REJECTED (unexpected)"; fail=1; fi
for t in vkweak padkeys; do
  rm -rf "${O:?}/$t"; cp -r "$FX/$t" "$O/$t"
  if "$HERE/audit_d9.sh" "$O/$t" "$HONEST" > "$O/$t.txt"; then echo "TAMPER_ACCEPTED $t (BAD)"; fail=1
  else echo "TAMPER_REJECTED $t: $(grep -h 'MISMATCH' "$O/$t.txt" | head -2 | tr '\n' ' ')"; fi
done
# base0 as a class dir of tree-prove (only the class-key check runs before the first proof: stop
# after 600 s at most; a refusal is a panic before TREE_CLASS_KEY_REBUILT class=0)
rm -rf "$O/base0" "$O/base0-out"; cp -r "$FX/base0" "$O/base0"
ln -sfn "$(readlink -f "$HONEST/public")" "$O/base0/public"
rc=0
NEARPROOF_ZK=1 NEARPROOF_TAPE_EVAL=1 NEARPROOF_CHAIN_GEOM=ns19lb6 NEARPROOF_ZK_FINAL=6 NEARPROOF_TREE_LEAF_PARAMS=ns20lb2 \
  timeout 600 taskset -c 8-15 "$P" tree-prove "$AIR" "$O/base0/public" "$O/base0-out" "$O/base0" "$K/calc/dkt_certs_o2.json" "$K/lean/DKTCertsO2_big.keys" - 1 "$O/base0" \
  > "$O/base0.log" 2>&1 || rc=$?
if [ "$rc" != 0 ] && ! grep -q "TREE_CLASS_KEY_REBUILT class=0" "$O/base0.log"; then
  echo "TAMPER_REJECTED base0: $(grep -h -A1 panicked "$O/base0.log" | tail -1 | cut -c1-200)"
else echo "TAMPER_ACCEPTED base0 (BAD) rc=$rc"; fail=1; fi
rm -rf "$O/base0-out"
[ $fail = 0 ] && echo TAMPER_D9_ALL_REJECTED || { echo TAMPER_D9_FAILED; exit 1; }
