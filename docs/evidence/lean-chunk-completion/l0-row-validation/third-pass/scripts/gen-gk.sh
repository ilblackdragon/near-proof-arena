#!/bin/bash
# Gas-key InvalidMethodName fixture family. PASS=1: honest cases + full mutant sets.
# PASS=2: the same runs (deterministic) with NEAR_L0_HDR_OVERRIDES=overrides.json, which adds the
# `l0.hdr.lean_outputs` mutant (header := the Lean checker's --blind outputs) to the listed cases.
set -u
cd /data/illia/nearproof-deps/l0-validate/b4/gk
PASS=${PASS:-1}
run() { # variant seed
  local out=p$PASS-$1-$2
  rm -rf $out
  local ov=""
  [ $PASS = 2 ] && ov="NEAR_L0_HDR_OVERRIDES=$PWD/overrides-$1-$2.json"
  env $ov NEAR_L0_ROW_MUTANTS=1 NEAR_SUCCESSOR_CONTRACT=$PWD/gk$1.wasm HEAVY_MEM=20G /data/illia/nearproof-deps/bin/heavy ../oracle-l0 gen \
    --domain d3 --seed $2 --chains 1 --blocks 12 --mutate-every 1 --code-mutant-p 0 --drop-cap 4 \
    --out $out > $out.log 2>&1
  echo "$out rc=$? $(tail -1 $out.log)"
}
for v in ${VARIANTS:-cont ret}; do
  for s in 31 32 33 34; do run $v $s & done
  wait
done
