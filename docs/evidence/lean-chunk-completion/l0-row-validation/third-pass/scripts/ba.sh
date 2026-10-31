#!/bin/bash
# Per-case before/after: before = ee00c918 (main with the current_contract_code fix, without the
# gas-key fix), after = 0b0f01ec (this branch).
cd /data/illia/nearproof-deps/l0-validate/b4/ba
W=/data/illia/nearproof/.claude/worktrees/agent-a8b3a000da794c665
H=/data/illia/nearproof-deps/l0-validate/hr
ba() { echo "== $1"; python3 $W/tools/d3/l0_before_after.py $1 $2/results.jsonl $3/results.jsonl > ba-$1.json; python3 -c "import json,sys; d=json.load(open(\"ba-$1.json\")); print(\"$1\", d[\"cases\"], \"moved\", {k: v for k, v in d[\"moved\"].items()}, \"unsound after\", d[\"lean_accept_nearcore_reject_after\"])"; }
ba gk-allFeatures base-gk-allFeatures after-gk-allFeatures
ba gk-signed base-gk-signed after-gk-signed
ba census-allFeatures $H/after-census-allFeatures after-census-allFeatures
ba census-signed $H/after-census-signed after-census-signed
ba fixtures-allFeatures $H/after-fixtures-allFeatures after-fixtures-allFeatures
ba fixtures-signed $H/after-fixtures-signed after-fixtures-signed
ba corpus8-allFeatures $H/after-corpus8-allFeatures after-corpus8-allFeatures
ba corpus8-signed base-corpus8-signed after-corpus8-signed
ba hostrows-allFeatures $H/after-hr after-hostrows-allFeatures
ba hostrows-signed base-hostrows-signed after-hostrows-signed
