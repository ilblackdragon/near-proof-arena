#!/usr/bin/env bash
set -u
cd /data/illia/nearproof-deps/e2e-laneA/m6-grow/tape
TAPE=/data/illia/nearproof/.claude/worktrees/agent-a8f4c7304349e6ca5/research/near-compression/wasm-base-lean/.lake/build/bin/wasmbase-tape
export WASMBASE_TAPE_CHECKER=M3
rm -f shards/*.tape.jsonl
for f in shards/cases.0?; do
  ( xargs -a "$f" "$TAPE" "$f.tape.jsonl" > /dev/null 2> "$f.err" || true ) &
done
wait
cat shards/*.tape.jsonl > tape.jsonl
wc -l tape.jsonl
