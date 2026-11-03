#!/usr/bin/env bash
# E2E milestone M3 (docs/zk-formal/E2E-GENERAL-CHUNK-PLAN.md): the chunk's own host tape for every
# corpus FunctionCall, then the Wasm trace replay against the chunk's outcome.
#
#   run.sh OUT_DIR CORPUS_D3_DIR...      e.g. run.sh /data/illia/nearproof-deps/e2e-laneA/m3 \
#                                             /data/illia/nearproof-deps/corpora/d3c{7,8,9,10}/d3
#
# 1. `wasmbase-tape` (wasm-base-lean/Tape.lean) runs the unmodified Lean checker
#    `Schema.checkVersioned (Tier.cfg .allFeatures)` on every case, 8 shards in parallel, recording
#    each Wasm call's host tape from the checker's own context and trie-backed store;
# 2. `sweep.py` turns each eligible call's tape into a trace (`nearproof-wasm-base check-tape`, the
#    `wasmBaseIfRegAir` constraint and bus pre-check) and compares status, burnt gas, logs and the
#    return value with the checker's outcome of that call.
# Builds must be fresh: `lake build wasmbase-tape wasmbase-tool` and the release `nearproof-wasm-base`.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
OUT=$1; shift
TAPE=$ROOT/research/near-compression/wasm-base-lean/.lake/build/bin/wasmbase-tape
mkdir -p "$OUT/shards"
rm -f "$OUT"/shards/cases.*   # the tape appends
for d in "$@"; do ls -d "$d"/*/ ; done | sed 's:/$::' | sort > "$OUT/cases.txt"
split -n r/8 -d "$OUT/cases.txt" "$OUT/shards/cases."
ls "$OUT"/shards/cases.* | xargs -P 8 -I{} sh -c "xargs -a {} \"$TAPE\" {}.tape.jsonl > /dev/null 2> {}.err || true"
cat "$OUT"/shards/cases.*.tape.jsonl > "$OUT/tape.jsonl"
python3 "$HERE/sweep.py" "$OUT/tape.jsonl" "$OUT" --jobs 8 | tee "$OUT/summary.txt"
