#!/usr/bin/env bash
# B-T1: the state side as pinned-shape tree leaves.
#   leaf.sh STATE_JSON OUT_DIR TEMPLATE_JSON [check|prove|stats] [GENARGS…]
# STATE_JSON is `extract_state.py`'s output (or `run.sh`'s OUT_DIR/state.json); TEMPLATE_JSON a
# template file (`templates/*.json`: D, and per proof kind `if` / `seg` the pinned table heights and
# the parameters). Writes OUT_DIR/{if,seg0,seg1,…} (one dump per proof, `tracegen.py --split`), proves
# each at the template (`prove`: proof + vk + statement saved in OUT_DIR/<dump>/out), then checks the
# chain of public values: IF's R_0 = seg0's R_in, seg_k's R_out = seg_{k+1}'s R_in, the last R_out =
# IF's R_n, IF's post-state root = the Lean spec oracle (`m5a-tool apply`).
# Extra args go to tracegen (e.g. --segs 3, --mutant NAME, --host: the segments' STATE rows fed by
# lane A's HOST buses, `m5tSegH`, with the cached `HOSTTAPE` standing in for lane A's rows).
# Exit 4: the case exceeds the template.
# Box rules: ≤ 8 threads, HEAVY_MEM ≤ 40G, temp files under /data/illia/nearproof-deps.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ST=$1; OUT=$2; TMPL=$3; MODE=${4:-prove}; shift 4 || true
DEPS=/data/illia/nearproof-deps/laneB-t1
TARGET_DIR=${TARGET_DIR:-$DEPS/target}
HEAVY="env HEAVY_MEM=${HEAVY_MEM:-40G} RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-8} /data/illia/nearproof-deps/bin/heavy"
D=$(python3 -c "import json,sys; print(json.load(open(sys.argv[1]))['D'])" "$TMPL")
mkdir -p "$OUT/air"
TOOL=$HERE/lean/.lake/build/bin/m5a-tool
( cd "$HERE/lean" && lake build m5a-tool >/dev/null )
"$TOOL" tmpl-if "$D" "$OUT/air/if.json" "$OUT/air/if.names.json" > "$OUT/air/if.txt"
"$TOOL" tmpl-seg "$D" "$OUT/air/seg.json" "$OUT/air/seg.names.json" > "$OUT/air/seg.txt"
"$TOOL" tmpl-segh "$D" "$OUT/air/segh.json" "$OUT/air/segh.names.json" > "$OUT/air/segh.txt"
WANT=$(python3 -c "import json,sys; print(json.load(open(sys.argv[1]))['post_root'])" "$ST")
GOT=$("$TOOL" apply "$ST")
[ "$GOT" = "$WANT" ] || { echo "spec oracle: $GOT != $WANT"; exit 1; }
echo "spec oracle: post-state root $GOT (Lean applyChanges)"
( cd "$HERE/prover" && CARGO_TARGET_DIR=$TARGET_DIR nice -n 10 cargo build --release --offline -j 8 2>/dev/null )
BIN=$TARGET_DIR/release/nearproof-e2e-m5a
rc=0
NAMES=$OUT/air/if.names.json
case " $* " in *" --host "*) NAMES=$OUT/air/segh.names.json ;; esac
python3 "$HERE/tracegen.py" "$ST" "$NAMES" "$OUT" --split --template "$TMPL" "$@" > "$OUT/gen.txt" || rc=$?
[ "$rc" = 0 ] || { cat "$OUT/gen.txt"; exit "$rc"; }
[ "$MODE" = stats ] && { cat "$OUT/gen.txt"; exit 0; }
for d in "$OUT"/if "$OUT"/seg*; do
  [ -d "$d" ] || continue
  air=$OUT/air/seg.json; [ "$(basename "$d")" = if ] && air=$OUT/air/if.json
  [ -f "$d/hosttape.json" ] && air=$OUT/air/segh.json
  echo "== $(basename "$d")"
  nice -n 10 $HEAVY "$BIN" "$air" "$d" "$MODE" "$d/out" > "$d/$MODE.log" 2>&1 || { tail -20 "$d/$MODE.log"; exit 1; }
  grep -E "PRECHECK|PARAMS|SOUNDNESS|PROOF |TIME prove|VERIFY|REJECTED|ACCEPTED|SAVED" "$d/$MODE.log" || true
done
python3 "$HERE/leaf_chain.py" "$OUT" "$GOT"
