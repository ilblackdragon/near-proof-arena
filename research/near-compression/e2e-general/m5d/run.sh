#!/usr/bin/env bash
# E2E M5d (lane G): the FINAL template (class F1) or the INIT template of one corpus chunk, on the
# main PQ stack.
#   run.sh CASE_DIR OUT_DIR [check|prove|mutants]
#   TEMPLATE=init runs the INIT template instead of FINAL.
#   MUTANTS="…" picks the mutant battery (default: every mutant of tracegen.py's MUTANTS / INIT_MUTANTS).
#   TMPL=FILE pins the shape (G-2, `templates/*.json`); default: the first of `templates/F1*.json`
#     (FINAL) / `templates/INIT-*.json` (INIT), smallest first (by `cells`), that the case fits (tracegen exit 4 =
#     overflow → the next one). TMPL=none: the superseded M5d-T1 path (natural heights, seg-v1
#     parameters; now on the same backend as the template path).
# `prove` with a template saves the proof in lane D's format under OUT_DIR/proof-$TEMPLATE/
# (STATE.proof, STATE.vk.json, statement.json) and verifies it with lane D's own driver
# (`nearproof-chunk-e2e fs-count VK PROOF 0`, the pq-e2e-d9 build; FSCOUNT=… overrides, FSCOUNT=
# skips).
# Box rules: ≤ 8 threads, prover ≤ 40 GB (HEAVY_MEM), temp files under /data/illia/nearproof-deps.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
CASE=$1; OUT=$2; MODE=${3:-prove}
DEPS=/data/illia/nearproof-deps/e2e-m5d
TARGET_DIR=${TARGET_DIR:-$DEPS/target}
HEAVY="env HEAVY_MEM=${HEAVY_MEM:-40G} RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-8} /data/illia/nearproof-deps/bin/heavy"
TOOL=$HERE/lean/.lake/build/bin/m5d-tool
BIN=$TARGET_DIR/release/nearproof-e2e-m5d
FSCOUNT=${FSCOUNT-/data/illia/nearproof-deps/pq-e2e-d9/drv/release/nearproof-chunk-e2e}
mkdir -p "$OUT"
"$HERE/build.sh" > "$OUT/build.log" 2>&1 || { tail -30 "$OUT/build.log"; exit 1; }
# 1. the Lean checker's own run on the case (finK + tailNew), with recomputation self-checks
"$TOOL" dump "$CASE" "$OUT/dump.json"
# 2. the AIR, exported from Lean
T=${TEMPLATE:-final}
"$TOOL" air-$T "$OUT/$T.json" "$OUT/$T-names.json" > "$OUT/air-$T.txt"
# 3. the template (G-2)
if [ "${TMPL:-}" = none ]; then
  CANDS=()
elif [ -n "${TMPL:-}" ]; then
  CANDS=("$TMPL")
else
  PFX=F1; [ "$T" = init ] && PFX=INIT-
  mapfile -t CANDS < <(python3 -c "
import glob, json, sys
fs = glob.glob(sys.argv[1] + '/templates/' + sys.argv[2] + '*.json')
print('\n'.join(sorted(fs, key=lambda f: json.load(open(f))['cells'])))" "$HERE" "$PFX")
fi
gen() { python3 "$HERE/tracegen.py" "$OUT/dump.json" "$OUT/$T-names.json" "$1" "${@:2}"; }
TARGS=()
for c in "${CANDS[@]}"; do
  rc=0; gen "$OUT/fit-probe" --template "$c" > "$OUT/fit-probe.txt" || rc=$?
  rm -rf "$OUT/fit-probe"
  if [ "$rc" = 0 ]; then TARGS=(--template "$c"); echo "TEMPLATE $c"; break; fi
  [ "$rc" = 4 ] || { cat "$OUT/fit-probe.txt"; exit "$rc"; }
  echo "TEMPLATE $c: $(cat "$OUT/fit-probe.txt")"
done
if [ "${#CANDS[@]}" -gt 0 ] && [ "${#TARGS[@]}" = 0 ]; then echo "no template fits the case"; exit 4; fi
if [ "$MODE" = mutants ]; then
  LIST=MUTANTS; [ "$T" = init ] && LIST=INIT_MUTANTS
  ALL=$(python3 -c "import sys; sys.path.insert(0, '$HERE'); import tracegen; print(' '.join(tracegen.$LIST))")
  for m in ${MUTANTS:-$ALL}; do
    rc=0; gen "$OUT/mut-$m" --mutant "$m" "${TARGS[@]}" > "$OUT/mut-$m.gen.txt" || rc=$?
    if [ "$rc" = 3 ]; then echo "$m: NOT APPLICABLE"; continue; fi
    [ "$rc" = 0 ] || { echo "$m: tracegen failed (exit $rc)"; cat "$OUT/mut-$m.gen.txt"; exit "$rc"; }
    echo -n "$m: "
    # G-2: the AIR's precheck first (constraints on every row + bus balance; `check` mode, cheap). A
    # precheck failure is the AIR rejecting the trace; the full prover + native verifier + statement
    # check run only for mutants that pass it (MUTANT_FULL=1: always run the full path, as M5d-T1).
    if [ "${MUTANT_FULL:-0}" != 1 ] && ! nice -n 10 $HEAVY "$BIN" "$OUT/$T.json" "$OUT/$T-names.json" "$OUT/mut-$m" check > "$OUT/mut-$m.log" 2>&1; then
      echo "PRECHECK FAIL: $(grep -oE "precheck: .*" "$OUT/mut-$m.log" | head -1 | cut -c11-200) REJECTED (AIR precheck; full prover skipped)"
    else
      nice -n 10 $HEAVY "$BIN" "$OUT/$T.json" "$OUT/$T-names.json" "$OUT/mut-$m" mutant > "$OUT/mut-$m.log" 2>&1 || true
      grep -E "PRECHECK FAIL|REJECTED|ACCEPTED" "$OUT/mut-$m.log" | tr '\n' ' ' | cut -c1-220; echo
    fi
    rm -rf "$OUT/mut-$m"
  done
else
  gen "$OUT/dump-$T" "${TARGS[@]}" | tee "$OUT/gen-$T.txt"
  PDIR=()
  [ "$MODE" = prove ] && [ "${#TARGS[@]}" -gt 0 ] && PDIR=("$OUT/proof-$T")
  nice -n 10 $HEAVY "$BIN" "$OUT/$T.json" "$OUT/$T-names.json" "$OUT/dump-$T" "$MODE" "${PDIR[@]}" | tee "$OUT/$T-$MODE.log"
  if [ "${#PDIR[@]}" -gt 0 ] && [ -n "$FSCOUNT" ]; then
    echo "== lane D's driver: fs-count $OUT/proof-$T"
    $HEAVY "$FSCOUNT" fs-count "$OUT/proof-$T/STATE.vk.json" "$OUT/proof-$T/STATE.proof" 0 2>&1 | tee "$OUT/$T-fscount.log"
  fi
fi
