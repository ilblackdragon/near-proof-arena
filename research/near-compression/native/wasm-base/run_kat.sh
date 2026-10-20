#!/usr/bin/env bash
# Known-answer tests: every program of programs/gen.py through (1) the Python reference
# interpreter, (2) the Lean spec (`wasmbase-tool prep`: prepare + check + spec `step` run),
# (3) the Rust trace generator + full constraint and bus pre-check (`check`).
# Usage: run_kat.sh <scratch_dir> [hash_iters...]
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
OUT=${1:?scratch dir}; shift
TOOL=$HERE/../../wasm-base-lean/.lake/build/bin/wasmbase-tool
BIN=${WASMBASE_BIN:-/data/illia/nearproof-deps/pq-wasm-base/target/release/nearproof-wasm-base}
G0=1000000000000000
python3 "$HERE/programs/gen.py" "$OUT/progs" "$@" >/dev/null
pass=0; fail=0
for w in "$OUT"/progs/*.wasm; do
  n=$(basename "$w" .wasm)
  "$TOOL" prep "$w" main $G0 > "$OUT/progs/$n.prep.json"
  # A program whose only imports are outside the checker's domain (the HOST row cannot carry the
  # signature: `validator_stake` np=3, `gas` i32) must be rejected as ineligible.  That rejection is
  # the KAT: there is no trace to generate.
  if [ "$(python3 -c "import json;print(json.load(open('$OUT/progs/$n.prep.json')).get('eligible'))")" = "False" ]; then
    if [ "$(python3 -c "import json;print(json.load(open('$OUT/progs/$n.json')).get('result'))")" = "ineligible" ]; then
      pass=$((pass+1)); continue
    fi
    fail=$((fail+1)); echo "FAIL $n (unexpectedly ineligible)"; continue
  fi
  read -r nloc ngl nimp <<<"$(python3 -c "import json;d=json.load(open('$OUT/progs/$n.prep.json'));print(len(d['localTags']),d.get('ngl',0),1 if d.get('hosts') else 0)")"
  AIRK=air; [ "$nimp" = 1 ] && AIRK=airH
  [ -f "$OUT/$AIRK-$nloc-g$ngl.json" ] || "$TOOL" $AIRK "$nloc" "$ngl" > "$OUT/$AIRK-$nloc-g$ngl.json"
  # Python reference vs Lean spec (value and step count).  Host programs are not gas-modelled by the
  # Python interpreter, so only the outcome is compared there.
  python3 - "$OUT/progs/$n.json" "$OUT/progs/$n.prep.json" "$nimp" <<'PY'
import json, sys
ref = json.load(open(sys.argv[1])); sp = json.load(open(sys.argv[2])); host = sys.argv[3] == '1'
if not host:
    assert sp['steps'] == ref['steps'], (sp['steps'], ref['steps'])
if ref['result'] == 'trap':
    assert sp['status'].startswith('abort '), sp['status']
    if not host:
        assert sp['status'].startswith('abort WasmTrap'), sp['status']
else:
    assert sp['status'] == 'fin', sp['status']
    l = sp['stack'][-1]['limbs']; v = l[0] | l[1] << 16 | l[2] << 32 | l[3] << 48
    assert v == ref['result'], (v, ref['result'])
PY
  if "$BIN" check "$OUT/$AIRK-$nloc-g$ngl.json" "$OUT/progs/$n.prep.json" > "$OUT/progs/$n.check.log" 2>&1; then
    pass=$((pass+1))
  else
    fail=$((fail+1)); echo "FAIL $n"; tail -3 "$OUT/progs/$n.check.log"
  fi
done
echo "KAT: $pass passed, $fail failed (python ref = Lean spec = Rust trace + AIR pre-check)"
[ "$fail" = 0 ]
