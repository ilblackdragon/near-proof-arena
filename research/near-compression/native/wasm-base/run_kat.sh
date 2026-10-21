#!/usr/bin/env bash
# Known-answer tests: every program of programs/gen.py through (1) the Python reference
# interpreter, (2) the Lean spec (`wasmbase-tool prep`: prepare + check + spec `step` run),
# (3) the Rust trace generator + full constraint and bus pre-check (`check`).
#
# Both sides must be rebuilt before trusting a result:
#   cd ../../wasm-base-lean && lake build wasmbase-tool   # after any Lean AIR change
#   cd . && cargo build --release                        # after any src/*.rs change
# A stale binary or tool has produced false failures three times; bin.sh now
# rejects a binary older than its sources, but it cannot see the Lean tool.
#
# Usage: run_kat.sh <scratch_dir> [hash_iters...]
# Env:   WASMBASE_BIN   override the binary path (still staleness-checked)
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
OUT=${1:?scratch dir}; shift
TOOL=$HERE/../../wasm-base-lean/.lake/build/bin/wasmbase-tool
# shellcheck source=bin.sh
. "$HERE/bin.sh"
BIN=$(resolve_bin) || exit 1
G0=1000000000000000
python3 "$HERE/programs/gen.py" "$OUT/progs" "$@" >/dev/null
pass=0; fail=0
for w in "$OUT"/progs/*.wasm; do
  n=$(basename "$w" .wasm)
  INP=$(python3 -c "import json;print(json.load(open('$OUT/progs/$n.json')).get('input',''))")
  "$TOOL" prep "$w" main $G0 "$INP" > "$OUT/progs/$n.prep.json"
  # A program whose only imports are outside the checker's domain (the HOST row cannot carry the
  # signature: `gas` takes an i32) must be rejected as ineligible.  That rejection is the KAT:
  # there is no trace to generate.
  if [ "$(python3 -c "import json;print(json.load(open('$OUT/progs/$n.prep.json')).get('eligible'))")" = "False" ]; then
    if [ "$(python3 -c "import json;print(json.load(open('$OUT/progs/$n.json')).get('result'))")" = "ineligible" ]; then
      pass=$((pass+1)); continue
    fi
    fail=$((fail+1)); echo "FAIL $n (unexpectedly ineligible)"; continue
  fi
  read -r nloc ngl nimp nreg nsha <<<"$(python3 -c "import json;d=json.load(open('$OUT/progs/$n.prep.json'));hs=d.get('hosts',[]);reg=any(h.get('hid') in (48,49) and h.get('regs') for h in hs);sha=any(h.get('hid')==53 for h in hs);print(len(d['localTags']),d.get('ngl',0),1 if hs else 0,1 if reg else 0,1 if sha else 0)")"
  AIRK=air; [ "$nimp" = 1 ] && AIRK=airH; [ "$nreg" = 1 ] && AIRK=airR; [ "$nsha" = 1 ] && AIRK=airX
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
  # A HOSTB group that is **absent** still balances its bus, so `check` cannot tell "the payload
  # was carried" from "no payload group existed".  `logkat` pins this: its three calls are
  # `log_utf8(0,5)`, `log_utf16(8,4)`, `value_return(0,5)` over known memory, and the byte-payload
  # ids are 45/46/50 (`Chips.hostByteIds`).  Assert the bytes, not just the balance.
  if [ "$n" = "logkat" ]; then
    "$BIN" hostb-dump "$OUT/$AIRK-$nloc-g$ngl.json" "$OUT/progs/$n.prep.json" > "$OUT/progs/$n.hostb.log" 2>&1
    hostb_ok=1
    python3 - "$OUT/progs/$n.hostb.log" > "$OUT/progs/$n.hostb.check" 2>&1 <<'PYHOSTB' || hostb_ok=0
import re, sys
rows = []
for ln in open(sys.argv[1]):
    m = re.match(r"HOSTB ts=(\d+) dir=(\d+) pos=(\d+) byte=(\d+) len=(\d+) hid=(\d+)", ln)
    if m:
        ts, d, pos, byte, ln_, hid = map(int, m.groups())
        rows.append((ts, d, pos, byte, ln_, hid))
want = {45: [104, 101, 108, 108, 111], 46: [104, 0, 105, 0],
        50: [104, 101, 108, 108, 111]}
got = {}
for ts, d, pos, byte, ln_, hid in rows:
    got.setdefault(hid, {})[pos] = byte
assert set(got) == set(want), f"HOSTB ids {sorted(got)} != {sorted(want)}: a payload group is missing"
for hid, exp in want.items():
    act = [got[hid][i] for i in sorted(got[hid])]
    assert act == exp, f"HOSTB payload for hid {hid} is {act}, want {exp}"
print(f"HOSTB payload OK: {len(rows)} rows, ids {sorted(got)} carry their memory bytes")
PYHOSTB
    if [ "$hostb_ok" = 0 ]; then
      fail=$((fail+1)); echo "FAIL $n (HOSTB payload)"; tail -3 "$OUT/progs/$n.hostb.check"; continue
    fi
  fi
  if "$BIN" check "$OUT/$AIRK-$nloc-g$ngl.json" "$OUT/progs/$n.prep.json" > "$OUT/progs/$n.check.log" 2>&1; then
    pass=$((pass+1))
  else
    fail=$((fail+1)); echo "FAIL $n"; tail -3 "$OUT/progs/$n.check.log"
  fi
done
echo "KAT: $pass passed, $fail failed (python ref = Lean spec = Rust trace + AIR pre-check)"
[ "$fail" = 0 ]
