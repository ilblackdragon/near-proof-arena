#!/usr/bin/env bash
# Build oracle/fixtures/v3/public-chunk-v3: the public fixtures of `near-chunk-v3` (arena layout,
# runners/worker NearV3Oracle): the union of
#   d0-*  oracle/fixtures/v3/arena-public (D0, verbatim)
#   d1-*  a coverage-selected subset of oracle/fixtures/v3/public-d1 (spec/tools/select_public_v3.py)
#   d2-*  a coverage-selected subset of oracle/fixtures/v3/public-d2
#   d3-*  a coverage-selected subset of a fresh D3 corpus (oracle/v3-d3 gen, seed 4402, chains 0-2 at
#         gas price 0 and 3-5 at min_gas_price 1e8; pass its directory as D3_CORPUS)
# converted with `arena-layout` (oracle/v3-d1/src/arena.rs; positives = nearcore accepts and in the
# domain, incl. nearcore-accepted in-domain mutants; rejections = the rest), case names prefixed by
# the domain, and one params.bin (domain D3a). From the D0-D2 sets only nearcore-rejected rejection
# cases are kept (see `add`).
#   D3_CORPUS=DIR spec/tools/build_public_chunk_v3.sh [OUT]
set -euo pipefail
repo="$(cd "$(dirname "$0")/../.." && pwd)"
out="${1:-$repo/oracle/fixtures/v3/public-chunk-v3}"
bin1="${BIN_D1:-$repo/oracle/d3-ttn/target/debug/near-arena-oracle-v3-d1}"
bin3="${BIN_D3:-$repo/oracle/d3-ttn/target/debug/near-arena-oracle-v3-d3}"
tmp="$(mktemp -d "${TMPDIR:-/tmp}/public-chunk-v3.XXXXXX")"; trap 'rm -rf "$tmp"' EXIT
rm -rf "$out"; mkdir -p "$out/cases" "$out/rejections"
# The statement is RelChunkV3 = Rel ∧ InD3α, so a D0/D1/D2 "rejection" that nearcore accepts (an honest
# chunk outside the lower domain, or a mutant nearcore accepts) may be a TRUE claim of the statement:
# from the D0-D2 sets only nearcore-rejected cases are kept as rejections (false at every tier); the
# D3 set is labelled against InD3α by the D3 oracle (its out-of-D3α chunks are rejections).
add() {  # add SRC_ARENA_DIR PREFIX [nearcore-rejected-only]
  for d in "$1/cases"/*; do cp -R "$d" "$out/cases/$2-$(basename "$d")"; done
  for d in "$1/rejections"/*; do
    if [ -n "${3:-}" ] && python3 -c 'import json,sys; sys.exit(0 if json.load(open(sys.argv[1])).get("nearcore") == "ok" else 1)' "$d/meta.json"; then
      continue
    fi
    cp -R "$d" "$out/rejections/$2-$(basename "$d")"
  done
}
add "$repo/oracle/fixtures/v3/arena-public" d0 nearcore-rejected-only
python3 "$repo/spec/tools/select_public_v3.py" d1 "$repo/oracle/fixtures/v3/public-d1" "$tmp/s1" --per-class 24 --per-family 1 --seed 3
"$bin1" arena-layout --domain d1 --in "$tmp/s1" --out "$tmp/a1" --accepted-mutants
add "$tmp/a1" d1 nearcore-rejected-only
python3 "$repo/spec/tools/select_public_v3.py" d2 "$repo/oracle/fixtures/v3/public-d2" "$tmp/s2" --per-class 24 --per-family 1 --seed 3
"$bin1" arena-layout --domain d2 --in "$tmp/s2" --out "$tmp/a2" --accepted-mutants
add "$tmp/a2" d2 nearcore-rejected-only
python3 "$repo/spec/tools/select_public_v3.py" d3 "${D3_CORPUS:?set D3_CORPUS}" "$tmp/s3" --per-class 36 --per-family 2 --seed 3
"$bin3" arena-layout --domain d3 --in "$tmp/s3" --out "$tmp/a3" --accepted-mutants
add "$tmp/a3" d3
python3 "$repo/spec/tools/params_bin_v3.py" "$out/params.bin" D3a >/dev/null
python3 - "$out" "$tmp" <<'PY'
import json, os, sys
out, tmp = sys.argv[1:3]
s = {"challenge": "near-chunk-v3", "layout": "cases/<domain>-<case>/{request,witness,expected_claim}.bin + meta.json; rejections/<domain>-<case>/{request,witness}.bin + meta.json; params.bin (domain D3a)",
     "sources": {"d0": "oracle/fixtures/v3/arena-public (verbatim)"}}
for d in ("d1", "d2", "d3"):
    s["sources"][d] = json.load(open(os.path.join(tmp, "a" + d[1], "summary.json")))["arena_layout"]
    src = json.load(open(os.path.join(tmp, "s" + d[1], "summary.json"))) if os.path.exists(os.path.join(tmp, "s" + d[1], "summary.json")) else {}
    s["sources"][d]["seed"] = src.get("seed"); s["sources"][d]["selection"] = src.get("public_selection")
    s["sources"][d]["chains"] = src.get("chains") or src.get("runs")
s["positives"] = len(os.listdir(os.path.join(out, "cases"))); s["rejections"] = len(os.listdir(os.path.join(out, "rejections")))
json.dump(s, open(os.path.join(out, "summary.json"), "w"), indent=1, sort_keys=True)
print(s["positives"], "positives,", s["rejections"], "rejections")
PY
