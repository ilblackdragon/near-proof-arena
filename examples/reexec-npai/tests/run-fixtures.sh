#!/usr/bin/env bash
# Local functional test: prove every public fixture with the Rust prover and
# verify with the judge's NPAI interpreter (npai-verify) on the exported image.
# usage: tests/run-fixtures.sh IMAGE [FIXTURES_DIR]
set -euo pipefail
here="$(cd "$(dirname "$0")/.." && pwd)"
root="$(cd "$here/../.." && pwd)"
img="$1"
fx="${2:-$root/oracle/fixtures/public}"
fuel=1073741824
pv="$root/target/release/npai-verify"
prove="$here/source/target/release/prove"
prep="$here/source/target/release/prepare"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
"$prep" --params "$fx/params.bin" --out "$tmp/pub"
pass=0; fail=0
for c in "$fx"/cases/*/; do
  n="$(basename "$c")"
  if ! "$prove" --public "$tmp/pub" --request "$c/request.bin" --witness "$c/witness.bin" \
      --claim-out "$tmp/claim.bin" --proof-out "$tmp/proof.bin" 2>"$tmp/err"; then
    echo "$n: prove failed: $(cat "$tmp/err")"; fail=$((fail+1)); continue
  fi
  if [ -f "$c/expected_claim.bin" ] && ! cmp -s "$c/expected_claim.bin" "$tmp/claim.bin"; then
    echo "$n: claim mismatch"; fail=$((fail+1)); continue
  fi
  set +e
  out="$("$pv" --image "$img" --public "$tmp/pub" --claim "$tmp/claim.bin" --proof "$tmp/proof.bin" --fuel $fuel)"
  rc=$?
  set -e
  echo "$n: rc=$rc proof=$(stat -c %s "$tmp/proof.bin") $out"
  if [ $rc -eq 0 ]; then pass=$((pass+1)); else fail=$((fail+1)); fi
done
echo "accepted $pass, failed $fail"
