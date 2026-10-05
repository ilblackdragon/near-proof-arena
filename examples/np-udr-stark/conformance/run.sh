#!/usr/bin/env bash
# Differential conformance: Rust prover (../source) vs the deployed Lean
# verifier model (np-lean-verify, ZkFormal.Stark.verifier Fp Fp8 air default).
#
#   ./run.sh [log ...]        (default logs: 3 6 10)
#
# 1. builds both sides;
# 2. checks `npudr export X` == `np-lean-export X` byte for byte (X = fib, multi)
#    and that the Lean reader round-trips the Rust export;
# 3. for each toy and log: `npudr toy X log dir`, then np-lean-verify must
#    accept the honest proof and reject every mutated proof (byte flips at
#    several offsets, truncation, an appended byte), plus a mutated claim.
# Heavy commands run under $HEAVY (default /data/illia/nearproof-deps/bin/heavy
# if present) so an OOM kills the command, not the session.
set -u
here="$(cd "$(dirname "$0")" && pwd)"
src="$here/../source"
out="$here/out"
if [ -z "${HEAVY+x}" ]; then
  if [ -x /data/illia/nearproof-deps/bin/heavy ]; then HEAVY=/data/illia/nearproof-deps/bin/heavy; else HEAVY=; fi
fi
export PATH="$HOME/.elan/bin:$PATH"
logs=("$@"); [ ${#logs[@]} -eq 0 ] && logs=(3 6 10)

fail=0
pass() { echo "PASS  $*"; }
bad()  { echo "FAIL  $*"; fail=1; }

echo "== build"
(cd "$src" && $HEAVY cargo build --release -q) || { echo "cargo build failed"; exit 2; }
(cd "$here" && $HEAVY lake build -q) || { echo "lake build failed"; exit 2; }
npudr="$src/target/release/npudr"
lv="$here/.lake/build/bin/np-lean-verify"
le="$here/.lake/build/bin/np-lean-export"
mkdir -p "$out"

echo "== AIR export: Rust vs Lean"
for x in fib multi; do
  "$npudr" export $x > "$out/rust-$x.json"
  "$le" $x > "$out/lean-$x.json"
  if cmp -s "$out/rust-$x.json" "$out/lean-$x.json"; then pass "export $x byte-identical"
  else bad "export $x differs"; diff <("$npudr" export $x | tr ',' '\n') <("$le" $x | tr ',' '\n') | head; fi
  if "$le" --roundtrip "$out/rust-$x.json" >/dev/null; then pass "roundtrip $x"; else bad "roundtrip $x"; fi
done

# verify <dir> <proof> [claim] -> prints accept/reject, returns exit code
verify() {
  local d=$1 pf=$2 cb=${3:-$1/claim.bin} pubf=$1/pub.bin
  [ -f "$pubf" ] || pubf=$1/pubdigest.bin   # provisional (pre-v1) Rust output
  HEAVY_MEM=${VERIFY_MEM:-4G} $HEAVY "$lv" "$d/air.json" "$pubf" "$cb" "$pf" 2>"$d/verify.err"
}

mutate() { # mutate <in> <out> <op> <offset>
  python3 - "$@" <<'PY'
import sys
src, dst, op, off = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
b = bytearray(open(src, 'rb').read())
if op == 'flip': b[off % len(b)] ^= 0x01
elif op == 'trunc': b = b[:-1]
elif op == 'append': b += b'\x00'
open(dst, 'wb').write(bytes(b))
PY
}

echo "== constraint evaluation at random points: Rust vs Lean"
ev="$here/.lake/build/bin/np-lean-eval"
for x in fib multi bus; do
  "$npudr" toy $x 3 "$out/ev-$x" >/dev/null
  for s in 1 2 3; do
    if cmp -s <("$npudr" eval-random "$out/ev-$x/air.json" $s) <("$ev" "$out/ev-$x/air.json" $s); then pass "eval $x seed $s"
    else bad "eval $x seed $s"; fi
  done
done

# check_proof <label> <dir>: honest proof accepted, mutations rejected
check_proof() {
  local x=$1 d=$2
  n=$(stat -c %s "$d/proof.bin")
  r=$(verify "$d" "$d/proof.bin"); rc=$?
  t=$(grep -o 'wall [0-9]* ms' "$d/verify.err")
  if [ "$r" = accept ] && [ $rc -eq 0 ]; then pass "$x honest proof ($n B) accepted, $t"
  else bad "$x honest proof ($n B) -> '$r' rc=$rc, $t"; cat "$d/verify.err"; fi
  # mutations: header, first root, middle, near the end, last byte
  for off in ${OFFSETS:-0 9 40 $((n/3)) $((n/2)) $((n-40)) $((n-1))}; do
    mutate "$d/proof.bin" "$d/mut.bin" flip $off
    r=$(verify "$d" "$d/mut.bin"); rc=$?
    if [ "$r" = reject ] && [ $rc -eq 1 ]; then pass "$x flip@$off rejected"
    else bad "$x flip@$off -> '$r' rc=$rc"; fi
  done
  for op in trunc append; do
    mutate "$d/proof.bin" "$d/mut.bin" $op 0
    r=$(verify "$d" "$d/mut.bin"); rc=$?
    if [ "$r" = reject ] && [ $rc -eq 1 ]; then pass "$x $op rejected"
    else bad "$x $op -> '$r' rc=$rc"; fi
  done
  if [ -s "$d/claim.bin" ]; then
    mutate "$d/claim.bin" "$d/claim.mut" flip 2
    r=$(verify "$d" "$d/proof.bin" "$d/claim.mut"); rc=$?
    if [ "$r" = reject ] && [ $rc -eq 1 ]; then pass "$x mutated claim rejected"
    else bad "$x mutated claim -> '$r' rc=$rc"; fi
  else
    # empty claim (SHA toy): extend it by one byte instead
    printf '\x00' > "$d/claim.mut"
    r=$(verify "$d" "$d/proof.bin" "$d/claim.mut"); rc=$?
    if [ "$r" = reject ] && [ $rc -eq 1 ]; then pass "$x extended claim rejected"
    else bad "$x extended claim -> '$r' rc=$rc"; fi
  fi
}

echo "== proofs"
for x in fib multi bus; do
  for lg in "${logs[@]}"; do
    d="$out/$x-$lg"; rm -rf "$d"; mkdir -p "$d"
    if ! $HEAVY "$npudr" toy $x $lg "$d" >/dev/null; then bad "$x log=$lg: npudr toy failed"; continue; fi
    check_proof "$x log=$lg" "$d"
  done
done

# SHA-256 toy (lane L5's block table + companions, src/sha.rs and
# Conformance/Sha.lean).  SHA_CASES: ';'-separated message-length lists.
echo "== SHA toy: AIR export"
"$npudr" export sha > "$out/rust-sha.json"
"$le" sha > "$out/lean-sha.json"
if cmp -s "$out/rust-sha.json" "$out/lean-sha.json"; then pass "export sha byte-identical"; else bad "export sha differs"; fi
if "$le" --roundtrip "$out/rust-sha.json" >/dev/null; then pass "roundtrip sha"; else bad "roundtrip sha"; fi

echo "== SHA toy: honest trace, Rust (npudr shatrace) vs Lean (ZkFormal.Sha.Gen)"
IFS=';' read -ra cases <<< "${SHA_CASES:-0;3;55;56;64;119;120;951;1000;0 3 55 56 64 120 1000}"
for c in "${cases[@]}"; do
  f=$(echo $c | tr ' ' _)
  $HEAVY "$here/.lake/build/bin/np-lean-shatrace" "$out/sha-lean-$f.bin" $c 2>/dev/null
  "$npudr" shatrace "$out/sha-rust-$f.bin" $c
  if cmp -s "$out/sha-lean-$f.bin" "$out/sha-rust-$f.bin"; then pass "sha trace [$c] identical ($(stat -c %s "$out/sha-rust-$f.bin") B)"
  else bad "sha trace [$c] differs"; fi
  if "$npudr" shacheck $c >/dev/null; then pass "sha trace [$c] satisfies every constraint, buses balance"
  else bad "sha trace [$c] fails the AIR"; fi
done

echo "== SHA toy: proofs"
d="$out/sha"; rm -rf "$d"; mkdir -p "$d"
if $HEAVY "$npudr" toy sha 6 "$d" ${SHA_PROOF_LENS:-0 3 56 119} 2>"$d/prove.err"; then
  OFFSETS="0 9 40 $(( $(stat -c %s "$d/proof.bin") / 2 )) $(( $(stat -c %s "$d/proof.bin") - 1 ))" check_proof "sha" "$d"
else bad "sha: npudr toy failed"; cat "$d/prove.err"; fi

[ $fail -eq 0 ] && echo "ALL PASS" || echo "SOME FAILURES"
exit $fail
