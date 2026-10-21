#!/usr/bin/env bash
# G2 gate reproduction (lane/pq-stream-commit): clean deps setup -> build -> real-settings G2 chain +
# FINAL + V_d (accept, wrong claim, wrong level, forged final) -> compare proof SHA-256s with MANIFEST.json.
#   reproduce.sh <fresh DEPS dir> [CARGO_TARGET_DIR]
# Needs network for the first setup (pinned stark-backend from GitHub, Plonky3 0.4.3 from crates.io,
# OpenVM v2.1.0-rc.1), the DKT certificate files of lane/pq-dkt-verify @ fb0efdb11 at the paths in
# MANIFEST.json (or CERTS= / EXCL= pointing at copies with the recorded sha256).
# THREADS defaults to 16 and CPUSET to the repository's non-benchmark CPUs.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
NATIVE=$(cd "$HERE/../../../native/recursion" && pwd)
DEPS=${1:?fresh deps dir}
export NEARPROOF_PQ_DEPS=$DEPS
export CARGO_TARGET_DIR=${2:-$DEPS-target}
mkdir -p "$DEPS"
export THREADS=${THREADS:-16}
export CPUSET=${CPUSET:-8-15,24-31}
export CERTS=${CERTS:-$HERE/../../../final-soundness/calc/dkt_certs_o2.json}
export EXCL=${EXCL:-$HERE/../../../final-soundness/lean/DKTCertsO2_big.keys}
# 1. trees: pinned upstreams + stark-backend-unified + openvm-recursion-sha384 + stream overlay + fast CPU overlay
"$NATIVE/setup_cpu_fast_deps.sh"
# 2. build (AVX-512 packing; identical bytes without it, only slower)
( cd "$DEPS/openvm-sha384"
  # Test instrumentation only: save intermediate bytes and exercise V_d controls.
  # Restore the checked source even when the build fails.
  git apply "$HERE/gate-harness.patch"
  trap 'git apply -R "$HERE/gate-harness.patch"' EXIT
  env HEAVY_MEM=${BUILD_MEM:-32G} RUSTFLAGS="-C target-cpu=native" \
  taskset -c "$CPUSET" /data/illia/nearproof-deps/bin/heavy \
  cargo test --locked --release -p openvm-recursion-circuit --lib --no-run \
    --message-format=json-render-diagnostics -j "$THREADS" ) > "$DEPS/build.jsonl"
# Select Cargo's reported test executable, never an old binary by modification time.
EXE=$(python3 - "$DEPS/build.jsonl" <<'PY'
import json, sys
artifacts = []
for line in open(sys.argv[1]):
    event = json.loads(line)
    if (event.get('reason') == 'compiler-artifact'
            and event.get('target', {}).get('name') == 'openvm_recursion_circuit'
            and event.get('profile', {}).get('test') and event.get('executable')):
        artifacts.append(event['executable'])
assert len(set(artifacts)) == 1, artifacts
print(artifacts[-1])
PY
)
mkdir -p "$DEPS/bin"; cp "$EXE" "$DEPS/bin/nv-g2s"
# 3. run (writes $DEPS/ckpt/g2gate/{run.log,L*.proof,FINAL.proof})
BIN="$DEPS/bin/nv-g2s" OUT="$DEPS/ckpt/g2gate" "$NATIVE/run_g2_chain.sh" g2gate
grep -E '^EXIT 0' "$DEPS/ckpt/g2gate/run.log" >/dev/null || { echo "run failed"; tail -20 "$DEPS/ckpt/g2gate/run.log"; exit 1; }
# 4. compare with the manifest
python3 - "$HERE/MANIFEST.json" "$DEPS/ckpt/g2gate" "$DEPS/bin/nv-g2s" <<'PY'
import hashlib, json, sys, os
m = json.load(open(sys.argv[1])); d = sys.argv[2]; bad = 0
for name, want in m["proofs_sha256"].items():
    got = hashlib.sha256(open(os.path.join(d, name), "rb").read()).hexdigest()
    print(f"{name}: {'OK' if got == want else 'MISMATCH'} {got}"); bad += got != want
log = open(os.path.join(d, "run.log")).read()
for marker in m["required_log_lines"]:
    ok = marker in log; print(f"log: {'OK' if ok else 'MISSING'} {marker}"); bad += not ok
# informational: the recorded binary vs the rebuilt one. Byte-identity of the binary is
# not required for byte-identity of the proofs; the proof hashes above are the gate.
want_bin = m.get("binary_sha256", {})
if want_bin:
    got_bin = hashlib.sha256(open(sys.argv[3], "rb").read()).hexdigest()
    rec = next(iter(want_bin.values()))
    print(f"binary: rebuilt {got_bin[:16]} recorded {rec[:16]} "
          f"({'same' if got_bin in want_bin.values() else 'differs (proofs still compared)'})")
sys.exit(1 if bad else 0)
PY
echo "G2 gate: PASS"
