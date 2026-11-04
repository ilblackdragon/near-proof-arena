#!/usr/bin/env bash
# E2E-D D-8 constraint-level tests on 2 CPUs (Fib fixture, engine.debug): the review-D7 forged
# node-shape / PAD / wrap-depth mix-ups (review_d7_mixup_debug, adopted from the reviewer's copy),
# the D-7 base-leaf forgeries (tree_d7_shapes_debug), then the non-ignored agg/tree tests.
# Builds the lib tests first. Fails (exit 1) on any failure.  usage: tests_d8.sh OUTDIR
set -uo pipefail
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d8}
O=${1:?outdir}; mkdir -p "$O"
C=${CPUSET:-24-25}
export PATH="$HOME/.cargo/bin:$PATH"
(cd "$D/openvm-sha384" && CARGO_TARGET_DIR=$D/target-test CARGO_ENCODED_RUSTFLAGS='-Ctarget-cpu=native' taskset -c "$C" \
  cargo test --release -j 2 -p openvm-recursion-circuit --lib --no-run > "$O/build_tests.log" 2>&1) || { echo "TESTS_BUILD_FAILED"; grep -E "^error" -A6 "$O/build_tests.log" | head; exit 1; }
T=$(ls -t "$D"/target-test/release/deps/openvm_recursion_circuit-* | grep -v '\.d$' | head -1)
cd "$D/openvm-sha384/crates/recursion" || exit 1
export RAYON_NUM_THREADS=2 PARENT_N_STACK=19
for t in review_d7_mixup_debug tree_d7_shapes_debug; do
  /usr/bin/time -v taskset -c "$C" "$T" --ignored --exact "nv::tree_tests::$t" --nocapture > "$O/$t.log" 2>&1 || { echo "TEST_FAILED $t"; exit 1; }
  echo "TEST_OK $t $(grep -h 'test result' "$O/$t.log")"
done
taskset -c "$C" "$T" nv::agg_tests nv::tree_tests > "$O/agg-tree.log" 2>&1 || { echo "TEST_FAILED agg/tree"; exit 1; }
echo "TEST_OK agg/tree $(grep -h 'test result' "$O/agg-tree.log")"
echo TESTS_D8_DONE
