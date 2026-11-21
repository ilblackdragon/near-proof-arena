#!/usr/bin/env bash
# E2E-D M8 tests of the heterogeneous tree (nv/htree.rs) on the Fib fixture: the non-ignored layout
# checks (htree_spec_checks), then the ignored end-to-end test (htree_fib_end_to_end: templates A, B
# of two vks + INIT / FINAL stubs, one P_2 over the template set, the wrap; constraint-level
# negatives), then the D-9 regression tests (tree_d9_wrap_set_debug and the non-ignored agg/tree
# tests). Builds the lib tests first. Fails (exit 1) on any failure.
#   usage: tests_m8.sh OUTDIR    (env TESTS: the ignored tests to run; CPUSET, THREADS)
set -euo pipefail
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-m8}
O=${1:?outdir}; mkdir -p "$O"
C=${CPUSET:-0-3}
export PATH="$HOME/.cargo/bin:$PATH"
(cd "$D/openvm-sha384" && CARGO_TARGET_DIR=$D/target-test CARGO_ENCODED_RUSTFLAGS='-Ctarget-cpu=native' taskset -c "$C" \
  cargo test --release -j 4 -p openvm-recursion-circuit --lib --no-run > "$O/build_tests.log" 2>&1) || { echo "TESTS_BUILD_FAILED"; grep -E "^error" -A6 "$O/build_tests.log" | head; exit 1; }
T=$(ls -t "$D"/target-test/release/deps/openvm_recursion_circuit-* | grep -v '\.d$' | head -1)
cd "$D/openvm-sha384/crates/recursion" || exit 1
export RAYON_NUM_THREADS=${THREADS:-4} PARENT_N_STACK=19
taskset -c "$C" "$T" nv::htree_tests::htree_spec_checks > "$O/htree_spec_checks.log" 2>&1 || { echo "TEST_FAILED htree_spec_checks"; exit 1; }
echo "TEST_OK htree_spec_checks $(grep -h 'test result' "$O/htree_spec_checks.log")"
for t in ${TESTS:-htree_tests::htree_fib_end_to_end tree_tests::tree_d9_wrap_set_debug}; do
  n=${t##*::}
  /usr/bin/time -v taskset -c "$C" "$T" --ignored --exact "nv::$t" --nocapture > "$O/$n.log" 2>&1 || { echo "TEST_FAILED $t"; exit 1; }
  echo "TEST_OK $t $(grep -h 'test result' "$O/$n.log")"
done
taskset -c "$C" "$T" nv::agg_tests nv::tree_tests > "$O/agg-tree.log" 2>&1 || { echo "TEST_FAILED agg/tree"; exit 1; }
echo "TEST_OK agg/tree $(grep -h 'test result' "$O/agg-tree.log")"
echo TESTS_M8_DONE
