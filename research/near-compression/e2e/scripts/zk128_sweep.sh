#!/usr/bin/env bash
# HVZK-WHIR proof-size overhead sweep (Plonky3 3acc8b7 + whir/examples/zk128.rs, see
# patches/plonky3-zk128-example.patch). One core each; sizes are deterministic, times are not.
set -uo pipefail
B=${ZK128:-/data/illia/nearproof-deps/pq-e2e-zk/p3zk/target/release/examples/zk128}
run() { timeout 3600 taskset -c "${CPU:-14}" "$B" "$@" 2>&1 | tail -1; }
run 16 100 2 16 16 5 capacity     # the RESULTS.md calibration point (100-bit, rate 1/4)
run 18 100 2 16 16 5 capacity
run 18 128 1 0 3 3 johnson        # the octic 128-bit Johnson config that panicked in the bench
run 16 128 6 30 16 5 johnson      # PQ-track-like: 128-bit Johnson, rate 1/64, z = 30
run 18 128 6 30 16 5 johnson
run 16 128 6 30 3 3 johnson
run 18 128 6 30 3 3 johnson
