#!/bin/bash
export RUST_LOG=info
export JOLT_PATH=/data/illia/pq-tail-architecture-20261024/jolt-target/ci/jolt
exec timeout 10800 taskset -c 8-15,24-31 /data/illia/pq-tail-architecture-20261024/jolt-target/ci/near-chunk-fold
