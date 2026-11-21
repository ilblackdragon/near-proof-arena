#!/usr/bin/env bash
# E2E-D M8 item 4: a one-template D0a tree at depth 0 (the wrap verifies the template leaf itself;
# no P_2, no PAD_L), one leaf family at the L geometry so the wrap's heights do not reveal the
# class. Chunk: D-9's L1 (class L); its D-9 template leaf is reused when it is the same proof
# (NEARPROOF_TREE_REUSE_LEAVES: native verification, heights, root, statement checked).
#   usage: depth0_m8.sh   (writes /data/illia/nearproof-deps/pq-e2e-m8/d0/<chunk>)
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
D9=/data/illia/nearproof-deps/pq-e2e-d9
export NEARPROOF_PQ_DEPS=/data/illia/nearproof-deps/pq-e2e-m8 OUT_ROOT=/data/illia/nearproof-deps/pq-e2e-m8
export PROVER=${PROVER:-/data/illia/nearproof-deps/pq-e2e-m8/drv2/release/nearproof-chunk-e2e}
export CLASS_DIRS="$D9/b8/d1_10-h10075-s0 $D9/b8/d1_10-h10056-s2 $D9/b8/d1_01-h10040-s3"
export NEARPROOF_TREE_CONFIRM="$D9/b8/d1_09-h10150-s3 $D9/b8/d1_05-h10085-s2 $D9/b8/d1_09-h10012-s0"
export NEARPROOF_TREE_LEAF_PARAMS=ns20lb2 NEARPROOF_TREE_LEAF_FAMILIES=one NEARPROOF_TREE_LEAF_GEOM=20,19
export NEARPROOF_TREE_REUSE_LEAVES=$D9/tree9/d1_01-h10040-s3
CH=$D9/b8/d1_01-h10040-s3
CPUSET=${CPUSET:-0-7} VERIFY_CPU=${VERIFY_CPU:-8} "$HERE/run_tree.sh" d0 - 0 "$CH" "$CH/claim.bin"
