#!/usr/bin/env bash
# Run every red-team reproducer. Server/db tests need ARENA_TEST_DATABASE_URL
# (default postgres://arena:arena@127.0.0.1:55471/postgres). Worker tests need
# ARENA_DEV_UNSAFE=1 and bwrap.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
cargo test -j 8 -p arena-server  --test pipeline redteam_formal_cache_covers_npai_bytecode
cargo test -j 8 -p arena-server  --test pipeline redteam_revocation_invalidates_formal_cache
cargo test -j 8 -p arena-server  --test security redteam_concurrent_uploads_respect_byte_quota
cargo test -j 8 -p arena-orchestrator redteam
ARENA_DEV_UNSAFE=1 cargo test -j 8 -p arena-worker --test pipeline redteam
echo "all red-team reproducers passed"
