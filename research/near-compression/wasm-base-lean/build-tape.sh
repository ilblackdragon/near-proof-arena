#!/usr/bin/env bash
# Build `wasmbase-tape` (E2E M3, Tape.lean): compile the C link-time wrapper, then the Lean exe.
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p .lake/build
cc -O2 -c tape_shim.c -I "$(lean --print-prefix)/include" -o .lake/build/tape_shim.o
lake build wasmbase-tape
