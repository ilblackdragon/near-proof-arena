#!/bin/sh
# Entry point for `make e2e-hostile`.
#
# Submits every hostile package to a running arena server and asserts the
# decisions/gates/reason codes match each case's expect.json, that nothing
# hostile is ever admitted or ranked, and that UI/log-injection payloads come
# back sanitized.
#
# With no server configured it falls back to a local packaging dry-run so the
# target is always runnable (CI without a live judge, local dev).
#
# Config via env:  ARENA_SERVER, ARENA_TOKEN, ARENA_CHALLENGE  (or pass through
# extra args, e.g. ./run.sh --server http://127.0.0.1:8080 --token XXX).
set -eu

HERE="$(cd "$(dirname "$0")" && pwd)"
PY="${PYTHON:-python3}"

# Also run the Rust-side local well-formedness check when cargo is available.
if command -v cargo >/dev/null 2>&1; then
  echo "== local suite well-formedness (cargo) =="
  ( cd "$HERE/../.." && RUSTC_WRAPPER="${RUSTC_WRAPPER:-}" cargo run -q -p proof-mutators --bin check-suite ) \
    | tail -n 2
  echo
fi

echo "== hostile e2e driver =="
exec "$PY" "$HERE/run_hostile.py" "$@"
