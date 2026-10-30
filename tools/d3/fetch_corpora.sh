#!/usr/bin/env bash
# Obtain and verify the pinned regression corpora for the `corpus-content-gates` CI job (W01).
# Runbook: tools/d3/CORPUS_RUNNER_RUNBOOK.md.
#
# The trust anchor is the committed content manifest
# (docs/evidence/lean-chunk-L7/corpus-manifest.json): whatever the source, the corpora are accepted
# only if `corpus_manifest.py --verify` reproduces every family's case count, byte total and digest.
# Transport checksums (SHA256SUMS) only detect a broken download early.
#
# Sources, first match wins:
#   1. NEAR_CORPORA_DIR already holds all six families (a runner that mounts them): verify only.
#   2. NEAR_CORPORA_SOURCE = an rsync source (local path or host:path) holding the families:
#      rsync each family into NEAR_CORPORA_DIR, then verify.
#   3. NEAR_CORPORA_URL = a base URL serving <family>.tar.zst and SHA256SUMS: download, check the
#      transport sums, extract into NEAR_CORPORA_DIR, then verify.
# Exit codes: 0 verified; 1 content drift / missing family / transport failure; 2 not configured.
set -euo pipefail

here="$(cd "$(dirname "$0")/../.." && pwd)"
manifest="${NEAR_CORPORA_MANIFEST:-$here/docs/evidence/lean-chunk-L7/corpus-manifest.json}"
families=(d1run d2corpus.v2 d3c7 d3c8 d3c9 d3c10)

if [ -z "${NEAR_CORPORA_DIR:-}" ]; then
  echo "::error::NEAR_CORPORA_DIR is not set (the corpora root the gate verifies)" >&2
  exit 2
fi
mkdir -p "$NEAR_CORPORA_DIR"

have_all() {
  local f
  for f in "${families[@]}"; do
    [ -d "$NEAR_CORPORA_DIR/$f" ] || return 1
  done
}

if have_all; then
  echo "corpora present under $NEAR_CORPORA_DIR; verifying in place"
elif [ -n "${NEAR_CORPORA_SOURCE:-}" ]; then
  command -v rsync >/dev/null || { echo "::error::rsync not installed" >&2; exit 1; }
  for f in "${families[@]}"; do
    echo "rsync $NEAR_CORPORA_SOURCE/$f -> $NEAR_CORPORA_DIR/$f"
    rsync -a --delete "$NEAR_CORPORA_SOURCE/$f/" "$NEAR_CORPORA_DIR/$f/"
  done
elif [ -n "${NEAR_CORPORA_URL:-}" ]; then
  command -v curl >/dev/null || { echo "::error::curl not installed" >&2; exit 1; }
  command -v zstd >/dev/null || { echo "::error::zstd not installed" >&2; exit 1; }
  dl="$(mktemp -d)"
  trap 'rm -rf "$dl"' EXIT
  curl -fsSL "$NEAR_CORPORA_URL/SHA256SUMS" -o "$dl/SHA256SUMS"
  for f in "${families[@]}"; do
    curl -fsSL "$NEAR_CORPORA_URL/$f.tar.zst" -o "$dl/$f.tar.zst"
  done
  (cd "$dl" && sha256sum --check --strict SHA256SUMS)
  for f in "${families[@]}"; do
    rm -rf "${NEAR_CORPORA_DIR:?}/$f"
    zstd -dc "$dl/$f.tar.zst" | tar -x -C "$NEAR_CORPORA_DIR"
  done
else
  echo "::error::corpora missing under $NEAR_CORPORA_DIR and no NEAR_CORPORA_SOURCE / NEAR_CORPORA_URL configured" >&2
  exit 1
fi

have_all || { echo "::error::a corpus family is missing after fetch" >&2; exit 1; }
python3 "$here/tools/d3/corpus_manifest.py" --corpora "$NEAR_CORPORA_DIR" --verify "$manifest"
