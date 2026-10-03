#!/usr/bin/env bash
# Offline re-verification of the historical fixtures (no network):
#  1. near-arena-historical replay: re-runs the pinned nearcore Runtime::apply on
#     apply_witness.bin (authentic mainnet trie nodes) and checks witness.bin and
#     expected_claim.bin are reproduced byte for byte and the case is in domain;
#  2. nearspec-check (compiled Lean reference semantics): derives the claim from
#     request.bin + witness.bin and decides NearRelation;
#  3. file digests match diagnostics.json, and provenance.json's recorded anchors.
# Requires: ../scripts/link-nearcore.sh done; Lean checker built (spec/lean: lake build)
# or NEARSPEC_CHECK pointing at a nearspec-check binary built from the same sources.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$here/../.." && pwd)"
cases="${1:-$repo/oracle/fixtures/historical/cases}"
(cd "$here" && cargo build -q -j 8)
"$here/target/debug/near-arena-historical" replay "$cases"/*/
lean="${NEARSPEC_CHECK:-$repo/spec/lean/.lake/build/bin/nearspec-check}"
if [[ -x "$lean" ]]; then
  "$lean" "$cases"
else
  echo "nearspec-check not found at $lean (build spec/lean or set NEARSPEC_CHECK); skipped" >&2
  exit 1
fi
python3 - "$cases" <<'PY'
import hashlib, json, os, sys
root = sys.argv[1]
bad = 0
for c in sorted(os.listdir(root)):
    d = os.path.join(root, c)
    diag = json.load(open(os.path.join(d, "diagnostics.json")))
    prov = json.load(open(os.path.join(d, "provenance.json")))
    for f, want in diag["digests"].items():
        got = "sha256:" + hashlib.sha256(open(os.path.join(d, f), "rb").read()).hexdigest()
        if got != want:
            print(f"DIGEST_MISMATCH {c}/{f}"); bad += 1
    if prov["claim"] != diag["claim"]:
        print(f"PROVENANCE_CLAIM_MISMATCH {c}"); bad += 1
    failed = sorted(k for k, v in prov["anchors"].items() if not v["ok"])
    print(f"{c}: class={prov['fixture_class']} anchors_ok={sum(v['ok'] for v in prov['anchors'].values())}/{len(prov['anchors'])} not_ok={failed}")
sys.exit(1 if bad else 0)
PY
