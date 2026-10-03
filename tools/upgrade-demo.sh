#!/usr/bin/env bash
# Protocol-upgrade governance demo on a REAL historical boundary:
# nearcore 2.12.0 (STABLE_PROTOCOL_VERSION 84) -> 2.13.4 (86).
# No nearcore release newer than 2.13.4 exists, so nothing here is invented:
# the arena's only signed formal challenge is the PV86 one, the PV84 side is
# exercised as (a) the real upgrade-monitor diff and (b) server-level fixtures
# (server/arena-server/tests/supersession.rs). See docs/PROTOCOL_UPGRADES.md §7.
#
# usage: tools/upgrade-demo.sh [OUT_DIR]
#   NEARCORE_CLONE   nearcore clone with both tags (default /data/illia/nearproof-deps/nearcore-upgrade-monitor)
#   SKIP_SERVER=1    skip the Postgres-backed server test
set -euo pipefail
ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"
OUT="${1:-$(mktemp -d)}"
mkdir -p "$OUT"
NC="${NEARCORE_CLONE:-/data/illia/nearproof-deps/nearcore-upgrade-monitor}"
V1=challenges/chl_5ef2bc7d2068219635426e47ca46bfbb.json
ORACLE=oracle/target/debug/near-arena-oracle
export RUSTC_WRAPPER="${RUSTC_WRAPPER:-sccache}"
step() { printf '\n== %s\n' "$*"; }
expect_exit() { # expect_exit CODE cmd...
  local want=$1; shift
  set +e; "$@"; local got=$?; set -e
  if [[ $got -ne $want ]]; then echo "FAIL: expected exit $want, got $got: $*" >&2; exit 1; fi
  echo "ok: exit $got (expected $want)"
}

cargo build -q -j 8 -p upgrade-monitor -p arena-admin
[[ -x $ORACLE ]] || (cd oracle && cargo build -q -j 8)

step "1. upgrade monitor: 2.12.0 (PV84) -> 2.13.4 (PV86); exit 3 = REVALIDATION_REQUIRED"
expect_exit 3 target/debug/upgrade-monitor --repo "$NC" --old 2.12.0 --new 2.13.4 \
  --impact-map spec/impact-map.toml --json "$OUT/nearcore-2.12.0-to-2.13.4.json" --markdown "$OUT/nearcore-2.12.0-to-2.13.4.md"
for f in json md; do
  if cmp -s "$OUT/nearcore-2.12.0-to-2.13.4.$f" "docs/upgrade-reports/nearcore-2.12.0-to-2.13.4.$f"; then
    echo "ok: report .$f is byte-identical to the committed one (deterministic)"
  else
    echo "NOTE: report .$f differs from docs/upgrade-reports (impact map or monitor changed since it was committed)"
  fi
done
step "1b. control: 2.13.4 -> 2.13.4 must be NO_SEMANTIC_CHANGE_DETECTED (exit 0)"
expect_exit 0 target/debug/upgrade-monitor --repo "$NC" --old 2.13.4 --new 2.13.4 \
  --impact-map spec/impact-map.toml --json "$OUT/self.json" --markdown "$OUT/self.md"

step "2. impact on the challenge's obligations / spec definitions (spec/impact-map.toml)"
python3 - "$OUT/nearcore-2.12.0-to-2.13.4.json" <<'EOF'
import json, sys
r = json.load(open(sys.argv[1]))
print("verdict:", r.get("verdict"))
imp = r["impact"]
print("reopen obligations:", ", ".join(imp["obligations_to_reopen"]))
print("spec definitions to revalidate:", ", ".join(imp["spec_definitions_to_revalidate"]))
print("fixtures to regenerate:", ", ".join(imp["fixtures_to_regenerate"]))
for h in imp["rule_hits"]:
    print(f"  rule {h['rule']}: {len(h['files'])} changed input(s) -> {', '.join(h['obligations'])}")
print(f"  [default] (unmapped, fail-closed): {len(imp['unmapped_files'])} input(s)")
p = r["protocol"]
print("protocol:", p["old_stable"], "->", p["new_stable"], "; newly stable features:", ", ".join(p["newly_stable_features"]))
EOF

step "3. fail closed on protocol versions"
python3 -c "
import json; c = json.load(open('$V1'))
c['protocol_version'] = 84; c['nearcore'] = {'repo': c['nearcore']['repo'], 'tag': '2.12.0', 'commit': '1144e310f7e70734453167cb07f8cccf28987eb8'}
json.dump(c, open('$OUT/pv84-variant.json', 'w'), indent=1)"
echo "-- the PV86 oracle refuses to serve a PV84 challenge:"
expect_exit 3 "$ORACLE" gen --seed 1 --valid 1 --out "$OUT/refused" --challenge "$OUT/pv84-variant.json"
echo "-- and serves the PV86 challenge:"
rm -rf "$OUT/cases"
expect_exit 0 "$ORACLE" gen --seed 84 --valid 1 --invalid 13 --out "$OUT/cases" --challenge "$V1"
WPV=$(python3 -c "
import json, glob
for d in sorted(glob.glob('$OUT/cases/*/diagnostics.json')):
    j = json.load(open(d))
    if j['generator']['invalid_kind'] == 'wrong_protocol_version': print(d.rsplit('/', 1)[0])" | head -1)
OK=$(python3 -c "
import json, glob
for d in sorted(glob.glob('$OUT/cases/*/diagnostics.json')):
    j = json.load(open(d))
    if j['in_domain']: print(d.rsplit('/', 1)[0])" | head -1)
echo "-- a request embedding protocol_version 85 is refused, a PV86 request accepted:"
expect_exit 3 "$ORACLE" check-request --request "$WPV/request.bin" --challenge "$V1"
expect_exit 0 "$ORACLE" check-request --request "$OK/request.bin" --challenge "$V1"
echo "-- the worker's RequestPin (runners/worker jobs.rs) applies the same header check before any sandbox runs:"
cargo test -q -j 8 -p arena-worker --lib request_pin 2>&1 | grep -E "test result|passed|failed"

step "4. signed challenges: v1 (PV86, baseline null) and its successor v1.1 (baselines pinned) verify; supersession chain"
target/debug/arena-admin verify --pubkey challenges/governance-local.pub --pubkey challenges/governance-dev.pub --all-in challenges

if [[ "${SKIP_SERVER:-0}" != 1 ]]; then
  step "5. server: A (PV84) superseded by B (PV86): history intact + labelled, boards separate, A closed, no reopen"
  cargo test -q -j 8 -p arena-server --test supersession 2>&1 | grep -E "^test |test result"
fi
echo
echo "upgrade demo OK; artifacts in $OUT"
