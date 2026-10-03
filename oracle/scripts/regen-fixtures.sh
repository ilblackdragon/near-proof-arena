#!/usr/bin/env bash
# Regenerate the committed dev fixtures (deterministic) and their provenance.
set -euo pipefail
here="$(cd "$(dirname "$0")/.." && pwd)"
cd "$here"
SEED=20261003
cargo build -q -j 8
bin=target/debug/near-arena-oracle
rm -rf fixtures/public fixtures/rejection
$bin gen --seed $SEED --valid 18 --with-example --fixtures-layout --out fixtures/public
$bin gen --seed $SEED --valid 0 --invalid 14 --fixtures-layout --out fixtures/rejection
rm -f fixtures/rejection/params.bin
$bin params --out fixtures/public/runtime-config.json 2>/dev/null
python3 - "$SEED" <<'PY'
import json, sys
seed = int(sys.argv[1])
pin = dict(l.strip().split("=", 1) for l in open("NEARCORE_PIN") if "=" in l)
common = {
  "schema": "near-arena-fixture-provenance-v1",
  "statement_id": "near/pv86/receipt-transfer-batch/v0",
  "nearcore": {"repo": pin["repo"], "tag": pin["tag"], "commit": pin["commit"]},
  "protocol_version": 86,
  "runtime_config": "RuntimeConfigStore::new(None).get_config(86) (mainnet parameters); see runtime-config.json",
  "generator": {"tool": "near-arena-oracle", "seed": seed,
                "command": "scripts/regen-fixtures.sh"},
  "synthetic_state_disclaimer": (
    "SYNTHETIC: every pre-state in these fixtures is a synthetic shard state built by the generator "
    "(random named accounts, balances, access keys, contract data) and executed by the REAL pinned "
    "nearcore Runtime::apply in memory. These are NOT mainnet history: pre_state_root values do not "
    "appear on any chain, and chain_id=mainnet only selects the mainnet runtime parameters."),
  "historical_replay": "unavailable (see spec/near-transfer-receipt-v1.md, 'Historical mainnet replay')",
}
pub = dict(common, layout="params.bin + cases/<name>/{request.bin,witness.bin,expected_claim.bin,state.bin,diagnostics.json}",
           cases="example-tierA/B = docs/research/first-slice.md worked example; s<seed>-v<i> = generator profiles basic,prefix,boundary,repeat,prices,large",
           params_bin="borsh: string 'near-arena-params-v1' | string statement_id | u32 protocol_version | string chain_id | [u8;32] runtime_config_digest")
rej = dict(common, layout="cases/<name>/{request.bin,witness.bin,state.bin,diagnostics.json} (no expected_claim.bin)",
           purpose="OUT-OF-DOMAIN requests: the judge must not issue them as jobs; checkers must classify them out_of_domain. diagnostics.json records nearcore's actual behaviour.")
json.dump(pub, open("fixtures/public/provenance.json", "w"), indent=1); open("fixtures/public/provenance.json", "a").write("\n")
json.dump(rej, open("fixtures/rejection/provenance.json", "w"), indent=1); open("fixtures/rejection/provenance.json", "a").write("\n")
PY
python3 tools/spec_check.py fixtures >/dev/null
echo "fixtures regenerated"
