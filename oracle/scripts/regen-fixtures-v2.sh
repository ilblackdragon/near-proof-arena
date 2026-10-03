#!/usr/bin/env bash
# Regenerate the committed v2 dev fixtures (near/pv86/receipt-transfer-batch/v1,
# challenge near-transfer-receipt-v2) and their provenance. Deterministic and
# byte-reproducible (v2 diagnostics carry no wall-clock timings).
set -euo pipefail
here="$(cd "$(dirname "$0")/.." && pwd)"
cd "$here"
SEED=20261003
cargo build -q -j 8
bin=target/debug/near-arena-oracle
out=fixtures/v2
rm -rf "$out/public" "$out/rejection"
# 20 valid cases = 2 per generator profile, plus the 5 worked examples
$bin gen --scope v2 --seed $SEED --valid 20 --with-example --fixtures-layout --out "$out/public"
# one case per out-of-domain family (14 receipt-level + 4 scheduler-context)
$bin gen --scope v2 --seed $SEED --valid 0 --invalid 18 --fixtures-layout --out "$out/rejection"
rm -f "$out/rejection/params.bin"
$bin params --scope v2 --out "$out/public/runtime-config.json" 2>/dev/null
python3 - "$SEED" "$out" <<'PY'
import json, sys
seed, out = int(sys.argv[1]), sys.argv[2]
pin = dict(l.strip().split("=", 1) for l in open("NEARCORE_PIN") if "=" in l)
common = {
  "schema": "near-arena-fixture-provenance-v1",
  "statement_id": "near/pv86/receipt-transfer-batch/v1",
  "challenge": "near-transfer-receipt-v2",
  "nearcore": {"repo": pin["repo"], "tag": pin["tag"], "commit": pin["commit"]},
  "protocol_version": 86,
  "runtime_config": "RuntimeConfigStore::new(None).get_config(86) (mainnet parameters); see runtime-config.json",
  "generator": {"tool": "near-arena-oracle", "scope": "v2", "seed": seed,
                "command": "scripts/regen-fixtures-v2.sh"},
  "synthetic_state_disclaimer": (
    "SYNTHETIC: every pre-state in these fixtures is a synthetic shard state built by the generator "
    "(random named accounts, balances, access keys, contract data, previous bandwidth-scheduler states, "
    "and in the trie_shapes profile raw keys no nearcore code writes, e.g. 0x0f-prefixed keys, used only "
    "to force every trie-insert case) and executed by the REAL pinned nearcore Runtime::apply in memory "
    "with a single-shard layout. These are NOT mainnet history: pre_state_root values do not appear on any "
    "chain, mainnet is multi-shard, and chain_id=mainnet only selects the mainnet runtime parameters."),
  "historical_replay": "unavailable (see spec/near-transfer-receipt-v2.md, 'Historical replay')",
}
pub = dict(common, layout="params.bin + cases/<name>/{request.bin,witness.bin,expected_claim.bin,state.bin,diagnostics.json}",
           cases=("example-v2-tier{A,B}[-bw][-missed] = the v1 worked example (alice/bob/carol) with the scheduler "
                  "key absent (insert) or present (update), and with a missed chunk; s<seed>-w<i> = generator profiles "
                  "basic,prefix,boundary,repeat,prices,large,bw_state,trie_shapes,missed,shards"),
           params_bin="borsh: string 'near-arena-params-v1' | string statement_id | u32 protocol_version | string chain_id | [u8;32] runtime_config_digest")
rej = dict(common, layout="cases/<name>/{request.bin,witness.bin,state.bin,diagnostics.json} (no expected_claim.bin)",
           purpose="OUT-OF-DOMAIN requests: the judge must not issue them as jobs; checkers must classify them out_of_domain. diagnostics.json records nearcore's actual behaviour.")
for d, name in ((pub, "public"), (rej, "rejection")):
    p = f"{out}/{name}/provenance.json"
    json.dump(d, open(p, "w"), indent=1); open(p, "a").write("\n")
PY
python3 tools/spec_check_v2.py "$out" >/dev/null
echo "v2 fixtures regenerated"
