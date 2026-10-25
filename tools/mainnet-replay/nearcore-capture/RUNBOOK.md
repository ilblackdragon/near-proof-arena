# Reproducing witness capture and extending it to all shards

## What this captures

The successful pilot used pinned nearcore **2.13.4 / PV86**, commit
`44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, with Rust **1.93.0**.
It ran a non-validator **stateful shadow-validation node**: sync shard state, execute chunks,
construct their state witnesses, export them and validate them natively. This is not a subscription
to the validator witness feed. Stateless replay needs the witness, not the complete shard database;
this acquisition method needs the database to construct witnesses without a validator key.

A cooperating validator exporting reconstructed witnesses, required code and chain/epoch context
is an alternative that avoids our state-sync cost. Ordinary RPC full chunks alone omit the state
proofs. Ordinary non-validator peers are not assigned the validator-directed witness-part stream.

The pilot captured 1,223 shard-13 witnesses and full chunks, heights 221489407–221490629. They passed
[native/Lean diagnostic replay](../../../docs/evidence/lean-chunk-completion/mainnet-w13-shard13/README.md).
Each capture contains one reconstructed chunk witness, not the erasure-coded network parts.

## Paths and artifacts from the successful run

| Artifact | Location |
|---|---|
| Isolated nearcore source | `/tmp/nearproof-nearcore-w13` |
| Build target | `/tmp/nearproof-neard-target` |
| Runtime root | `/data/illia/nearproof-deps/mainnet-w13` |
| Capture binary | `bin/neard` under runtime root |
| Home/database/log/status | `home/`, `home/data/`, `home/node.log`, `home/capture-status.json` |
| Continuous exports | `exports/` |
| Copied launcher/configuration/patch | `run/` |
| Build and initial network identities | `build-evidence.json`, `home/setup-evidence.json` |
| Corrected startup/config identities | `restart-evidence.json` |
| Claims and replay results | `replay-cases/`, `replay-results/`, `replay-provenance/` |

Preserve the database until claims and all required epoch/chain facts have been exported. A raw
witness alone is insufficient to reproduce claim construction. The node is non-archival: continuing
indefinitely may garbage-collect old context. Stop and snapshot/export between acquisition windows.
Do not delete the database or reinitialize the successful pilot to collect another shard.

## Build from a clean pinned checkout

Set paths for the new run; these are examples, not storage sizing guarantees:

```sh
CAPTURE_REPO=/data/illia/nearproof
CAPTURE_SRC=/data/illia/nearproof-deps/nearcore-capture-all
CAPTURE_ROOT=/data/illia/nearproof-deps/mainnet-w13-all
CAPTURE_TARGET=/tmp/nearproof-neard-all-target

git clone https://github.com/near/nearcore.git "$CAPTURE_SRC"
git -C "$CAPTURE_SRC" checkout --detach 44f7ae6cd7ef08bab604e20a473bf77e35d4c993
git -C "$CAPTURE_SRC" apply "$CAPTURE_REPO/tools/mainnet-replay/nearcore-capture/export.patch"
cd "$CAPTURE_SRC"
CARGO_BUILD_JOBS=8 CARGO_TARGET_DIR="$CAPTURE_TARGET" \
  CARGO_PROFILE_RELEASE_LTO=false CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16 \
  cargo +1.93.0 build -p neard --release --locked --no-default-features \
  --features json_rpc,shadow_chunk_validation
mkdir -p "$CAPTURE_ROOT/bin" "$CAPTURE_ROOT/run" "$CAPTURE_ROOT/exports"
install -m 755 "$CAPTURE_TARGET/release/neard" "$CAPTURE_ROOT/bin/neard"
cp "$CAPTURE_REPO/tools/mainnet-replay/nearcore-capture/"{configure.py,supervise.py,export.patch} "$CAPTURE_ROOT/run/"
"$CAPTURE_ROOT/bin/neard" --version
sha256sum "$CAPTURE_ROOT/bin/neard" "$CAPTURE_ROOT/run/"{export.patch,configure.py,supervise.py} > "$CAPTURE_ROOT/build.sha256"
```

Run Cargo from the nearcore checkout so its `.cargo/config.toml` applies. Record the source commit,
patch, toolchain, build flags and binary hash. Install Rust 1.93.0 first if it is absent.
The capture patch is independent of the later diagnostic claim-export patch in `../native/`.

## Initialize and choose shard coverage

```sh
"$CAPTURE_ROOT/bin/neard" --home "$CAPTURE_ROOT/home" init --chain-id mainnet --download-config rpc
python3 "$CAPTURE_ROOT/run/configure.py" --home "$CAPTURE_ROOT/home" --shard 13
```

The configurator checks public mainnet PV86, checks the requested live shard ID, gets fresh public
boot peers, and writes `setup-evidence.json`. It refuses an existing database. Public FastNear RPC
worked without credentials. No validator/staking key is used.

For a single shard, use its current ID with `--shard`. **The configurator currently has no
`--all-shards` flag.** To track all shards, make this explicit edit **before first startup**:

```sh
python3 - "$CAPTURE_ROOT/home" <<'PY'
import hashlib, json, sys, urllib.request
from pathlib import Path
home = Path(sys.argv[1])
assert not (home / 'data').exists(), 'use a fresh isolated home'
request = urllib.request.Request('https://rpc.mainnet.fastnear.com',
    json.dumps({'jsonrpc':'2.0','id':'capture','method':'EXPERIMENTAL_protocol_config',
                'params':{'finality':'final'}}).encode(), headers={'Content-Type':'application/json'})
with urllib.request.urlopen(request, timeout=30) as response:
    protocol = json.load(response)['result']
assert protocol['protocol_version'] == 86, 'outside pinned target'
layout = next(iter(protocol['shard_layout'].values()))
config_path = home / 'config.json'
config = json.loads(config_path.read_text())
config['tracked_shards_config'] = 'AllShards'
config_path.write_text(json.dumps(config, indent=2) + '\n')
evidence_path = home / 'setup-evidence.json'
evidence = json.loads(evidence_path.read_text())
evidence.update(selected_shards=layout['shard_ids'], tracking_policy='AllShards',
                shard_layout=protocol['shard_layout'], scope='all-shard acquisition; not replay acceptance',
                config_sha256=hashlib.sha256(config_path.read_bytes()).hexdigest())
evidence_path.write_text(json.dumps(evidence, indent=2) + '\n')
print('Tracking current shards:', layout['shard_ids'])
PY
```

The observed PV86 layout had IDs `[10,11,1,8,9,6,7,4,12,13]`; derive the live layout instead of
assuming IDs 0–9. One AllShards node needs all shard states. Alternatively use separate fresh homes
on separate hosts with `--shard ID`, and collect an overlapping common block window. Same-host nodes
need distinct RPC, metrics and P2P ports: edit `rpc.addr`, `rpc.prometheus_addr`, `network.addr`, and
pass the matching `--rpc http://127.0.0.1:PORT/status` to each supervisor. Give each its own service,
home, exports and resource budget. Do not point two processes at one database.

## Start a bounded persistent service

The successful single-shard pilot used this service with 32 GiB memory, eight CPU equivalents,
35 GiB home allocation, 15 GiB free-space reserve, and 1,200 captures:

```sh
systemd-run --user --unit=nearproof-mainnet-w13 --collect \
  -p MemoryMax=32G -p MemorySwapMax=0 -p CPUQuota=800% -p IOWeight=20 \
  /usr/bin/python3 "$CAPTURE_ROOT/run/supervise.py" \
  --binary "$CAPTURE_ROOT/bin/neard" --home "$CAPTURE_ROOT/home" \
  --exports "$CAPTURE_ROOT/exports" \
  --max-data-gib 35 --reserve-gib 15 --max-captures 1200
```

**Change the unit name and budgets for an all-shard run.** The above is the measured pilot recipe,
not a tested all-shard capacity plan. Set `--max-data-gib` from provisioned storage and choose memory
and CPU budgets for the host. Keep home and exports on the same filesystem: the free-space guard
checks the home's filesystem, and the home-allocation limit does not count sibling exports.
Pilot final home allocation was about 22.3 GiB, with 219 MiB exports; other shards may be much larger.

The capture limit is an **aggregate safety ceiling**, not a coverage criterion. At ten shards,
1,200 captures could be only about 120 block heights. Even 10,000 captures do not prove 1,000 complete
all-shard heights: early-syncing shards can consume the quota while another shard still syncs.
Choose a larger ceiling (for example 100,000, subject to provisioned disk), monitor per-shard coverage,
and stop after independently verifying the common window. A ceiling-triggered stop with gaps requires
resuming with a larger ceiling or a new window, not declaring success. Counts include existing exports
on restart. The 15-second polling interval permits overshoot: the pilot stopped at 1,223 rather than 1,200.

## Monitor, stop and resume

```sh
systemctl --user status nearproof-mainnet-w13.service
cat "$CAPTURE_ROOT/home/capture-status.json"
tail -n 20 "$CAPTURE_ROOT/home/node.log"
curl --fail http://127.0.0.1:3038/status
curl --fail http://127.0.0.1:3039/metrics
systemctl --user stop nearproof-mainnet-w13.service
```

Use the actual unit/ports for a new node. This transient user service survives the chat/session but
is not an installed reboot-start service. After a clean stop and unit collection, rerun the launch
command with the **same home**, desired capture ceiling and existing exports; do not run init or
configure again. Wait for RocksDB shutdown before restarting or running offline claim export.

Sync stages are epoch proof → recent headers → state parts → apply state → catch up → live chunks.
`/status` may still show genesis PV29/height during state sync; use `node.log`'s `parts (N/T)` progress.
State-sync parts are not witnesses and their count is unrelated to witnesses per chunk.
The current supervisor tolerates historical startup status, but stops on a recent synced protocol
mismatch or any protocol beyond PV86. Do not restore the earlier `syncing=false => reject PV29` check.

The first attempt reached 243/371 state parts before its sync target became stale and nearcore reset
its database. The corrected attempt used 24 peer downloads, per-shard concurrency 24, apply concurrency
4, and a 60-second response timeout. These are global/per-shard caps, not 24 downloads for each shard
simultaneously. It restarted at 23:30 UTC on October 24; state application began around 03:11 UTC on
October 25; the capture target was reached at 04:45 UTC. These timings are observations, not an ETA.
Monitor stalls, stale-target resets and limits; a running process alone is not successful acquisition.

## Output, completeness and handoff to replay

Each `exports/hHEIGHT-sSHARD-CHUNKHASH/` contains:

- `state_witness.borsh`: reconstructed witness with its main and optional implicit transitions.
- `chunk.borsh`: full chunk, including transactions and previous outgoing receipts.
- `block.borsh`, `parent_header.borsh`: containing block and parent header.
- `code/*.wasm`: available accessed/deployed code, named by base58 hash.
- `capture.json`: identities, witness size/hash and explicit missing-code entries; written last.
- `native-validation.json`: asynchronous shadow verdict, when available. Missing is not acceptance.

Exports bypass the node's bounded latest-witness ring. Copy the complete directory, not just raw
witness files. Preserve config and binary/patch/launcher hashes, protocol/layout, node context,
per-case verdicts and errors. Node keys and the database should not be checked into Git.

For all-shard acquisition, select at least 1,000 consecutive PV86 heights **after every required shard
can export**, and audit against each canonical block's full chunk slots. Match every newly included
chunk by `(block hash, shard ID, chunk hash)`; distinguish repeated/missed slots. Check capture files,
code availability and verdicts, not just minimum/maximum heights or total files. The shadow hook has
an upstream layout-change limitation: use a stable-layout window for this run; real resharding/rare
features need separate validator fixtures. Fork captures must be checked against canonical context.

Capture the independent block denominator using `gate.py capture --start HEIGHT --blocks 1000 --out
NEW_CAPTURE_DIR` (see [the full gate contract](../README.md)). Stop/snapshot the node, then use
[the native database exporter](../native/README.md) to export claims and replay. `replay-export` walks
all capture directories, including multiple shards. `shard_replay.py --shard ID` diagnoses each shard;
it cannot certify all-shard coverage. Full `gate.py` import/replay still needs the cold native adapter
that independently verifies supplied claim facts. Do not substitute a successful diagnostic report
for that adapter or weaken the all-shard gate.
