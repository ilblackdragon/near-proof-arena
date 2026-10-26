# W13 all-shard capture runbook

This runbook brings up **one isolated, pinned nearcore 2.13.4 node that tracks every mainnet shard
and exports a witness for every new chunk**. It then takes that capture through `make w13-gate`.
It extends the single-shard pilot ([nearcore-capture/README.md](nearcore-capture/README.md),
[nearcore-capture/RUNBOOK.md](nearcore-capture/RUNBOOK.md)) and the gate contract
([README.md](README.md)). Read those first: they define the export format, the supervisor and the
pass criteria. This file adds only what changes for all shards.

**Status.** No all-shard run has been done yet. The figures from the pilot are measured, and they are
labelled as such. Every all-shard figure below is an **estimate** with its source. `make w13-gate`
also still needs the cold native adapter (README "Native adapter contract"), which is not
implemented. So this runbook gets a capture to the gate's input; it cannot make the gate pass yet.

Pins: nearcore `44f7ae6cd7ef08bab604e20a473bf77e35d4c993` (2.13.4, PV86, db 49), Rust 1.93.0,
features `json_rpc,shadow_chunk_validation`, plus `nearcore-capture/export.patch`.

Do **not** reuse or touch the pilot node at `/data/illia/nearproof-deps/mainnet-w13`. Its database is
the context for the existing shard-13 claims (`replay-cases/`). Use a fresh home on the new machine.

## 1. Sizing (estimates, with sources)

| Resource | Plan for | Source / reasoning |
|---|---|---|
| CPU | ≥ 8 cores / 16 threads with AVX | NEAR mainnet RPC and archival hardware pages, both updated 2026-03-17: "8-Core (16-Thread) Intel i7/Xeon or equivalent" ([RPC](https://near-nodes.io/rpc/hardware-rpc), [archival](https://near-nodes.io/archival/hardware-archival)). Shadow validation re-executes every chunk on top of normal application, so 16+ cores is better. |
| RAM | **64 GiB** (32 GiB is the documented floor for RPC) | RPC page: 32 GB recommended, 16 GB minimum. On top of that come the shadow-validation and witness-export overhead, plus the configured caches: the pilot config has `col_state_cache_size` 3 GiB, and `trie_cache.per_shard_max_bytes` up to 3 GB on the hot shards. `load_mem_tries_for_tracked_shards` stays `false`, as in the pilot. Turning it on for all shards needs far more RAM than is budgeted here. |
| Node database (non-archival, `gc_num_epochs_to_keep = 3`) | **4 TB NVMe** | RPC page: "4TB NVMe SSD" recommended, minimum "2.5TB SATA3-class SSD supporting at least 15k IOPS and 800 MiBps". The page also notes `gc_num_epochs_to_keep` defaults to 5 with a minimum of 3. Pilot, measured: a one-shard home grew to 22–24 GiB (`home_allocated_bytes` 23,954,968,576 in `capture-status.json`). Shard 13 is a quiet shard, so do not scale that number linearly. |
| Archival alternative | 3 TB SSD hot + 115 TB cold | Archival page. You do **not** need it here: the capture node is non-archival (`archive: false`). Archival is only needed to regenerate witnesses for historical heights, which this runbook does not do. |
| Exports + replay cases | **≥ 200 GiB** on the same filesystem as the home | Pilot, measured: 1,223 captures came to 219 MiB of exports plus 162 MiB of claim/witness cases, about 0.3 MiB per chunk. Shard-13 witnesses: median 7,359 B, max 80,414 B (`capture-stats-summary.json`). 1,000 blocks × ~10 shards is ~10,000 chunks. Busy shards carry far larger witnesses and contract code, and nearcore caps one witness at 128 MB (`SINGLE_LATEST_WITNESS_MAX_SIZE`, `chain/chain/src/store/latest_witnesses.rs:31`). So 200 GiB covers a mean of 20 MiB per chunk. Treat it as a reserve, not a measurement. |
| Network | Unmetered, ≥ 1 Gbit/s | State sync downloads every shard's state parts. The pilot needed about 3.7 h of state-part download and application for **one** shard (RUNBOOK "Monitor, stop and resume"). |

Before you start, check that free space ≥ 4 TB + 200 GiB + the supervisor reserve on one filesystem:
`df -h /path/to/capture-root`.

## 2. Build (identical to the pilot)

```sh
CAPTURE_REPO=/path/to/nearproof              # this repository
CAPTURE_SRC=/path/to/nearcore-capture-all    # fresh nearcore checkout
CAPTURE_ROOT=/path/to/mainnet-w13-all        # home, exports, binary, evidence (one filesystem)
CAPTURE_TARGET=/path/to/neard-target

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
"$CAPTURE_ROOT/bin/neard" --version   # must print 2.13.4, commit 44f7ae6c…, protocol 86, db 49
sha256sum "$CAPTURE_ROOT/bin/neard" "$CAPTURE_ROOT/run/"* > "$CAPTURE_ROOT/build.sha256"
```

The pilot's `build-evidence.json` records the expected version line. A different binary hash is
expected, because the build is not reproducible. Record it; do not compare it.

## 3. Initialise and configure all-shard tracking

```sh
"$CAPTURE_ROOT/bin/neard" --home "$CAPTURE_ROOT/home" init --chain-id mainnet --download-config rpc
python3 "$CAPTURE_ROOT/run/configure.py" --home "$CAPTURE_ROOT/home" --shard 13
```

`configure.py` checks live PV86, fetches public boot peers, sets loopback RPC (`127.0.0.1:3038`) and
metrics (`127.0.0.1:3039`), and sets P2P to `0.0.0.0:24578`. It also writes the capture keys below and
`setup-evidence.json`. It refuses a home that already has `data/`. It only knows single-shard
schedules (`--shard` is a placeholder here). So, **before first start**, switch tracking to all shards:

```sh
python3 - "$CAPTURE_ROOT/home" <<'PY'
import hashlib, json, sys, urllib.request
from pathlib import Path
home = Path(sys.argv[1])
assert not (home / 'data').exists(), 'fresh home only'
req = urllib.request.Request('https://rpc.mainnet.fastnear.com', json.dumps({'jsonrpc': '2.0', 'id': 'w13',
      'method': 'EXPERIMENTAL_protocol_config', 'params': {'finality': 'final'}}).encode(),
      headers={'Content-Type': 'application/json'})
protocol = json.load(urllib.request.urlopen(req, timeout=30))['result']
assert protocol['protocol_version'] == 86, 'outside the pinned target'
layout = next(iter(protocol['shard_layout'].values()))
cfg_path = home / 'config.json'
cfg = json.loads(cfg_path.read_text())
cfg['tracked_shards_config'] = 'AllShards'
for legacy in ('tracked_shards', 'tracked_accounts', 'tracked_shard_schedule'):
    cfg.pop(legacy, None)
cfg_path.write_text(json.dumps(cfg, indent=2) + '\n')
ev_path = home / 'setup-evidence.json'
ev = json.loads(ev_path.read_text())
ev.update(selected_shards=layout['shard_ids'], tracking_policy='AllShards',
          shard_layout=protocol['shard_layout'],
          scope='all-shard acquisition; not replay acceptance',
          config_sha256=hashlib.sha256(cfg_path.read_bytes()).hexdigest())
ev_path.write_text(json.dumps(ev, indent=2) + '\n')
print('tracking all shards of layout', layout['shard_ids'])
PY
```

The config keys that matter, and their values for this run:

| Key (`config.json`) | Value | Why |
|---|---|---|
| `tracked_shards_config` | `"AllShards"` | `TrackedShardsConfig::AllShards` (`core/chain-configs/src/client_config.rs:49-63`). The older `tracked_shards` key is deprecated; nearcore reads `tracked_shards_config` first (`nearcore/src/config.rs:248-262, 659-664`). Remove the legacy keys so there is only one source of truth. |
| `save_latest_witnesses` | `true` | Default `false` (`nearcore/src/config.rs:420, 530`). Keeps the bounded latest-witness ring: **1,800 witnesses or 4 GB** (`latest_witnesses.rs:28-34`). That is under 200 blocks at ~10 shards, so the patch's continuous export in `exports/` is the real record. The ring is only a cross-check. |
| `save_invalid_witnesses` | `true` | Keeps any witness that fails native validation, for diagnosis. |
| `archive` | `false` | Non-archival RPC-style node (sizing above). |
| `gc_num_epochs_to_keep` | `3` | The documented minimum. The claim exporter needs the chain/epoch context of the captured window, so **stop the node and export claims within ~3 epochs** (about 1.5 days at mainnet's 43,200-block epochs) of the window, or raise this value and the disk budget. |
| `state_sync.concurrency` | `apply 4, apply_during_catchup 1, peer_downloads 24, per_shard 24` | The pilot's corrected settings. `peer_downloads` is a global cap shared by all shards. |
| `consensus.state_sync_p2p_timeout` | `60 s` | The pilot's fix for a stale sync target. |
| `store.load_mem_tries_for_tracked_shards` | `false` (default) | See the RAM row above. |
| `rpc.addr` / `rpc.prometheus_addr` / `network.addr` | loopback / loopback / `0.0.0.0:24578` | Never expose RPC. Open only the P2P port. |

Split alternative: separate fresh homes on separate hosts, each with `--shard ID`, collecting an
overlapping window. Same-host nodes need distinct ports and must never share a database. The pilot
RUNBOOK covers the port edits. The gate only needs every shard's chunks for one common block window.

## 4. Run the bounded capture service

```sh
systemd-run --user --unit=nearproof-mainnet-w13-all --collect \
  -p MemoryMax=60G -p MemorySwapMax=0 -p CPUQuota=1600% -p IOWeight=50 \
  /usr/bin/python3 "$CAPTURE_ROOT/run/supervise.py" \
  --binary "$CAPTURE_ROOT/bin/neard" --home "$CAPTURE_ROOT/home" \
  --exports "$CAPTURE_ROOT/exports" \
  --max-data-gib 4200 --reserve-gib 100 --max-captures 100000
```

- Set `--max-data-gib` to the provisioned disk. The home-allocation limit does not count the sibling
  `exports/`; the free-space reserve covers both, because they share a filesystem.
- `--max-captures` is a **safety ceiling, not a coverage criterion**. At ~10 shards, 1,200 captures is
  only ~120 heights. 100,000 is about 10,000 heights at full slot coverage.
- The supervisor stops when a recent synced head leaves PV86. A protocol upgrade during the window
  ends the run, which is the correct behaviour for a PV86 pin.

Monitor (use the actual unit name and ports):

```sh
systemctl --user status nearproof-mainnet-w13-all.service
cat "$CAPTURE_ROOT/home/capture-status.json"            # state, captures, accepts/rejects, free bytes
grep -E 'parts \(|State sync|catchup' "$CAPTURE_ROOT/home/node.log" | tail   # sync progress
curl -s http://127.0.0.1:3038/status | python3 -m json.tool | grep -E 'height|syncing|protocol'
ls "$CAPTURE_ROOT/exports" | sed -E 's/^h[0-9]+-s([0-9]+)-.*/\1/' | sort | uniq -c   # per-shard counts
```

During state sync, `/status` can show genesis PV29. Use `node.log`'s `parts (N/T)` instead. Expect
the sync to take several times the pilot's single-shard ~3.7 h, because the parts of all shards
share the `peer_downloads` cap.

## 5. Choose and verify a ≥ 1,000-block window for every shard

1. Wait until **every** shard in `setup-evidence.json`'s `selected_shards` has been exporting
   continuously. The first heights after sync are often partial: a shard that is still catching up
   exports nothing.
2. Pick a start height `H` after that point and capture the independent block denominator:

   ```sh
   python3 tools/mainnet-replay/gate.py capture --start H --blocks 1000 --out "$CAPTURE_ROOT/gate-capture"
   ```

   This fetches each canonical block's full chunk list from the configured archive. It fails if the
   window is discontinuous or a height is missing; a skipped height currently fails closed.
3. Audit the exports against that denominator. Every **new** chunk (`height_included == height`)
   must have exactly one export `h{height}-s{shard}-{chunk_hash}` with `capture.json` present and no
   missing code:

   ```sh
   python3 - "$CAPTURE_ROOT/gate-capture" "$CAPTURE_ROOT/exports" <<'PY'
   import json, sys
   from pathlib import Path
   cap, exp = Path(sys.argv[1]), Path(sys.argv[2])
   m = json.loads((cap / 'manifest.json').read_text())
   assert not m['acquisition_errors'], m['acquisition_errors'][:3]
   have = {p.name for p in exp.iterdir() if (p / 'capture.json').exists()}
   need = missing = 0
   for b in m['blocks']:
       blk = json.loads((cap / b['artifact']['path']).read_text())['block']
       for ch in blk['chunks']:
           if ch['height_included'] != b['height']:
               continue   # repeated/missed slot: counted by the gate, no witness expected
           need += 1
           name = f"h{b['height']}-s{ch['shard_id']}-{ch['chunk_hash']}"
           if name not in have:
               missing += 1
               print('missing', name)
           elif json.loads((exp / name / 'capture.json').read_text()).get('missing_code'):
               print('missing code', name)
   print(f'{need} new chunks, {missing} without an export')
   PY
   ```

   Any `missing` line means you must move `H` later or capture longer. Do not drop the chunk.
4. Keep capturing until the audit is clean, then stop the service cleanly
   (`systemctl --user stop nearproof-mainnet-w13-all.service`) and wait for RocksDB to shut down.
   Do this within the `gc_num_epochs_to_keep` horizon.

## 6. Export claims, attach cases, run the gate

Build the diagnostic exporter binary from the same pin with `native/replay-export.patch` and the
three `w13_*.rs` files ([native/README.md](native/README.md)). Keep it separate from the capture
binary. Then run:

```sh
NEARD_EXPORT=/path/to/exporting/neard
"$NEARD_EXPORT" --home "$CAPTURE_ROOT/home" view-state state-witness replay-export \
  --input "$CAPTURE_ROOT/exports" --output "$CAPTURE_ROOT/replay-cases"
# bind each exported pair to the gate capture (re-fetches and checks the claim's segment headers)
for d in "$CAPTURE_ROOT"/replay-cases/h*-s*-*/; do
  python3 tools/mainnet-replay/gate.py attach --capture "$CAPTURE_ROOT/gate-capture" --case "$d" \
    || echo "ATTACH FAILED $d" >> "$CAPTURE_ROOT/attach-failures.txt"
done
```

Exports for heights outside the window fail `attach` ("does not identify exactly one … chunk in
this capture"). Expect that, but check that every failure is outside the window.

Per-shard diagnostics (allowed now; they do **not** certify all-shard coverage):

```sh
(cd spec/lean/v3 && lake build nearspec-v3-check-successor)
for s in $(python3 -c "import json;print(*json.load(open('$CAPTURE_ROOT/home/setup-evidence.json'))['selected_shards'])"); do
  python3 tools/mainnet-replay/shard_replay.py --captures "$CAPTURE_ROOT/exports" \
    --cases "$CAPTURE_ROOT/replay-cases" --binary spec/lean/v3/.lake/build/bin/nearspec-v3-check-successor \
    --native-binary "$NEARD_EXPORT" --tier allFeatures --shard "$s" --jobs 8 \
    --out "$CAPTURE_ROOT/replay-results-s$s"
done
```

The gate:

```sh
make d3-drivers
make w13-gate \
  W13_CAPTURE="$CAPTURE_ROOT/gate-capture" \
  W13_NATIVE_COMMAND_FILE=/path/to/native-command.json \
  W13_TIER=allFeatures \
  W13_REPORT="$CAPTURE_ROOT/w13-report"
```

- `W13_TIER` defaults to `curveHosts` in the `Makefile`. Pass `allFeatures`, the cumulative tier the
  shard-13 diagnostic used, so that no exercised feature is out of domain by tier choice.
- `native-command.json` is the JSON argv of the **cold native adapter**. It must run pinned
  `pre_validate_chunk_state_witness` + `validate_chunk_state_witness` against the node context and
  verify every trusted claim fact (README "Native adapter contract"). **That adapter does not exist
  yet.** Without it the gate fails and still writes `report.json`. The diagnostic `replay-export`
  binary validates the node's own claims, not externally supplied ones, so do not wrap it as the
  adapter.
- A pass needs ≥ 1,000 consecutive heights, 100% replay coverage of new chunks and 0 mismatches,
  with every case native-accepted and Lean-accepted. Report mismatch %, coverage % and verified-match %
  exactly as `report.json` gives them. A diagnostic or partial run is a failure of this gate, not a
  waiver.

## 7. Evidence to keep (never commit keys or the database)

`build.sha256`; `home/config.json` and its hash; `home/setup-evidence.json`; final
`home/capture-status.json`; `node.log` excerpts for sync and stop; `gate-capture/manifest.json`; the
audit output from §5; `replay-cases/exports.json`; `attach-failures.txt`; every `replay-results-s*`
and `w13-report/report.json`. Summaries and small samples go under `docs/evidence/` (< 5 MB). The raw
exports stay on the capture disk.
