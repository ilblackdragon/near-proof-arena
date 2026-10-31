# W13 all-shard capture runbook

This runbook brings up **one isolated, pinned nearcore 2.13.4 node that tracks every mainnet shard
and exports a witness for every new chunk**. It then takes that capture through `make w13-gate`.
It extends the single-shard pilot ([nearcore-capture/README.md](nearcore-capture/README.md),
[nearcore-capture/RUNBOOK.md](nearcore-capture/RUNBOOK.md)) and the gate contract
([README.md](README.md)). Read those first: they define the export format, the supervisor and the
pass criteria. This file adds what changes for all shards, and the single-machine plan for the
sponsor box.

**Status (2026-10-27).** Everything after the capture is built and has been dry-run:

- the cold native adapter: `neard … view-state state-witness cold-validate`
  ([native/README.md](native/README.md));
- the finality/provenance boundary;
- `gate.py capture/attach-all/run`, with blind replay;
- `make w13-gate`.

The dry run used the 1,223 shard-13 pilot captures and an archive capture of all ten shards for the
same 1,223 heights
([evidence](../../docs/evidence/lean-chunk-completion/mainnet-w13-gate-dryrun/README.md)). The gate
fails there, as it must: only shard 13 has witnesses. **No all-shard capture has been run yet.**
Figures marked *measured* come from the pilot, the dry run or this machine. Every other figure is an
**estimate**, and its source is given.

Pins: nearcore `44f7ae6cd7ef08bab604e20a473bf77e35d4c993` (2.13.4, PV86, db 49), Rust 1.93.0,
features `json_rpc,shadow_chunk_validation`.

- Capture binary: pin + `nearcore-capture/export.patch`.
- Adapter/exporter binary: pin + `export.patch` + `native/replay-export.patch` + the four
  `native/w13_*.rs` files.

Do **not** reuse or touch the pilot node at `/data/illia/nearproof-deps/mainnet-w13`. Its database is
the context for the existing shard-13 claims (`replay-cases/`). Use a fresh home.

## 1. The machine and the single-filesystem plan

The sponsor machine is this box. Measured on 2026-10-27:

| Resource | This box (measured) | Need for one all-shard node | Source of the need |
|---|---|---|---|
| CPU | AMD Ryzen 9 9950X3D, 16 cores / 32 threads, AVX2 | ≥ 8 cores / 16 threads | NEAR [RPC](https://near-nodes.io/rpc/hardware-rpc) and [archival](https://near-nodes.io/archival/hardware-archival) hardware pages (2026-03-17). Shadow validation re-executes every chunk on top of normal application, so more cores help. |
| RAM | 125 GiB | 64 GiB budget (`MemoryMax=96G` cap) | RPC page: 32 GB recommended. On top of that come shadow validation, witness export and the configured caches (`col_state_cache_size` 3 GiB, per-shard trie caches up to 3 GB on hot shards). `load_mem_tries_for_tracked_shards` stays `false`. |
| Disks | 2 × Micron 7450 960 GB NVMe (894.3 GiB each). `/` = nvme0n1p3 (878 GiB fs), `/data` = nvme1n1p1 (880 GiB fs). | **One** filesystem for node home, exports, replay cases and gate capture | The supervisor's free-space guard sees only the home's filesystem. |
| Free space at time of writing | `/` 21 GiB, `/data` 40 GiB | **≥ 600 GiB free on `/data`** before the snapshot download | Budget below. Freeing it is a separate task; nothing here deletes data. |
| Network | 0.89 Gbit/s, measured downloading 4.77 GB of SST files from the Aurora snapshot (16 streams, 42.9 s) | Unmetered | — |

Put **everything on `/data`** (nvme1n1). It is the larger free target once cleaned, and keeping
the node home and exports on one filesystem lets the supervisor's reserve cover both. Root (`/`)
holds the OS, toolchains and build targets.

```sh
CAPTURE_REPO=/data/illia/nearproof                         # this repository
CAPTURE_ROOT=/data/illia/nearproof-deps/mainnet-w13-all    # home, exports, cases, gate capture, evidence
CAPTURE_SRC=/data/illia/nearproof-deps/nearcore-capture-all
ADAPTER_SRC=/data/illia/nearproof-deps/nearcore-adapter
CAPTURE_TARGET=/tmp/nearproof-neard-all-target             # on /, keeps build churn off /data
```

### Disk budget on `/data`

| Item | Size | Status |
|---|---|---|
| Node database, restored from the Aurora "Mainnet - Nearcore - Full" snapshot | **389.07 GB** (362 GiB) at block 221,878,352, 2026-10-27 20:53 UTC, version 2.13.4 | *measured* (snapshot listing). The listing grew from 372.28 GB to 389.07 GB in 18 h (02:53→20:53), so expect it to be larger when you download. |
| Growth while capturing (~2 days: catch-up, window, export) | +50 GiB | *estimate*, from that 18 h growth (~0.9 GB/h) |
| `exports/` + `replay-cases/` for ~10,000 chunks | reserve 100 GiB | Pilot *measured*: 219 MiB of exports + 162 MiB of cases for 1,223 shard-13 chunks (~0.3 MiB/chunk), with a median witness of 7,359 B and a max of 80,414 B. Shard 13 is quiet; busy shards carry far larger witnesses and code, and nearcore caps one witness at 128 MB. So this is a reserve, not a scaled measurement. |
| Gate capture (1,000 blocks) + per-case context blocks | ~0.1 GiB + ~1.5 GiB | *measured*: 68–160 KB per block JSON on the dry run. Context blocks are ~2 per case, copied from the capture when in the window. |
| Supervisor free-space reserve | 50 GiB | `--reserve-gib 50` |
| **Total** | **≈ 560 GiB → provision ≥ 600 GiB free** | — |

The downloaded snapshot includes 3,549 `contract.cache/*` files (the snapshot node's warm
compiled-contract cache). Skip them (below). The capture node rebuilds what it needs. The W13
adapter never reads any compiled cache.

## 2. Bootstrapping: snapshot or state sync

| | Aurora 2.13.4 snapshot (recommended) | State sync for all shards |
|---|---|---|
| Data moved | 389 GB of raw RocksDB files (`rclone`, resumable) | Every shard's state parts from peers, then flat-storage build and catch-up |
| Time | Download: **~1 h** at the measured 0.89 Gbit/s (estimate: 389 GB × 8 / 0.89 Gbit/s ≈ 58 min). Then block catch-up from the snapshot height: the snapshot is ≤ 6 h old, and catch-up speed for all shards is **not measured**. | Pilot *measured*: ~3.7 h of part download and application for **one** quiet shard. The first pilot attempt reset at 243/371 parts on a stale sync target. All ten shards share the global `peer_downloads` cap. *Estimate*: 10–24 h or more, with reset risk. |
| Shard coverage | **Not stated by the listing.** The snapshot must hold state for all ten shards. Verify with `flat-storage view` before relying on it (§3). | AllShards by construction |
| Trust | Third-party database. Harmless for W13: the node re-validates new blocks, and the gate's facts come from this node's store only after it has followed the chain. The adapter's finality check reads the same store, so record the snapshot name and index hash. | Peers + state root checks |
| GC horizon | The snapshot node's `gc_num_epochs_to_keep` is unknown. Ours is set to 3 before start. | 3 |

Use the snapshot. Fall back to state sync if `flat-storage view` shows a shard missing or not
`Ready`. Then either wait for an epoch boundary (nearcore should catch up newly tracked shards by
state sync at the next epoch; not verified for this build) or start a fresh home with state sync.

## 3. Build, initialise, restore

Build the capture binary exactly as the pilot did:

```sh
git clone https://github.com/near/nearcore.git "$CAPTURE_SRC"
git -C "$CAPTURE_SRC" checkout --detach 44f7ae6cd7ef08bab604e20a473bf77e35d4c993
git -C "$CAPTURE_SRC" apply "$CAPTURE_REPO/tools/mainnet-replay/nearcore-capture/export.patch"
cd "$CAPTURE_SRC"
CARGO_BUILD_JOBS=16 CARGO_TARGET_DIR="$CAPTURE_TARGET" \
  CARGO_PROFILE_RELEASE_LTO=false CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16 \
  cargo +1.93.0 build -p neard --release --locked --no-default-features \
  --features json_rpc,shadow_chunk_validation
mkdir -p "$CAPTURE_ROOT/bin" "$CAPTURE_ROOT/run" "$CAPTURE_ROOT/exports"
install -m 755 "$CAPTURE_TARGET/release/neard" "$CAPTURE_ROOT/bin/neard"
cp "$CAPTURE_REPO/tools/mainnet-replay/nearcore-capture/"{configure.py,supervise.py,export.patch} "$CAPTURE_ROOT/run/"
"$CAPTURE_ROOT/bin/neard" --version   # 2.13.4, commit 44f7ae6c…, protocol 86, db 49
sha256sum "$CAPTURE_ROOT/bin/neard" "$CAPTURE_ROOT/run/"* > "$CAPTURE_ROOT/build.sha256"
```

Build the adapter/exporter binary into a separate checkout and target, following
[native/README.md](native/README.md) "Build". Install it as `$CAPTURE_ROOT/bin/neard-adapter`.

Initialise and configure (both refuse a home that already has `data/`, so this comes **before**
the restore):

```sh
"$CAPTURE_ROOT/bin/neard" --home "$CAPTURE_ROOT/home" init --chain-id mainnet --download-config rpc
python3 "$CAPTURE_ROOT/run/configure.py" --home "$CAPTURE_ROOT/home" --shard 13
```

`configure.py` checks live PV86, fetches public boot peers, sets loopback RPC (`127.0.0.1:3038`)
and metrics (`127.0.0.1:3039`), sets P2P to `0.0.0.0:24578`, and writes the capture keys below and
`setup-evidence.json`. The pilot node uses the same ports. It is stopped, so they are free, but
never run both. `--shard` is a placeholder. Before the first start, switch tracking to all
shards:

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

Restore the newest 2.13.4 snapshot into `home/data`, without the warm contract cache or a stale
`LOCK`. Install rclone ≥ 1.70 first:

```sh
L=$(curl -s https://snapshots.aurora.dev/latest/mainnet/nearcore/full/uncompressed); echo "$L" | tee "$CAPTURE_ROOT/snapshot-url.txt"
curl -s "$L/index" | grep -v -e '^contract.cache/' -e '^LOCK$' > "$CAPTURE_ROOT/snapshot-index.txt"
sha256sum "$CAPTURE_ROOT/snapshot-index.txt" >> "$CAPTURE_ROOT/build.sha256"
df -h /data                                          # ≥ 600 GiB free (§1)
rclone copy --buffer-size 128M --transfers 64 --retries 20 --retries-sleep 1s --low-level-retries 10 \
  --multi-thread-streams 1 --no-traverse --http-url "$L/data" --files-from "$CAPTURE_ROOT/snapshot-index.txt" \
  --checkers 64 --progress --stats-one-line :http: "$CAPTURE_ROOT/home/data"
"$CAPTURE_ROOT/bin/neard" --home "$CAPTURE_ROOT/home" flat-storage view   # every shard of the layout: Ready
```

Record the snapshot directory name (e.g. `20261027-2053-221878352`) in `setup-evidence.json`. If a
shard of the live layout is missing from `flat-storage view`, see §2's fallback.

The config keys that matter, and their values for this run:

| Key (`config.json`) | Value | Why |
|---|---|---|
| `tracked_shards_config` | `"AllShards"` | `TrackedShardsConfig::AllShards` (`core/chain-configs/src/client_config.rs:49-63`). The older `tracked_shards` key is deprecated; nearcore reads `tracked_shards_config` first (`nearcore/src/config.rs:248-262, 659-664`). |
| `save_latest_witnesses` | `true` | Default `false`. Keeps the bounded ring: **1,800 witnesses or 4 GB** (`latest_witnesses.rs:28-34`), which is under 200 blocks at ten shards. The patch's continuous export in `exports/` is the real record; the ring is only a cross-check. |
| `save_invalid_witnesses` | `true` | Keeps any witness that fails native validation. |
| `archive` | `false` | Non-archival. |
| `gc_num_epochs_to_keep` | `3` | The documented minimum. Claim export needs the window's chain/epoch context, so **stop the node and export within ~3 epochs** (~1.5 days at 43,200-block epochs) of the window. |
| `state_sync.concurrency` | `apply 4, apply_during_catchup 1, peer_downloads 24, per_shard 24` | The pilot's corrected settings. Only used if a shard must state sync. |
| `consensus.state_sync_p2p_timeout` | `60 s` | The pilot's fix for a stale sync target. |
| `store.load_mem_tries_for_tracked_shards` | `false` (default) | RAM (§1). |
| `rpc.addr` / `rpc.prometheus_addr` / `network.addr` | loopback / loopback / `0.0.0.0:24578` | Never expose RPC. Open only P2P. |

## 4. Run the bounded capture service

```sh
systemd-run --user --unit=nearproof-mainnet-w13-all --collect \
  -p MemoryMax=96G -p MemorySwapMax=0 -p CPUQuota=2400% -p IOWeight=50 \
  /usr/bin/python3 "$CAPTURE_ROOT/run/supervise.py" \
  --binary "$CAPTURE_ROOT/bin/neard" --home "$CAPTURE_ROOT/home" \
  --exports "$CAPTURE_ROOT/exports" \
  --max-data-gib 520 --reserve-gib 50 --max-captures 100000
```

- `--max-data-gib` limits the home only. 520 GiB is the 362 GiB snapshot plus growth plus margin.
  The free-space reserve covers home and exports together, because they share `/data`.
- `--max-captures` is a **safety ceiling, not a coverage criterion**. At ten shards, 100,000
  captures is ~10,000 heights.
- The supervisor stops when a recent synced head leaves PV86. A protocol upgrade during the window
  ends the run, which is correct for a PV86 pin.

Monitor:

```sh
systemctl --user status nearproof-mainnet-w13-all.service
cat "$CAPTURE_ROOT/home/capture-status.json"            # state, captures, accepts/rejects, free bytes
curl -s http://127.0.0.1:3038/status | python3 -m json.tool | grep -E 'height|syncing|protocol'
ls "$CAPTURE_ROOT/exports" | sed -E 's/^h[0-9]+-s([0-9]+)-.*/\1/' | sort | uniq -c   # per-shard counts
df -h /data
```

After a snapshot restore, the node first catches up blocks from the snapshot height. Exports start
when it applies live chunks. If a shard must state sync, `/status` can show genesis PV29; use
`node.log`'s `parts (N/T)`.

## 5. Choose and verify a ≥ 1,000-block window for every shard

1. Wait until **every** shard in `setup-evidence.json`'s `selected_shards` exports continuously.
2. Pick a start height `H` after that point and capture the independent block denominator:

   ```sh
   python3 tools/mainnet-replay/gate.py capture --start H --blocks 1000 \
     --archive-url jsonrpc+https://archival-rpc.mainnet.fastnear.com --interval 0.1 \
     --out "$CAPTURE_ROOT/gate-capture"
   # transient failures: rerun the same command with --resume until acquisition_errors is empty
   ```

   Measured on the dry run: NEAR Data (the default archive) rate-limited this box with HTTP 429
   after ~13 blocks and kept doing so. The FastNEAR archival JSON-RPC served all 1,223 blocks
   (0 acquisition errors) at 0.1 s spacing in about an hour. It too returned 429 at times; the
   backoff absorbed those. The window fails closed on any missing or discontinuous height.
3. Audit the exports against that denominator. Every **new** chunk (`height_included == height`)
   must have exactly one export `h{height}-s{shard}-{chunk_hash}` with `capture.json` present and no
   missing code:

   ```sh
   python3 - "$CAPTURE_ROOT/gate-capture" "$CAPTURE_ROOT/exports" <<'PY'
   import json, sys
   from pathlib import Path
   sys.path.insert(0, 'tools/mainnet-replay')
   from gate import block_of
   cap, exp = Path(sys.argv[1]), Path(sys.argv[2])
   m = json.loads((cap / 'manifest.json').read_text())
   assert not m['acquisition_errors'], m['acquisition_errors'][:3]
   have = {p.name for p in exp.iterdir() if (p / 'capture.json').exists()}
   need = missing = 0
   for b in m['blocks']:
       blk = block_of(json.loads((cap / b['artifact']['path']).read_text()))
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
4. Keep capturing until the audit is clean **and the node's final head is past the window's last
   height**. The adapter admits only blocks at or below the store's final head. In the dry run, the
   pilot store's final head stopped two heights short of its last capture, and those two chunks
   were (correctly) gate errors. Then stop the service
   (`systemctl --user stop nearproof-mainnet-w13-all.service`) and wait for RocksDB to shut down,
   within the `gc_num_epochs_to_keep` horizon.

## 6. Export claims, attach cases, run the gate

The node is stopped. The exporter and the adapter open its store read-only.

```sh
NEARD_ADAPTER="$CAPTURE_ROOT/bin/neard-adapter"
"$NEARD_ADAPTER" --home "$CAPTURE_ROOT/home" view-state state-witness replay-export \
  --input "$CAPTURE_ROOT/exports" --output "$CAPTURE_ROOT/replay-cases"
python3 tools/mainnet-replay/gate.py attach-all \
  --capture "$CAPTURE_ROOT/gate-capture" --cases "$CAPTURE_ROOT/replay-cases"
printf '["%s", "--home", "%s", "view-state", "state-witness", "cold-validate"]\n' \
  "$NEARD_ADAPTER" "$CAPTURE_ROOT/home" > "$CAPTURE_ROOT/native-command.json"
```

`attach-all` writes `gate-capture/attach-replay-cases.json`. Exports for heights outside the window
fail with "does not identify exactly one … chunk in this capture". Check that every failure is
outside the window.

Optional, recommended before the gate: the adapter's deliberate-breakage controls on a sample. They
must report 0 unexpected:

```sh
python3 tools/mainnet-replay/native/cold_controls.py --native-command-file "$CAPTURE_ROOT/native-command.json" \
  --cases "$CAPTURE_ROOT/replay-cases" --limit 500 --jobs 12 --out "$CAPTURE_ROOT/cold-controls"
```

The gate:

```sh
(cd spec/lean/v3 && lake build nearspec-v3-check-successor)
make w13-gate \
  W13_CAPTURE="$CAPTURE_ROOT/gate-capture" \
  W13_NATIVE_COMMAND_FILE="$CAPTURE_ROOT/native-command.json" \
  W13_REPORT="$CAPTURE_ROOT/w13-report" W13_JOBS=12
```

- Tier: `allFeatures` (the Makefile default).
- Every case goes through the cold adapter. That means: claim recomputed and byte-equal; including
  block canonical and final, with a hash equal to the archive's; empty compiled cache; code only
  from `witness.bin`. Every native accept is then replayed **blind**.
- A pass needs ≥ 1,000 consecutive heights, 100% replay coverage of new chunks and 0 mismatches.
  Report mismatch %, coverage %, verified-match % and `per_shard` exactly as `report.json` gives
  them. A diagnostic or partial run is a failure of this gate, not a waiver.

Throughput (dry run, *measured*, 22 GB pilot store): ~2.4 s per adapter call, dominated by opening
the store and the epoch manager; native validation itself was ≤ 0.55 s per shard-13 chunk. The full
dry-run gate (12,230 slots, 1,223 cases, `W13_JOBS=6`) took about 15 minutes. Run the gate and the
controls in their own scope (`systemd-run --user --scope -p MemoryMax=16G make w13-gate …`). Inside
a shared, memory-throttled session cgroup, every adapter call hit the 600 s timeout
(`mem_cgroup_handle_over_high`). On the ~400 GB all-shard store and busy shards it will be slower
(*estimate*: 10,000 cases at 12 jobs in ~1–3 h, Lean included).

## 7. Evidence to keep (never commit keys or the database)

`build.sha256` (binaries, launcher, snapshot index); `snapshot-url.txt`; `home/config.json` and its
hash; `home/setup-evidence.json`; `flat-storage view` output; final `home/capture-status.json`;
`node.log` excerpts for catch-up and stop; `gate-capture/manifest.json`; the §5 audit output;
`replay-cases/exports.json`; `gate-capture/attach-replay-cases.json`; `cold-controls/report.json`;
and `w13-report/report.json`. Summaries and small samples go under `docs/evidence/` (< 5 MB). The raw
exports stay on the capture disk.
