# Mainnet witness acquisition pilot

This runs nearcore **2.13.4**, commit
`44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, with Rust **1.93.0** and
`json_rpc,shadow_chunk_validation`. It tracks shard **13** on mainnet PV86.
No staking or validator key is required: the stateful node constructs witnesses
from executed chunks, then calls native shadow validation.

## Build and launch

Use a separate checkout of the pinned nearcore commit. Apply `export.patch`, then
build from that checkout (so its Cargo configuration is used):

```sh
git apply /absolute/path/to/nearcore-capture/export.patch
CARGO_BUILD_JOBS=8 CARGO_TARGET_DIR=/tmp/nearproof-neard-target \
  CARGO_PROFILE_RELEASE_LTO=false CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16 \
  cargo +1.93.0 build -p neard --release --locked --no-default-features \
  --features json_rpc,shadow_chunk_validation
```

Initialize an isolated home with `neard --home HOME init --chain-id mainnet
--download-config rpc`, then run `configure.py --home HOME`. Configuration checks
live mainnet PV86 and shard membership, obtains fresh public boot peers, tracks
only shard 13, and binds RPC to `127.0.0.1:3038`, metrics to
`127.0.0.1:3039`, and P2P to `0.0.0.0:24578`. It refuses to reconfigure an
existing database. No FastNear API key is needed for these public RPC calls.

Run `supervise.py --binary /absolute/path/neard --home HOME --exports EXPORTS`
in a persistent service. Defaults stop at 1,200 captures, 35 GiB allocated home
data, or less than 15 GiB free on the home filesystem. Keep home and exports on
the same filesystem so the reserve covers both. A fully synced node outside PV86
also stops. Limits are a pilot budget, not a claim that every mainnet shard fits.

## Output and interpretation

Each `EXPORTS/hHEIGHT-sSHARD-CHUNKHASH/` contains:

- `state_witness.borsh`: raw `ChunkStateWitness`.
- `chunk.borsh`: full `ShardChunk`, including transactions and receipts.
- `block.borsh` and `parent_header.borsh`: containing block and parent header.
- `code/*.wasm`: available accessed/deployed contract code; accessed code is
  hash-checked before writing. `capture.json` explicitly lists missing code.
- `capture.json`: chunk/block/epoch/protocol identity and witness hash/size.
- `native-validation.json`: asynchronous native shadow verdict, if validation
  reaches that stage. Missing verdicts are pending/errors, never acceptance.

`HOME/capture-status.json` reports sync status, counts, disk usage and stop reason.
`HOME/node.log` records sync/export/validation errors. Keep `setup-evidence.json`,
config, binary hash and patch hash with acquisition evidence; never commit node
keys or the database. Stop the supervisor normally to shut down neard cleanly.

The patch preserves full block-slot indices when skipping missing chunks and
limits shadow validation to tracked shards. Upstream's layout-change limitation
still applies; a resharding boundary needs separate handling.

**This is acquisition, not a W13 pass.** Shadow validation uses the running node's
context and cache. W13 still requires complete code closure, authenticated
DB-to-claim conversion, a cold native validation adapter, Lean replay, and the
1,000-block all-shard representative window. Single-shard captures or native
acceptance alone do not satisfy those conditions.
