# W13: exact mainnet stateless replay gate

`replay.py` is the older **metadata census**. `gate.py` is the new capture/import/replay gate.
It never counts metadata, generated TestEnv cases, or rebased historical receipt fixtures as
executed mainnet chunks. W13 is **not complete** until an actual qualifying run passes.

## Gate and percentages

`make w13-gate` exits zero only when:

1. At least 1,000 consecutive captured block heights form a continuous mainnet block chain.
2. Every shard slot is derived from the captured block's full chunk list. Every newly included
   chunk has its exact claim/witness pair; repeated/missed chunk slots are counted separately.
3. Claim bytes identify the on-chain chunk hash, shard, epoch and PV86/mainnet. Every claim segment
   block hash appears in the independent archive capture. The Lean checker authenticates the trie,
   receipt proofs and block-slot roots against those commitments.
4. The cold native adapter ([native/README.md](native/README.md)) validates the same bytes against
   its actual mainnet chain/epoch store with an **empty compiled-contract cache**. It verifies **all
   trusted claim facts** (layout, validators, epoch flags, transaction-validity flags, validator
   rewards/minimum stakes, Reed–Solomon parameters and genesis extra where used) by recomputing
   the claim and requiring byte equality. It also attests that the including block is canonical and
   final in its store, and that block's hash must equal the archive's.
5. Every native-accepted case is replayed **blind**: produced values are removed from the inputs,
   Lean must accept and emit exactly the endorsed header's outputs, and the blinded inputs rerun
   with comparisons on must not accept. No unsupported case, missing witness, acquisition failure,
   native rejection, crash, timeout, changed artifact or unexplained difference remains.

A run prints and writes `report.json` with:

- **Mismatch %** = `100 × mismatches / compared`. Here `mismatches` covers Lean rejects,
  `output_mismatch` (a blind output differs from the header) and `blind_leak` (the control accepted
  blinded inputs), and `compared` is matches plus mismatches. With no comparisons it is JSON `null`,
  displayed **N/A**, never "0%". A native-accepted chunk rejected by Lean is a mismatch; its precise
  rejection reason is retained.
- **Replay coverage %** = `100 × compared / expected newly included chunks`.
- **Verified match %** = `100 × matches / expected newly included chunks`.
- Separate missing-witness, unsupported, native-reject, runner-unavailable and error counts, in
  total and per shard (`per_shard`).
- Block-capture coverage and whether the expected chunk count is complete. An acquisition gap
  leaves the chunk denominator incomplete and prevents passing regardless of those percentages.
- Exact executable, input, block-artifact, harness and native-adapter identities. Inputs and
  executables are hashed again before completion. Per-case results include native and Lean replies.

All three dimensions matter: **0% mismatch with 2% coverage is FAIL**. The 1,000-block minimum
cannot be lowered to turn a diagnostic run into a W13 pass. A missed block height currently fails
closed; support for a proven skipped-height chain window is a future extension.

Lean computes the endorsed header's 11 outputs blind (`blind_inputs.COMPARED`). It also checks the
remaining **recomputed commitments**, not header read-backs:
state root and implicit transitions, outcome root, outgoing receipts root, gas used/limit,
balance burnt, validator proposals, congestion, bandwidth, transaction root, encoded root/length,
incoming proofs and applied-receipt hash. A successful endorsed-chunk validation checks the prior
execution transitions committed by that chunk. This is not an independent export of every internal
execution field, log or receipt: the separate W01 observable driver remains useful diagnostic work.
Unsupported resharding/key/host paths are failures of this full-window gate, not waived exclusions.

## Capture

```sh
python3 tools/mainnet-replay/gate.py capture \
  --start 220185617 --blocks 1000 --out /data/mainnet-w13
```

The default source is `https://mainnet.neardata.xyz/v0/block/{height}`. A NEAR JSON-RPC archive works
too: `--archive-url jsonrpc+https://archival-rpc.mainnet.fastnear.com` (method `block` by height,
same BlockView). HTTP 429/5xx are retried with exponential backoff. NEAR Data answers 429 with
`Retry-After: 0` while still throttling, so that header never shortens the wait. Heights that
still fail are recorded as acquisition errors; `capture --resume` (same window and archive)
refetches only those. `--interval` spaces requests. Raw responses and SHA256 hashes are retained. The trust boundary is the configured HTTPS mainnet archive and the native
validator's canonical mainnet store. This tool does **not** verify consensus finality signatures
or establish an independent light-client trust root. A self-labelled JSON document is not a
cryptographic proof of mainnet provenance. Operators must choose and retain a trusted source;
the gate records this limitation explicitly.

Capture does not fetch trie witnesses: public block data does not contain them.

## Obtain witnesses and context

For a full all-shard capture (node sizing, `tracked_shards_config = "AllShards"`, window audit and
the `make w13-gate` invocation), follow [ALL_SHARDS_RUNBOOK.md](ALL_SHARDS_RUNBOOK.md).

At pinned nearcore `44f7ae6cd7ef08bab604e20a473bf77e35d4c993`,
`tools/state-viewer/src/latest_witnesses.rs` supports:

```sh
neard --home /path/to/mainnet-node view-state state-witness dump-latest binary /data/raw-witnesses
```

The node must have retained witnesses (`save_latest_witnesses`) for the intended heights/shards.
Only a subset may be retained or observed by a particular validator; the gate does not assume that
a directory of dumps covers all shards. Archive-node state-transition recording/generation is
another acquisition route, but needs the actual node database and correct epoch configuration.
Do not modify a production node's configuration merely to run this command.

A raw Borsh `ChunkStateWitness` can be wrapped for Lean without inventing state:

```sh
python3 tools/mainnet-replay/gate.py pack-witness \
  --raw /data/raw-witnesses/witness.bin \
  --code SHA256_OF_CONTRACT=/data/code/contract.wasm \
  --out /data/exported-case/witness.bin
```

Repeat `--code` for needed contract code. Hashes are verified, blobs sorted/deduplicated by hash,
and the raw witness bytes preserved. This packaging step does not claim successful validation.

The companion `claim.bin` must be exported from the **same native mainnet chain/epoch context**
using [claim-v3](../../spec/claim-v3.md), including the authenticated block segment and trusted facts.
`oracle/v3/src/enc.rs` defines the matching encoder. The generated-chain oracle is not a mainnet
exporter. **A database-to-claim exporter and the cold validator adapter** that verifies supplied claims for
the full gate are in [native/README.md](native/README.md).
Neither raw witness packaging nor public RPC metadata supplies those facts by itself.

Import an exported pair and independently capture its segment headers. Headers inside the window
are copied from the capture; older ones are fetched from the same archive:

```sh
python3 tools/mainnet-replay/gate.py attach \
  --capture /data/mainnet-w13 --case /data/exported-case
python3 tools/mainnet-replay/gate.py attach-all \
  --capture /data/mainnet-w13 --cases /data/replay-cases   # every case; failures -> attach-<dir>.json
```

Failed imports remain visibly marked and cannot pass the gate. Imports never overwrite prior cases.

## Native adapter contract and run

Provide a JSON argv file. For the implemented cold adapter that is
`["/abs/neard", "--home", "/abs/node-home", "view-state", "state-witness", "cold-validate"]`. The
gate appends the case directory, invokes it without a shell, and requires exit zero and exactly
one JSON object containing:

```json
{
  "chain_id": "mainnet",
  "nearcore_commit": "44f7ae6cd7ef08bab604e20a473bf77e35d4c993",
  "block_hash": "BASE58_INCLUDED_BLOCK_HASH",
  "chunk_hash": "BASE58_CHUNK_HASH",
  "claim_sha256": "HEX_SHA256_OF_CLAIM",
  "witness_sha256": "HEX_SHA256_OF_WITNESS",
  "facts_verified": true,
  "verdict": "accept",
  "finality": {"final": true, "canonical": true, "included_block_hash": "BASE58_INCLUDED_BLOCK_HASH"},
  "cache": {"policy": "cold", "entries_before": 0}
}
```

`finality.included_block_hash` must equal the archive's block hash for the slot. The gate rejects
any row without a final, canonical including block or without an empty compiled-contract cache.

The adapter is trusted test infrastructure, not a proof oracle for Lean. It must actually run
pinned nearcore `pre_validate_chunk_state_witness` and `validate_chunk_state_witness` against the
node context and verify claim facts. `cold-validate` does ([native/README.md](native/README.md),
including its deliberate-breakage controls). A canned success JSON is invalid evidence. In particular,
`neard ... state-witness validate` printing “Validation finished” is **not** a machine-readable
acceptance result: the pinned implementation logs the asynchronous result. It cannot be wrapped
as success based solely on exit status. This is why the gate requires an explicit adapter instead
of pretending the existing CLI already provides the necessary contract.

```sh
make d3-drivers
make w13-gate \
  W13_CAPTURE=/data/mainnet-w13 \
  W13_NATIVE_COMMAND_FILE=/data/native-command.json \
  W13_REPORT=/data/mainnet-w13-results W13_JOBS=8
```

`W13_TIER` defaults to `allFeatures`. `W13_JOBS` runs cases concurrently: the adapter opens the
store read-only, so parallel instances are safe. Blinded inputs are kept under
`W13_REPORT/blind-cases/` only for cases that did not match.

Without inputs or the adapter this command fails and still writes a failure report. Small captures
can be run through the same command for diagnostics; they always fail the 1,000-block gate.

`make w13-test` runs offline adversarial harness tests. The existing CI `difftest-gates` job also
runs them through `oracle/tools/test_*.py`; a green harness job **does not** certify W13 mainnet
replay. See the live, explicitly failing acquisition probe under
`docs/evidence/lean-chunk-completion/mainnet-w13-probe/`.

## FastNear access or a local nearcore node

FastNear credentials can be supplied as `--api-key-env FASTNEAR_API_KEY` to `capture`.
Only the environment-variable **name** is recorded; the key travels in a bearer header. Query-string
credentials are rejected, and cross-origin redirects drop authorization. There is no need to paste
an API key into chat or put it in a manifest.

The published [FastNear API index](https://docs.fastnear.com/openapi) and
[NEAR Data interface](https://docs.fastnear.com/neardata) describe block/shard/receipt data, not a
chunk state-witness download endpoint. Private witness or recorded-state-transition exports may
still be available; the exact API product/endpoint must be established before implementing that
source adapter. Indexed state changes and RPC account values do not replace trie proof nodes.

A non-validator nearcore node is not guaranteed to receive all shards' validator witnesses. The
pinned source has another route: build `neard` with `--features shadow_chunk_validation`, track
and execute the relevant shard states, and enable `save_latest_witnesses` in an isolated capture
node. `chain/client/src/stateless_validation/shadow_validate.rs` generates witnesses from processed
chunks and saves them; `chain/chain/src/chain.rs` records state transitions for this feature.
This is a stateful synchronization/execution route, not a stateless public witness subscription.
Its source explicitly notes a resharding limitation, so do not assume it covers boundary windows.

`chain/chain/src/store/latest_witnesses.rs` retains at most **1,800 witnesses or 4 GB** (and skips
individual witnesses above 128 MB). Export continuously or implement an append-only capture hook;
one final dump cannot guarantee the roughly 10,000+ witnesses needed for 1,000 all-shard blocks.
`view-state state-witness generate` can replay recorded state in a node database, but its current
command only validates/logs results; it does not automatically supply the W13 claim/native adapter.

## Captured single-shard diagnostic and the 2026-10-27 gate dry run

The node acquired 1,223 witnesses/full chunks for shard 13 at heights 221489407–221490629.
[The diagnostic replay](../../docs/evidence/lean-chunk-completion/mainnet-w13-shard13/README.md)
reports 1,223 native/Lean matches, 0% mismatch and 100% coverage of that captured shard population.
Use [the native exporter and diagnostic runner](native/README.md) to reproduce it. This retains the
native compiled-code cache and covers one shard; it does not pass or weaken the full W13 gate.

The same 1,223 cases were then run through `make w13-gate` with the cold adapter, against an
archive capture of all ten shards for heights 221489407–221490629:
[mainnet-w13-gate-dryrun](../../docs/evidence/lean-chunk-completion/mainnet-w13-gate-dryrun/README.md).
Shard 13: 1,221 match, cold and blind. The last two heights (221490628–9) are errors, because
they are above the pilot store's final head (221490627), so the adapter does not admit them. The
gate **fails**, as it must: coverage is 9.98% (1,221/12,230), and the other nine shards have no
witnesses.
