# Native W13 tools: claim export and the cold adapter

Two `neard view-state state-witness` subcommands, built into one binary from pinned nearcore
`44f7ae6cd7ef08bab604e20a473bf77e35d4c993` (2.13.4, PV86, db 49):

| Subcommand | Source | Role |
|---|---|---|
| `replay-export` | `w13_batch.rs` | Exports `claim.bin` / `witness.bin` from the capture node's own chain store and epoch manager. Also reruns native validation, with the node's **warm** compiled-contract cache. Diagnostic only. |
| `cold-validate CASE` | `w13_cold.rs` | **The W13 gate adapter** ([../README.md](../README.md), "Native adapter contract"). It verifies an externally supplied pair against the node store, cold, and prints one JSON object. |

`w13_claim.rs` adapts `oracle/v3/src/claim.rs` to take `Chain` instead of a test client's `Client`.
`w13_enc.rs` adapts the matching encoder to use nearcore SHA256 instead of an extra sha2
dependency. Both subcommands share them. The format, backward walk, epoch facts, transaction
validity and apply-fact logic are the oracle's.

## The cold adapter (`cold-validate`)

For one case directory the adapter does four things.

1. **Decodes the witness the way a validator receives it.** `near-arena-witness-v3`: the raw
   `ChunkStateWitness`, rejected above `MAX_UNCOMPRESSED_STATE_WITNESS_SIZE` (64 MiB).
   `near-arena-cwitness-v3`: the encoded bytes, refused above `MAX_COMPRESSED_STATE_WITNESS_SIZE`
   (48 MiB) and decoded with nearcore's own `EncodedChunkStateWitness::decode` (64 MiB limit).
2. **Fixes the finality and provenance boundary.** The block that includes the chunk must be the
   canonical block at `height_created` in the node store, and must carry this chunk as a new chunk
   (`height_included == height`). It must also be at or below the store's final head, and the final
   head must itself be canonical. Finality here is nearcore's doomslug finality as the node accepted
   it while syncing headers. It is not a light-client proof (see "Trust boundary" below).
3. **Verifies every trusted claim fact** (spec/claim-v3.md §2.4, T1–T14). It recomputes the claim
   from the node's store and epoch manager (`build_claim`) and requires the supplied `claim.bin` to
   be **byte-identical**. That covers section B (the segment the validator's backward walk reads),
   section C (Reed–Solomon parameters, epochs, layouts, validators, epoch-start flags, apply facts,
   `tx_valid`, genesis chunk extra), `protocol_version` and `chain_id`. `epoch_id` (T1) is also
   checked against `get_epoch_id_from_prev_block`, because `build_claim` copies it from the witness.
   `facts_verified` is true only if all of this holds and the protocol version is 86.
4. **Validates cold.** It builds a fresh `NightshadeRuntime` whose compiled-contract cache is an
   empty `FilesystemContractRuntimeCache` in a new temporary home. That home is created per case,
   checked empty before execution (`cache.entries_before == 0`) and deleted afterwards. The node's
   `data/contract.cache` is never opened. The adapter refuses a configured absolute
   `contract_cache_path`, because it could point at a warm cache. Contract code comes only from
   `witness.bin`'s `contract_code`, merged into `main_state_transition.base_state` exactly as
   `partial_witness_tracker.rs:692-696` does. State snapshots are disabled and the main-transition
   cache is fresh. The verdict is the `Result` of pinned `pre_validate_chunk_state_witness` +
   `validate_chunk_state_witness`, run synchronously.

   If the supplied code exceeds `MAX_UNCOMPRESSED_CONTRACT_CODE_RESPONSE_SIZE` (64 MiB), the verdict
   is `reject`. A cold validator cannot receive that code, so the case is out of domain
   (`w.code_response_size`); `code.response_within_limit` is `false`. The bound counts every supplied
   blob, so it is conservative.

Output (one line). `gate.py` requires the contract fields plus `finality.final`,
`finality.canonical`, `finality.included_block_hash == archive block hash`, `cache.policy == "cold"`
and `cache.entries_before == 0`:

```json
{"chain_id": "mainnet", "nearcore_commit": "44f7ae6c…", "block_hash": "…", "chunk_hash": "…",
 "claim_sha256": "…", "witness_sha256": "…", "facts_verified": true, "verdict": "accept",
 "native_error": null, "facts": {"claim_equal": true, "first_difference_offset": null, …},
 "finality": {"canonical": true, "final": true, "included_block_hash": "…", "final_head_height": …},
 "cache": {"policy": "cold", "entries_before": 0, "entries_after": 2, …}, "code": {…}}
```

If the adapter cannot finish, it prints `{"facts_verified": false, "verdict": null,
"adapter_error": …}`. The gate records that as an error, never as a match or a mismatch.

`nearcore_commit` is fixed at compile time from `W13_NEARCORE_COMMIT` (below). It is the builder's
label. The gate also hashes the executable, and that hash is the binding identity.

### Trust boundary (what is checked, what is trusted)

| Item | How it enters | Checked by |
|---|---|---|
| Block window and chunk denominator | Archive capture (`gate.py capture`): consecutive `prev_hash` chain | `gate.py inventory` |
| Including block is canonical and final | Node store: canonical hash at the height, ≤ final head | adapter `finality`, compared by `gate.py` with the archive block hash (two sources) |
| Claim segment (section B) | Hash chain from `chunk_inner.prev_block_hash` | Lean `Rel`; adapter byte equality; `gate.py anchor_case` (every hash in the archive) |
| Chunk identity | `chunk_inner` | `gate.py anchor_case` (hash = archive chunk hash); adapter byte equality with the witness header |
| Trusted facts (section C, T1–T14) | Node epoch manager and store | adapter recomputation + byte equality |
| Header validity, BFT/doomslug signatures, epoch-manager correctness | **trusted**: the pinned node's own sync | not checked here (out of scope for the Lean relation) |

So a gate pass means this: for every chunk that pinned nearcore 2.13.4, run cold, accepted in
canonical, final mainnet blocks (as seen by a pinned node and an independent archive), Lean
computed the same header outputs blind. It is not a light-client proof that those blocks are
mainnet.

### Deliberate-breakage controls

`cold_controls.py` runs the adapter on each honest case and on four mutants of it. Expected
outcomes:

* `no_code`: code stripped. Reject (cold). A warm cache would still accept.
* `claim_epoch`: one byte of T1 flipped. Facts rejected.
* `claim_tail`: last claim byte (T14 tag) flipped. Facts rejected.
* `post_root`: main post state root zeroed. Reject.

```sh
python3 tools/mainnet-replay/native/cold_controls.py --native-command-file native-command.json \
  --cases /path/to/replay-cases --out /path/to/cold-controls --jobs 12
```

## Build

Copy `w13_batch.rs`, `w13_claim.rs`, `w13_enc.rs` and `w13_cold.rs` into
`tools/state-viewer/src/` of a pinned checkout. Apply `../nearcore-capture/export.patch`: it also
fixes the pinned `neard/src/cli.rs` `tcp::` import, which breaks `--no-default-features` builds.
Then apply `replay-export.patch`, which registers both subcommands.

```sh
git -C "$SRC" checkout --detach 44f7ae6cd7ef08bab604e20a473bf77e35d4c993
git -C "$SRC" apply "$REPO/tools/mainnet-replay/nearcore-capture/export.patch"
git -C "$SRC" apply "$REPO/tools/mainnet-replay/native/replay-export.patch"
cp "$REPO"/tools/mainnet-replay/native/w13_{batch,claim,enc,cold}.rs "$SRC/tools/state-viewer/src/"
cd "$SRC"
W13_NEARCORE_COMMIT=$(git rev-parse HEAD) CARGO_BUILD_JOBS=8 CARGO_TARGET_DIR=/path/to/target \
  CARGO_PROFILE_RELEASE_LTO=false CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16 \
  cargo +1.93.0 build -p neard --release --locked --no-default-features \
  --features json_rpc,shadow_chunk_validation
```

The 2026-10-27 build came from a non-VCS copy of a clean `44f7ae6c` checkout. It used
`GIT_CEILING_DIRECTORIES` so that `neard/build.rs` did not pick up an unrelated parent
repository; `neard --version` then reports `commit unknown`. Keep this binary separate from the
capture node's binary.

The adapter opens the node store read-only (the `view-state` default). Stop the capture service
first. To run it without touching a database that must stay pristine, point `--home` at a
hard-link view: copy `config.json`, `genesis.json` and `node_key.json`, hard-link `data/*.sst`
(immutable), and copy `CURRENT`, `IDENTITY`, `MANIFEST-*`, `OPTIONS-*` and the WAL `*.log`. Leave
out `contract.cache` (the warm cache) and `state_snapshot`.

## Diagnostic export (`replay-export`)

Stop the capture service before accessing its database; preserve all captures and the database.

```sh
neard --home /data/illia/nearproof-deps/mainnet-w13/home \
  view-state state-witness replay-export \
  --input /data/illia/nearproof-deps/mainnet-w13/exports \
  --output /data/illia/nearproof-deps/mainnet-w13/replay-cases
```

Output must be a new directory. Optional `--limit 1` is only a smoke run. For every capture the
command writes claim/witness bytes and `export.json`, or records the export error in `exports.json`.
Native rejects are explicit results, never inferred from process exit status. Preserve the native
binary, source patch and full export output with the run.

Build the actual intended Lean configuration with `lake build nearspec-v3-check-successor` in
`spec/lean/v3`, then from the repository root:

```sh
python3 tools/mainnet-replay/shard_replay.py \
  --captures /data/illia/nearproof-deps/mainnet-w13/exports \
  --cases /data/illia/nearproof-deps/mainnet-w13/replay-cases \
  --binary spec/lean/v3/.lake/build/bin/nearspec-v3-check-successor \
  --native-binary /absolute/path/to/the/exporting/neard \
  --tier allFeatures --shard 13 --jobs 4 \
  --out /data/illia/nearproof-deps/mainnet-w13/replay-results
```

The runner freezes a copy of the Lean binary, hashes input files and executable identities, and
checks those hashes again at completion. The selected capture directories define the population;
missing exports stay in the denominator. It requires one correctly identified result per case and
reports timeouts, malformed outputs, native rejects and unsupported cases separately.
Mismatch percentage is rejects / (accepts + rejects) among native-accepted inputs; unsupported/error
cases reduce coverage, and zero comparisons yields null rather than zero mismatch. Diagnostic
success requires every captured case to match. `w13_gate_pass` is always false for this scope.
Contiguous captured heights do not establish all-shard coverage or independently audit missing
capture slots against a full block archive.

Run offline report controls with `python3 tools/mainnet-replay/test_shard_replay.py`.

## Blind replay

Add `--blind` to the runner to grade computed outputs instead of verdicts. Each case is copied with
every produced value removed (`../blind_inputs.py`), the checker runs `--blind` and emits what it
computed, and every field must equal the canonical `chunk.borsh` header (hash-checked against the
captured chunk hash and found in the captured block). The same blinded inputs are rerun with
comparisons on as a control and must not accept. See
`docs/evidence/lean-chunk-completion/mainnet-w13-shard13-blind/README.md`. `gate.py run` always
grades this way.
