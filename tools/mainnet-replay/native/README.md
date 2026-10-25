# Single-shard diagnostic export and replay

This exports claim-v3 context from the offline capture node's actual chain store and epoch
manager, reruns native witness validation synchronously, and compares the current Lean successor.
It is **not the cold, all-shard W13 admission gate**. Native execution gets a fresh main-transition
cache per case but retains the node's existing compiled-contract cache. The current helper exports
claims; it does not independently verify externally supplied claims for `gate.py`'s native-adapter
contract. Mainnet provenance is anchored to the local canonical node store, not an independent
finality proof. Full per-field observable export remains W01 work; Lean checks recomputed commitments.

`w13_claim.rs` adapts `oracle/v3/src/claim.rs` to take `Chain` instead of a test client's `Client`.
`w13_enc.rs` adapts the matching encoder to use nearcore SHA256 instead of an extra sha2 dependency.
The format, backward walk, epoch facts, transaction validity and apply-fact logic are unchanged.
`w13_batch.rs` binds each captured block to the canonical store, builds claims from native context,
hash-checks and sorts contract code, and calls both native prevalidation and validation. Export
errors are retained in `exports.json`; no missing case may count as success.

## Reproduce

Use pinned nearcore `44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, Rust 1.93.0, and the capture build
recipe from `../nearcore-capture/README.md`. On that checkout:

1. Apply `replay-export.patch`.
2. Copy `w13_batch.rs`, `w13_claim.rs`, `w13_enc.rs` into `tools/state-viewer/src/`.
3. Rebuild neard using the capture recipe. Keep this diagnostic binary separately from the live node.
4. Stop the capture service before accessing its database; preserve all captures and the database.

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
