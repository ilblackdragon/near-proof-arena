# Mainnet shard-13 blind replay — 2026-10-25

**PASS for the captured single-shard diagnostic: Lean computes every transition output from inputs
that do not contain it.** Full W13 remains open.

Same population as [the verdict diagnostic](../mainnet-w13-shard13/README.md): 1,223 consecutive
shard-13 chunks, heights 221489407–221490629, mainnet PV86, all native-accepted. Source is committed
HEAD (`git-head.txt`); Lean `allFeatures` binary `a603a893…` (in `report.json`).

## What "blind" means here

For each case `tools/mainnet-replay/blind_inputs.py` writes a new `claim.bin`/`witness.bin` in which
every value the transition produces is zeroed or emptied:

* both copies of the endorsed chunk header (claim `chunk_inner`, witness chunk header):
  `prev_state_root`, `prev_outcome_root`, `prev_gas_used`, `prev_balance_burnt`,
  `prev_outgoing_receipts_root`, `prev_validator_proposals`, `congestion_info`,
  `bandwidth_requests`, `encoded_merkle_root`, `encoded_length`;
* the witness's main and implicit transitions' `post_state_root`.

A case is refused unless no real 32-byte output, and not the real header, occurs anywhere in the
blinded files. The only values exempted from that scan are empty-chunk protocol constants (the
no-receipts outgoing root of the layout and the encoded root of the empty body), computed from the
claim's layout and Reed–Solomon parameters; they occur in other shards' headers in the segment.

The checker runs with `--blind`: it skips every comparison against a produced value and emits what
it computed. Expected values come from the canonical mainnet chunk (`chunk.borsh` in the capture),
whose header is hash-checked against the captured chunk hash and found in the captured block. Lean
never reads that file.

## Result (`report.json`, `summary.json`)

| | |
|---|---|
| cases | 1,223 / 1,223 match, 0 field differences |
| fields compared | stateRoot, outcomeRoot, gasUsed, balanceBurnt, outgoingReceiptsRoot, proposals, txRoot, encodedMerkleRoot, encodedLength, congestion, bwRequests |
| control: blinded inputs with comparisons on | 1,223 / 1,223 reject (the inputs really lack the values) |
| verdict replay on the original inputs (`verdict-report.json`) | 1,223 / 1,223 match |
| window content | 581 chunks with nonzero gas, 394 with nonzero balance burnt, 1,223 distinct state roots, 395 distinct outgoing roots, 471 nonempty bodies, 1,112 emitted receipts |

**Not exercised by this window:** validator proposals, bandwidth requests, nonzero congestion and
implicit transitions (missing chunks) — those fields were compared only at their empty/zero values.
Native validation still uses the node's warm compiled-contract cache; this is not the cold all-shard
W13 gate (`w13_gate_pass: false`).

## Reproduce

```sh
python3 tools/mainnet-replay/shard_replay.py --blind \
  --captures /data/illia/nearproof-deps/mainnet-w13/exports \
  --cases /data/illia/nearproof-deps/mainnet-w13/replay-cases \
  --binary spec/lean/v3/.lake/build/bin/nearspec-v3-check-successor \
  --native-binary /tmp/nearproof-neard-target/release/neard \
  --tier allFeatures --shard 13 --jobs 12 --out <new dir>
```

Blinded cases are written under `<out>/blind-cases/` (157 MB for this window; not committed).
`manifest.sha256` hashes the files here.
