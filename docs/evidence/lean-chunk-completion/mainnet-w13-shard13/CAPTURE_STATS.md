# Captured shard-13 payload statistics

Decoded all 1,223 raw `ShardChunk` and `ChunkStateWitness` payloads using the pinned nearcore
Borsh types. Heights 221489407–221490629. Every chunk hash matches its witness header.
These are payload-content counts, **not an execution trace**: source-receipt proofs may include
more than the receipts applied, and delayed/postponed execution cannot be inferred from counts.

| Top-level action | Captured chunk transactions | Witness source receipts | Chunk previous outgoing receipts |
|---|---:|---:|---:|
| FunctionCall | 144 | 451 | 424 |
| Transfer | 3 | 463 | 585 |
| Delegate | 0 | 18 | 0 |
| AddKey | 0 | 1 | 0 |
| CreateAccount | 0 | 1 | 0 |
| All other action variants | 0 | 0 | 0 |
| **Total** | **147** | **934** | **1,009** |

The 18 Delegate wrappers contain 18 additional FunctionCall actions: `l2_claim` 10,
`harvest` 4, `recruit_tinkers` 2, `upgrade_tinker` 2. They are reported separately rather than
counted both as wrapper and child in the top-level table. Transfer actions can include refunds;
these counts are not all user-initiated payments. The columns describe overlapping pipeline stages
and must not be added into a unique executed-action total.

- Captured chunk transactions: **147**, in **132/1,223 chunks**; max 3 per chunk.
- Witness replay transactions: **148** (145 FunctionCall, 3 Transfer), in 133 witnesses. A witness
  attests prior execution, so window-edge totals differ from the endorsed chunk's new transactions.
- Witness new transactions: **147**, matching captured chunk transactions.
- Witness source receipts: **1,053**, in 530 witnesses; 641 Action, 282 ActionV2, 130 Data.
  Maximum 13 receipts in a witness's source proofs. Empty proof lists still count as proof entries.
- Chunk previous outgoing receipts: **1,112**, in 394 chunks; 687 Action, 322 ActionV2, 103 Data.
  Maximum 25 per chunk. No yield/resume/global-distribution receipts appear in these payloads.

## Witness structure and sizes

| Metric | Result |
|---|---|
| Distinct chunk hashes / reconstructed witnesses | 1,223 / 1,223 |
| Witnesses per chunk | Exactly 1 for every chunk |
| Main transitions per witness | 1 |
| Implicit transitions | 0 throughout this window |
| Source-receipt proofs per witness | Exactly 10; many contain zero receipts |
| Main-state proof entries (nodes and values) | Median 33; mean 61.53; p95 138; maximum 310 |
| Raw witness size | Minimum 6,677 B; median 7,359 B; mean 12,441 B; p95 27,591 B; maximum 80,414 B |
| Total raw witness bytes | 15,215,689 B (14.51 MiB) |
| Total full-chunk bytes | 961,004 B (0.92 MiB) |
| Full-chunk size | Median 417 B; mean 786 B; p95 2,147 B; maximum 10,624 B |
| Captures reporting accessed code | 279; eight distinct code hashes; no missing-code reports |

The 371 state-sync parts from node bootstrap are unrelated to the witness count. These exports
contain reconstructed witnesses, not a count of erasure-coded witness network fragments.
Proof entries include serialized trie nodes and values, not just separate Merkle proofs.

Top methods in witness source receipts: `ft_resolve_transfer` 113, `ft_transfer_call` 110,
`ft_transfer` 75, `unstake` 38, `near_withdraw` 36. Nested delegate methods are separate above.
The full method/action distributions and per-chunk statistics are in `capture-stats-summary.json`
and `capture-stats.jsonl.gz`. This single-shard window does not cover every protocol action family.

## Reproduce

Copy `tools/mainnet-replay/native/capture_stats.rs` from this repository into
`core/primitives/examples/w13_capture_stats.rs` in the pinned nearcore checkout. Build from that
checkout with Rust 1.93.0, using the capture build's target directory and release settings:

```sh
CARGO_BUILD_JOBS=8 CARGO_TARGET_DIR=/tmp/nearproof-neard-target \
  CARGO_PROFILE_RELEASE_LTO=false CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16 \
  cargo +1.93.0 build -p near-primitives --example w13_capture_stats --release --locked
/tmp/nearproof-neard-target/release/examples/w13_capture_stats \
  /data/illia/nearproof-deps/mainnet-w13/exports > /tmp/capture-stats.jsonl
```

From the nearproof repository root:

```sh
python3 tools/mainnet-replay/capture_stats.py /tmp/capture-stats.jsonl --out /tmp/capture-stats-summary.json
```

No running node/database/RPC is needed for this decode. The summary binds the decoded JSONL hash;
`capture-stats-provenance.json` binds decoder source/binary and the exact payloads decoded.
