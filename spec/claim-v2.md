# Claim encoding v2 — `near-arena-claim-v2`

Canonical byte formats for the challenge statement
`near/pv86/receipt-transfer-batch/v1` (challenge `near-transfer-receipt-v2`;
nearcore `2.13.4`, commit `44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, protocol
version 86). Semantics: `spec/near-transfer-receipt-v2.md`. Lean definitions:
`spec/lean/NearSpec/TransferV2.lean` (encoders are the specification) and
`spec/lean/NearSpec/ClaimCodecV2.lean` (strict decoder, proved round trip).

This format is a **separate** statement from v1 (`spec/claim-v1.md`,
`near/pv86/receipt-transfer-batch/v0`, which stays unchanged). Every file starts
with a v2 format tag and the v1 statement id is never accepted: a v1 claim does
not decode as a v2 claim and vice versa (kernel-checked:
`NearSpec.Examples.V2Negative.v1_decoder_rejects_v2` / `v2_decoder_rejects_v1`).

| file | who sees it | role |
|---|---|---|
| `request.bin` | judge, prover | the job: context (incl. congestion info) + the ordered receipt batch |
| `witness.bin` | prover only | trie nodes and values on the receivers' Account paths **and on the path to `0x0f`** |
| `claim.bin` | everyone; the only statement input of `verify` | public statement |
| `params.bin` | judge-run `prepare` | challenge-level public parameters |
| `state.bin` | judge/oracle only (dev fixtures publish it) | full synthetic pre-state |

## 1. Conventions

As in v1 (`spec/claim-v1.md` §1): fixed-width little-endian integers, `bytes` =
`u32` length ‖ raw bytes, `hash` = 32 raw bytes, strict decoding (truncation,
trailing bytes, length prefixes past the end, unknown tags, out-of-range values
are rejected), one encoding per value. Every file starts with its format tag;
`request.bin`, `claim.bin` and `params.bin` then carry the statement id
`near/pv86/receipt-transfer-batch/v1`.

## 2. `request.bin` — `near-arena-request-v2`

```
bytes   format_id        = "near-arena-request-v2"
bytes   statement_id     = "near/pv86/receipt-transfer-batch/v1"
u32     protocol_version                      (domain: = 86)
bytes   chain_id         1..64 bytes, 0x21..0x7e   (domain: = "mainnet")
u64     shard_id                              (SEMANTIC: the only shard of the layout; domain < 2^32)
u64     block_height                          (semantic: refund receipt ids)
u128    block_gas_price                       (semantic: burn price)
u64     gas_limit                             (semantic: compute limit)
u128    delayed_receipts_gas    ┐
u128    buffered_receipts_gas   │ CongestionInfoV1 of the shard in the block
u64     receipt_bytes           │ (domain: the first three are 0)
u16     allowed_shard           ┘ (bound; not semantic under zero congestion)
u64     missed_chunks_count                   (SEMANTIC: link allowance, refund forwarding)
hash    pre_state_root
u32     n                                     (domain: 1..=256)
Receipt × n                                   nearcore borsh of `Receipt` (as in v1 §2)
```

The five congestion fields are exactly the shard's entry of
`ApplyState.congestion_info` (`ExtendedCongestionInfo { congestion_info:
CongestionInfo::V1(CongestionInfoV1 { delayed_receipts_gas,
buffered_receipts_gas, receipt_bytes, allowed_shard }), missed_chunks_count }`,
`core/primitives/src/congestion_info.rs:434-470`): the previous chunk header's
congestion info and the block's missed-chunk count for the shard.

Block fields still absent, and why that is sound inside the domain:
`prev_block_hash` (only seeds the scheduler's tie-breaking shuffle, which never
runs without bandwidth requests), `block_timestamp`, `random_seed`, `epoch_id`
(no contracts; the shard layout is fixed by the domain), block bandwidth
requests (domain `no_bandwidth_requests`: they are generated from outgoing
buffers, which are empty when `receipt_bytes = 0`).

## 3. `claim.bin` — `near-arena-claim-v2` (public statement)

```
bytes   format_id        = "near-arena-claim-v2"
bytes   statement_id     = "near/pv86/receipt-transfer-batch/v1"
u32     protocol_version
bytes   chain_id
u64     shard_id
u64     block_height
u128    block_gas_price
u64     gas_limit
u128    delayed_receipts_gas
u128    buffered_receipts_gas
u64     receipt_bytes
u16     allowed_shard
u64     missed_chunks_count
hash    pre_state_root
u32     receipt_count
hash    receipts_commitment        sha256(u64 shard_id ‖ Vec<Receipt>)          (as v1)
hash    post_state_root            the REAL Runtime::apply post-state root
hash    outcome_root               nearcore merklize over outcome to_hashes()   (as v1)
u32     refund_count
hash    refunds_commitment         sha256(Vec<Receipt>) of generated gas refunds (as v1)
u64     gas_burnt_total
u128    tokens_burnt_total
```

Lean: `NearSpec.TransferV2.Claim`, `Claim.encode`, `decodeClaim`; proved
`decodeClaim_encode : c.wf → decodeClaim c.encode = some c` and
`Claim.encode_injective`. Size: 352 bytes + `len(chain_id)`; with `mainnet`
every claim is **359 bytes**; `max_claim_bytes` = 352 + 64 = **416**.

`post_state_root` is `ApplyResult.state_root` of nearcore's `Runtime::apply` for
the chunk — the value stored in `ChunkExtra.state_root` and carried by the next
chunk header as `prev_state_root` — for a chunk in the domain. It includes the
`TrieKey::BandwidthSchedulerState` write that v1's `slice_post_root` omitted
(v1 §5), so it is **not** a projection. `receipts_commitment`, `outcome_root`,
`refunds_commitment`, `gas_burnt_total` and `tokens_burnt_total` are defined
exactly as in v1 (`spec/claim-v1.md` §3.1).

## 4. `witness.bin` — `near-arena-witness-v2` (prover only)

```
bytes   format_id = "near-arena-witness-v2"
hash    pre_state_root
u8      0                                   PartialState::TrieValues
u32     m
bytes × m                                   strictly ascending, no duplicates
```

The tail is nearcore's `borsh(PartialState::TrieValues(values))` as recorded by
nearcore's `TrieRecorder` for reads, on the pre-state trie, of
`TrieKey::Account{receiver}` for every receiver **and of
`TrieKey::BandwidthSchedulerState`**. For an absent `0x0f` key the recorded
nodes end where the path leaves the trie (the proof of absence the insert
needs); for a present key they include its value. Its total size equals that
of the storage proof nearcore itself records for the whole `apply` on all 1505
in-domain cases of the reported difftest run (`diagnostics.json`:
`slice_witness_bytes`, `full_apply_recorded_bytes`; sizes compared, not bytes).

## 5. `params.bin`, `state.bin`

```
params.bin:  bytes "near-arena-params-v1" ‖ bytes "near/pv86/receipt-transfer-batch/v1" ‖
             u32 86 ‖ bytes "mainnet" ‖ hash runtime_config_digest_v2
state.bin:   as v1 ("near-arena-state-v1"), may contain key 0x0f
```

`params.bin` keeps v1's layout (its tag names the layout); the statement id and
the digest differ. `runtime_config_digest_v2` is defined in
`spec/near-transfer-receipt-v2.md` §8.

## 6. Classification of every value

| value | class | anchored by / trusted how |
|---|---|---|
| protocol_version, chain_id | public, fixed by challenge | as v1 |
| shard_id | public, bound, **semantic** | the epoch's shard layout (external); domain: the layout has exactly this one shard |
| block_height, block_gas_price, gas_limit | public, bound, semantic | as v1 |
| delayed/buffered receipts gas, receipt_bytes, allowed_shard | public, bound | the previous chunk header's `congestion_info` (external: block validity); domain fixes the first three to 0 |
| missed_chunks_count | public, bound, semantic | the block's chunk mask history (external) |
| pre_state_root | public, bound | the real `prev_state_root` (as v1) |
| receipts | request; claim holds the commitment | external receipt inclusion (as v1) |
| trie nodes, values (Account paths, 0x0f path) | witness | proven: hash-linked to `pre_state_root` |
| post_state_root | public output | proven; the real on-chain post-state root for a chunk in the domain |
| outcome_root, refunds, gas/tokens totals | public output | proven (as v1) |
| runtime config (fees, limits, bandwidth-scheduler parameters) | pinned constants | `runtime_config_digest_v2`; constants in `NearSpec.Params`, `NearSpec.Bandwidth` |

**Not proven by an admitted proof:** block/chunk finality, data availability,
receipt inclusion, that `pre_state_root` and the congestion info are on chain,
that the shard layout at that height has exactly one shard, that the chain ran
PV 86 with mainnet parameters; everything listed in the spec's exclusions.
