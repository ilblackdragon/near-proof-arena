# Claim encoding v1 — `near-arena-claim-v1`

Canonical byte formats for the challenge statement
`near/pv86/receipt-transfer-batch/v0` (nearcore `2.13.4`,
commit `44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, protocol version 86).
Semantics are in `spec/near-transfer-receipt-v1.md`; the Lean definitions are
in `spec/lean/NearSpec/` (encoders are the specification; decoders are
implementations checked against them).

| file | who sees it | role |
|---|---|---|
| `request.bin` | judge, prover (`prove --request`) | the job: context + the ordered receipt batch |
| `witness.bin` | prover only (`prove --witness`) | trie nodes and account values for the touched paths |
| `claim.bin` | everyone; the only statement input of `verify` | public statement |
| `params.bin` | judge-run `prepare` | challenge-level public parameters |
| `state.bin` | judge/oracle only (dev fixtures publish it) | full synthetic pre-state, for re-execution |

## 1. Conventions (all files)

* Integers are fixed-width little endian: `u8`, `u16`, `u32`, `u64`, `u128`.
* `bytes` = `u32` LE length ‖ raw bytes (borsh `Vec<u8>`/`String`).
* `hash` = 32 raw bytes (SHA-256 output), no length prefix.
* `Vec<T>` = `u32` LE count ‖ elements.
* Every file starts with a **format tag** (`bytes`), compared byte-for-byte
  against the exact constant; an unknown tag (including another version) is
  rejected. Then the **statement id** `bytes` =
  `near/pv86/receipt-transfer-batch/v0` (except `witness.bin`, `state.bin`).
* Decoding is strict: truncation, trailing bytes, length prefixes that run past
  the end, unknown enum tags and non-canonical values (see per-field rules) are
  rejected. There is exactly one encoding of each value: integers are
  fixed-width, so there are no alternative length encodings to normalize.

## 2. `request.bin` — `near-arena-request-v1`

```
bytes   format_id        = "near-arena-request-v1"
bytes   statement_id     = "near/pv86/receipt-transfer-batch/v0"
u32     protocol_version                      (domain: = 86)
bytes   chain_id         1..64 bytes, 0x21..0x7e   (domain: = "mainnet")
u64     shard_id                              (bound; non-semantic for this slice)
u64     block_height                          (semantic: refund receipt ids)
u128    block_gas_price                       (semantic: burn price)
u64     gas_limit                             (semantic: compute limit, domain R4)
hash    pre_state_root                        (shard trie root before the batch)
u32     n                                     (domain: 1..=256)
Receipt × n                                   nearcore borsh of `Receipt`, in order
```

`Receipt` is nearcore's own borsh (`core/primitives/src/receipt.rs`); for the
slice shape it is:

```
bytes predecessor_id ‖ bytes receiver_id ‖ hash receipt_id ‖
u8 0 (ReceiptEnum::Action) ‖ bytes signer_id ‖ PublicKey ‖ u128 gas_price ‖
u32 0 (output_data_receivers) ‖ u32 0 (input_data_ids) ‖
u32 1 ‖ u8 3 (Action::Transfer) ‖ u128 deposit
PublicKey = u8 0 ‖ 32 bytes (ED25519) | u8 1 ‖ 64 bytes (SECP256K1)
```

A request containing any receipt not of this shape (other `ReceiptEnum`
variant, data dependencies, more than one action, a non-Transfer action, an
ML-DSA-65 key, ...) is **out of domain**: the judge never issues it as a job and
checkers classify it `out_of_domain`.

Block fields deliberately absent: `block_timestamp`, `prev_block_hash`,
`random_seed`, `epoch_id`, congestion info, bandwidth requests. None of them
influences the slice's outputs (they feed contract execution, the bandwidth
scheduler and congestion control, which are excluded); adding them would bind
values the relation cannot constrain.

## 3. `claim.bin` — `near-arena-claim-v1` (public statement)

```
bytes   format_id        = "near-arena-claim-v1"
bytes   statement_id     = "near/pv86/receipt-transfer-batch/v0"
u32     protocol_version
bytes   chain_id
u64     shard_id
u64     block_height
u128    block_gas_price
u64     gas_limit
hash    pre_state_root
u32     receipt_count
hash    receipts_commitment        sha256(u64 shard_id ‖ Vec<Receipt>)
hash    slice_post_root            projection root (NOT an on-chain root)
hash    outcome_root               nearcore merklize over outcome to_hashes()
u32     refund_count
hash    refunds_commitment         sha256(Vec<Receipt>) of generated gas refunds
u64     gas_burnt_total
u128    tokens_burnt_total
```

Lean: `NearSpec.TransferV1.Claim`, `Claim.encode` (specification),
`decodeClaim` (strict decoder) with the proved round trip
`decodeClaim_encode : c.wf → decodeClaim c.encode = some c` and
`Claim.encode_injective` (`spec/lean/NearSpec/ClaimCodec.lean`). Every public
value is bound: two well-formed claims with equal bytes are equal.
Size: 302 bytes + `len(chain_id)`; with `mainnet` every claim is **309 bytes**;
`max_claim_bytes` = 302 + 64 = **366**.

### 3.1 Commitments

* `receipts_commitment = sha256(u64 shard_id ‖ u32 n ‖ Receipt_1 ‖ … ‖ Receipt_n)` —
  i.e. `sha256(borsh((ShardId, Vec<Receipt>)))`, the exact form nearcore uses
  for one destination-shard bucket of a chunk's outgoing receipts
  (`chain/chain/src/chain.rs:4102-4130 build_receipts_hashes`). It therefore
  equals a leaf of the source chunk's `outgoing_receipts_root` **when the batch
  is exactly one source chunk's receipts for this shard, in that order**. In
  general (several source chunks, shuffled by the chain) it is just a hash of
  the ordered batch; anchoring the batch to the chain is external (§6).
* `outcome_root = merklize([o.to_hashes() for o in outcomes]).0`
  (`chain/chain/src/types.rs:151-163`): leaf `= sha256(u32 2 ‖ receipt_id ‖
  sha256(PartialExecutionOutcome))`, inner `sha256(l ‖ r)`, odd node promoted.
  Within the domain the chunk executes exactly these receipts and nothing else,
  so this IS nearcore's chunk outcome root (the next chunk header's
  `prev_outcome_root`).
* `refunds_commitment = sha256(u32 k ‖ Refund_1 ‖ … ‖ Refund_k)` over the
  generated gas-refund receipts in creation order (one per receipt with
  `receipt.gas_price > block_gas_price`), each a full nearcore `Receipt`
  (predecessor `system`, receiver = signer, id
  `sha256(receipt_id ‖ block_height_le64 ‖ 0_le64)`, gas_price 0,
  `[Transfer{(gas_price − block_gas_price)·G}]`). In a single-shard layout
  with no buffering these are exactly the chunk's outgoing receipts, and
  `prev_outgoing_receipts_root = sha256(sha256(u64 shard_id ‖ Vec<Refund>))`.
* `gas_burnt_total = n·G` (= chunk `gas_used`, G = 223 182 562 500);
  `tokens_burnt_total = Σ G·min(gas_price_i, block_gas_price)` (=
  `stats.balance.tx_burnt_amount` = the chunk's `prev_balance_burnt` here,
  since slashed/other/subsidized are zero in the domain).

## 4. `witness.bin` — `near-arena-witness-v1` (prover only)

```
bytes   format_id = "near-arena-witness-v1"
hash    pre_state_root                      (must equal request.pre_state_root)
u8      0                                   PartialState::TrieValues
u32     m
bytes × m                                   strictly ascending (bytewise), no duplicates
```

The tail after `pre_state_root` is exactly nearcore's
`borsh(PartialState::TrieValues(values))` as produced by nearcore's
`TrieRecorder` for reads of `TrieKey::Account{receiver}` for every receiver,
on the pre-state trie (oracle: `recording_reads_new_recorder` + `get`). Each
value is either a `RawTrieNodeWithSize` serialization or an account value
(72 bytes); entries are addressed by `sha256(entry)`. The relation's witness
(`NearSpec.TransferV1.Witness`) is the receipts plus a *partial trie*; a
prover is free to use any witness representation internally. `witness.bin` is
never given to `verify`.

## 5. `params.bin`, `state.bin`

```
params.bin:  bytes "near-arena-params-v1" ‖ bytes statement_id ‖ u32 86 ‖
             bytes "mainnet" ‖ hash runtime_config_digest
state.bin:   bytes "near-arena-state-v1" ‖ u32 k ‖ (bytes key ‖ bytes value) × k,
             keys strictly ascending (raw trie keys, e.g. 0x00 ‖ account_id)
```

`runtime_config_digest` is defined in `spec/near-transfer-receipt-v1.md` §8.

## 6. Classification of every value

| value | class | anchored by / trusted how |
|---|---|---|
| protocol_version, chain_id | public, fixed by challenge (domain) | challenge definition; consensus/epoch (external trust) that the chunk ran at PV 86 |
| shard_id | public, bound | external: shard layout / epoch manager (non-semantic for transfers) |
| block_height, block_gas_price | public, bound, semantic | block header (external: block validity/finality) |
| gas_limit | public, bound, semantic | chunk header `gas_limit` |
| pre_state_root | public, bound | real `prev_state_root`: the current chunk header field (= post-state of the previous chunk) |
| receipts | in `request.bin`; claim holds the commitment | external: the receipts are the chunk's incoming receipts, proven by receipt proofs against source chunks' `outgoing_receipts_root` (NOT proven here) |
| trie nodes, account values | witness | proven: hash-linked to `pre_state_root` inside the relation |
| slice_post_root | public output | proven projection; **not** an on-chain root (bandwidth-scheduler write excluded) |
| outcome_root | public output | proven; equals the next chunk header's `prev_outcome_root` for a chunk consisting of exactly this batch |
| refund_count, refunds_commitment | public output | proven |
| gas_burnt_total, tokens_burnt_total | public output | proven; equal `prev_gas_used`, `prev_balance_burnt` in the domain |
| runtime config (fees, limits) | pinned constants | `runtime_config_digest`; constants in `NearSpec.Params` |

**Not proven by an admitted proof:** block or chunk finality; data
availability; that the receipts were actually included/routed to this shard in
an authorized block (receipt inclusion); that `pre_state_root` is on chain;
that the chain ran PV 86 with mainnet parameters at that height; the
bandwidth-scheduler write and therefore the on-chain post-state root;
signatures, transactions, and everything listed in the spec's exclusions.
