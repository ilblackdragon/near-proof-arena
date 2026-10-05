# NEAR stateless chunk validation: the exact boundary (pinned nearcore)

**Pin.** `near/nearcore` tag `2.13.4`, commit `44f7ae6cd7ef08bab604e20a473bf77e35d4c993`,
`STABLE_PROTOCOL_VERSION = 86` (`core/primitives-core/src/version.rs:628`).
Checkout: `/data/illia/nearproof-deps/nearcore`. Every `file:line` below is
relative to that checkout (or, for third-party crates, to
`~/.cargo/registry/src/index.crates.io-*/<crate>-<ver>/`) and was read in the
source. Items not confirmed in source are marked **[unverified]**.

This document answers one question: *what exactly does a chunk validator
establish when it validates a `ChunkStateWitness` and endorses a chunk, and
which inputs does it take from its own chain/epoch state rather than from the
witness?* It is the source for `spec/near-chunk-validation-v0.md` and
`spec/claim-v3.md`. It supersedes nothing: `docs/research/nearcore-boundary.md`
(the `Runtime::apply` boundary used by v1/v2) stays valid and is cited for the
runtime internals.

---

## 1. Call graph and what an endorsement means

```
partial_witness_tracker::deliver_witness            (transport: RS-decode parts, zstd+borsh decode, merge contract code)
  └─ ChunkValidationActor::process_chunk_state_witness_message
       └─ process_chunk_state_witness               (prev block must be in the store)
            └─ start_validating_chunk               (epoch-id check, pre-validation, [shortcut], spawn)
                 ├─ chunk_validation::pre_validate_chunk_state_witness     (chain-store + epoch-manager reads)
                 │    ├─ ShardChunkHeader::validate_version
                 │    ├─ ValidatedTransaction::check_valid_for_config  (new_transactions)
                 │    ├─ get_state_witness_block_range               (backward walk; implicit-transition params)
                 │    ├─ validate_source_receipt_proofs              (+ filter, shuffle → receipts_to_apply)
                 │    ├─ applied_receipts_hash, tx_root of the last new chunk
                 │    └─ check_transaction_validity_period           (per tx of the last new chunk)
                 └─ chunk_validation::validate_chunk_state_witness → validate_chunk_state_witness_impl
                      ├─ apply_new_chunk (main transition, recorded storage)     → ChunkExtra, outgoing receipts
                      ├─ apply_old_chunk / resharding (each implicit transition)
                      ├─ validate_chunk_with_chunk_extra_and_receipts_root       (header vs ChunkExtra)
                      └─ tx_root(new_transactions) + validate_chunk_with_encoded_merkle_root (Reed–Solomon)
                 Ok ⇒ send_chunk_endorsement_to_block_producers
```

| step | location |
|---|---|
| contract code merged into `main_state_transition.base_state` | `chain/client/src/stateless_validation/partial_witness/partial_witness_tracker.rs:692-696` |
| witness key must equal the partial-witness key | `partial_witness_tracker.rs:685-691` |
| prev block lookup (orphan pool otherwise) | `chain/client/src/stateless_validation/chunk_validation_actor.rs:542-583` |
| `prev_block_hash` match | `chunk_validation_actor.rs:338-345` |
| `witness.epoch_id == get_epoch_id_from_prev_block(prev)` | `chunk_validation_actor.rs:384-391` |
| pre-validation | `chunk_validation_actor.rs:393-412` → `chain/chain/src/stateless_validation/chunk_validation.rs:310-444` |
| shortcut when the node already has the prev `ChunkExtra` | `chunk_validation_actor.rs:414-463` |
| full validation (spawned) | `chunk_validation_actor.rs:473-508` → `chunk_validation.rs:782-822`, `565-780` |
| endorsement | `chunk_validation_actor.rs:487-493` |

**The shortcut** (`chunk_validation_actor.rs:425-463`): a node that already
holds the `ChunkExtra` of `(prev_block_hash, shard)` (it applied the chunk
itself) skips re-execution and runs `validate_chunk_with_chunk_extra_and_roots`
(`chain/chain/src/validate.rs:99-130`): the same header comparison, tx-root
and encoded-merkle-root checks as the witness path, with `ChunkExtra` and the
outgoing receipts read from its database. Both paths decide the same
predicate when the node's database is correct; the witness path is the one a
stateless validator runs and is the one specified here. Note the shortcut runs
*after* pre-validation, so pre-validation failures reject in both paths.

**What the endorsement signs** (`core/primitives/src/stateless_validation/chunk_endorsement.rs:23-39, 117-140`):

```
signature          = sign( borsh(ChunkEndorsementInnerV1 { chunk_hash, signature_differentiator: "ChunkEndorsement" }) )
metadata_signature = sign( borsh(ChunkEndorsementMetadata { account_id, shard_id, epoch_id, height_created }) )
```

Only `chunk_hash` (and, in the metadata, `shard_id`, `epoch_id` and
`height_created`) is signed. `chunk_hash = SHA256(SHA256(borsh(inner)) ‖
inner.encoded_merkle_root)` for a `V3` header (`core/primitives/src/sharding.rs:291-296`),
where `borsh(inner)` is the **tagged** `ShardChunkHeaderInner`. The hash does
not cover `height_included` or the chunk producer's signature. So an
endorsement asserts exactly:

> *the chunk whose header inner hashes to `chunk_hash`, in epoch `epoch_id`,
> passes `validate_chunk_state_witness` against my chain.*

**Not checked on the validation path** (relevant to claim design and malleability):

* the chunk header's `signature` (no call verifies it; block producers check it when including the chunk);
* the chunk header's `height_included` (producers emit 0, `sharding.rs:384`);
* `ChunkStateTransition.block_hash` of the main and implicit transitions (never compared);
* who produced the witness: the chunk producer's signature is on the *partial* witness parts (`chain/client/src/stateless_validation/validate.rs:64-130`; signed inner `core/primitives/src/stateless_validation/partial_witness.rs:58, 92-118`), i.e. transport authentication, not part of validity.

---

## 2. `ChunkStateWitness` and the types it contains

### 2.1 Versions in use at PV 86

`ChunkStateWitness` has a single live variant: `V2 = 1` (`core/primitives/src/stateless_validation/state_witness.rs:93-99`; V1 removed).
`ShardChunkHeader` is accepted iff it is `V3` (tag 2) with inner `V4` (tag 3, always) or `V5`
(tag 4, iff `DynamicResharding` = PV 85 is enabled); `V1`/`V2` headers, inner V1–V3, and inner V6 (Spice, PV 180)
are rejected (`ShardChunkHeader::validate_version`, `sharding.rs:606-632`; run at `chunk_validation.rs:318-320` with the
protocol version of `witness.epoch_id`). New headers are V3/inner V5 (`sharding.rs:318-355`).

### 2.2 Byte layout (borsh)

```
u8 0x01                                         ChunkStateWitness::V2
[32]  epoch_id
ShardChunkHeader chunk_header                   §2.3
ChunkStateTransition main_state_transition      { [32] block_hash, PartialState base_state, [32] post_state_root }   (state_witness.rs:279-295)
HashMap<ChunkHash, ReceiptProof> source_receipt_proofs
[32]  applied_receipts_hash
Vec<SignedTransaction> transactions             txs of the LAST NEW chunk of the shard (applied by the main transition)
Vec<ChunkStateTransition> implicit_transitions  forward chronological order
Vec<SignedTransaction> new_transactions         txs of the chunk being validated
```
(`state_witness.rs:103-166`.) `PartialState = 0x00 ‖ u32 n ‖ n × (u32 len ‖ bytes)`
(`core/primitives/src/state.rs:7-17`), trie nodes and values exactly as the
`TrieRecorder` stores them (`docs/research/nearcore-boundary.md` §6).
`ReceiptProof = (Vec<Receipt>, ShardProof { from_shard_id u64, to_shard_id u64, proof: Vec<MerklePathItem{[32] hash, u8 direction}> })`
(`sharding.rs:936-963`, `core/primitives/src/merkle.rs:18-40`). `Receipt` is
`ReceiptV0` with no tag (`core/primitives/src/receipt.rs:221-233`). `SignedTransaction =
Transaction ‖ Signature`; `Transaction` V0 untagged / V1 = `0x01 ‖ …` with the
2-byte look-ahead rule (`core/primitives/src/transaction.rs:219-270`).

Decoding rules that matter for a re-implementation:

* `borsh::from_slice`/`from_reader` reject trailing bytes (borsh-1.5.3 `de/mod.rs:46-53, 1034-1041`).
* `HashMap` deserialization does **not** require sorted or unique keys (`de_strict_order` is not enabled; borsh `de/mod.rs:541-574`, nearcore `Cargo.toml:171`): any order is accepted and a duplicate key keeps the **last** value. Serialization sorts by key.
* `AccountId` deserialization validates the id (near-account-id-2.0.0 `src/borsh.rs:9-30`); `Signature::ED25519` rejects `sig[63] & 0xE0 != 0` (`core/crypto/src/signature.rs:1180-1182`); `PublicKey`/`Signature` tags 0/1/2 = ED25519/SECP256K1/MLDSA65 (`signature.rs:371-411, 1148-1196`).
* The raw (uncompressed) witness must be ≤ `MAX_UNCOMPRESSED_STATE_WITNESS_SIZE` = 64 MiB (`state_witness.rs:19-20`; enforced by the counting reader in `CompressedData::decode`, `core/primitives/src/utils/compression.rs:44-76`, `utils/io.rs:64-90`).
* On the wire the witness is `zstd(level 1)(borsh(witness))`, RS-coded into one part per chunk validator (data ratio 0.6, `chain/client/src/stateless_validation/partial_witness/encoding.rs:6-14`), each part signed by the chunk producer. Compression and the part code are transport; only the decoded borsh value reaches validation.
* Contract code: accessed contracts are **not** in the produced witness; the validator fetches them (`ChunkContractAccesses`, signed by the chunk producer) and appends them as extra `TrieValues` to the main transition's `base_state` before validation (`partial_witness_tracker.rs:692-696`). For any chunk without function calls this list is empty.

### 2.3 `ShardChunkHeader` V3 / inner V5 layout

```
u8 0x02 (V3) ‖ u8 0x04 (inner V5; 0x03 = V4)
[32] prev_block_hash ‖ [32] prev_state_root ‖ [32] prev_outcome_root ‖ [32] encoded_merkle_root
u64 encoded_length ‖ u64 height_created ‖ u64 shard_id ‖ u64 prev_gas_used ‖ u64 gas_limit
u128 prev_balance_burnt ‖ [32] prev_outgoing_receipts_root ‖ [32] tx_root
Vec<ValidatorStake> prev_validator_proposals        (0x00 ‖ AccountId ‖ PublicKey ‖ u128 each)
CongestionInfo congestion_info                      (0x00 ‖ u128 delayed_receipts_gas ‖ u128 buffered_receipts_gas ‖ u64 receipt_bytes ‖ u16 allowed_shard)
BandwidthRequests bandwidth_requests                (0x00 ‖ Vec<{u16 to_shard, [u8;5] bitmap}>)
Option<TrieSplit> proposed_split                    (V5 only: AccountId ‖ u64 left_memory ‖ u64 right_memory)
u64 height_included ‖ Signature signature           (outside the inner; not hashed)
```
(`sharding.rs:236-248, 388-395`; `sharding/shard_chunk_header_inner.rs:365-427`;
`congestion_info.rs:187-189, 460-470`; `bandwidth_scheduler.rs:28-79, 131, 183-225`;
`trie_split.rs:20-27`; `types.rs:589-601, 787-798`.) The `hash` field is
`#[borsh(skip)]` and recomputed on deserialize (`sharding.rs:287-289`).
`is_new_chunk(h) ⇔ height_included == h` (`sharding.rs:460-462`); `is_genesis ⇔ prev_block_hash == 0^32` (`sharding.rs:491-494`).

### 2.4 Block header and chunk slots (chain context, not witness)

At PV 86 blocks are `BlockV4 { header, body: BlockBody::V2 }`; headers are `BlockHeader::V6` (tag 5)
= `prev_hash ‖ inner_lite ‖ inner_rest_v6 ‖ signature` (`core/primitives/src/block.rs:80-108`,
`block_header.rs:647-664, 939-1090`). `inner_lite` = `height, epoch_id, next_epoch_id,
prev_state_root, prev_outcome_root, timestamp, next_bp_hash, block_merkle_root`
(`block_header.rs:30-47`); `inner_rest_v6` includes `chunk_headers_root, random_value,
chunk_mask, next_gas_price, last_final_block, …, shard_split` (`block_header.rs:308-354`).

* **Block hash** = `SHA256( SHA256( SHA256(borsh inner_lite) ‖ SHA256(borsh inner_rest) ) ‖ prev_hash )` (`block_header.rs:781-791`). Version tag and signature are not hashed.
* **Chunk slots.** A block has one chunk header per shard index (`block.rs:530-532, 718-729`), new or carried over. `chunk_headers_root = merklize([ChunkHashHeight(chunk_hash, height_included) for each slot])` (`block.rs:815-822`, `sharding.rs:700-703`). So a block hash authenticates, per slot, exactly `(tagged inner, height_included)` — the same data the validator uses — and nothing else (not the chunk signature).
* `merklize` (`merkle.rs:46-110`): leaf = `SHA256(borsh(item))`; inner = `SHA256(l ‖ r)`; an odd last node is promoted unchanged; `[]` → `0^32`; one item → its leaf hash.

---

## 3. Pre-validation (`pre_validate_chunk_state_witness`, `chunk_validation.rs:310-444`)

| # | check / computation | inputs | source of inputs |
|---|---|---|---|
| P1 | `chunk_header.validate_version(pv)` (:318-320) | header; `pv = epoch_info(witness.epoch_id).protocol_version` | witness; **epoch manager** |
| P2 | each `new_transactions[i]` passes `check_valid_for_config(runtime_config(pv), tx, pv)` (:323-341): V1 tx needs GasKeys, `Strict` nonce mode needs StrictNonce, PQ keys need PostQuantumSignatures, `wire_size ≤ max_transaction_size` (1 572 864) (`transaction.rs:302-341, 448-461`; `runtime_configs/69.yaml:3`). **No signature check here.** | witness | witness + pinned config |
| P3 | backward walk `get_state_witness_block_range` (§4) | `prev_block_hash` | **chain store, epoch manager** |
| P4 | `receipts_to_apply = validate_source_receipt_proofs(...)` (§5) | `source_receipt_proofs` + blocks | witness + **chain store** |
| P5 | `SHA256(borsh(Vec<Receipt> receipts_to_apply)) == applied_receipts_hash` (:360-367) | | witness |
| P6 | `merklize(transactions).root == tx_root` of the last new chunk's header in `last_chunk_block` (:368-380) | | witness + **chain** |
| P7 | per tx of `transactions`: `check_transaction_validity_period(header(last_chunk_block.prev_hash), tx.block_hash)` → `Vec<bool>` (:382-401; `chain/chain/src/store/utils.rs:56-75, 130-177`); **invalid txs are skipped by `apply`, not rejected**; all `true` if `last_chunk_block` is genesis | | **chain store** (depends on canonical chain and `transaction_validity_period` from genesis config) |
| P8 | main-transition parameters (:403-441): genesis case → `ChunkExtra` of the genesis chunk; else `NewChunkData { gas_limit, prev_state_root, prev_validator_proposals, chunk_hash` of the last new chunk's header, `transactions` + P7 flags, `receipts_to_apply`, block context `get_apply_chunk_block_context(last_chunk_block, header(last_chunk_block.prev_hash), true)`, storage = `Recorded(main_state_transition.base_state)` } | | witness + **chain** |

## 4. The backward walk (`get_state_witness_block_range`, `chunk_validation.rs:144-253`)

Start: `prev_block = block(chunk_header.prev_block_hash)`; shard id = the header's
`shard_id`, which must exist in `get_shard_layout_from_prev_block(prev)` (:169-176).
Loop over `position.prev_block` = X (newest first):

1. `epoch_id = get_epoch_id_from_prev_block(X.hash)`; `shard_uid` (:187-190).
2. Resharding check (only before the first new chunk is seen): `get_resharding_transition` (:255-305) yields `ImplicitTransitionParams::Resharding` iff the block after X starts an epoch whose layout differs from the previous epoch's and this shard is a child of the split.
3. `(prev_layout, prev_shard_id, prev_shard_index) = get_prev_shard_id_from_prev_hash(X.hash, shard_id)` (:200-201; `chain/epoch-manager/src/adapter.rs:271-289`: identity unless the block after X starts an epoch with a new layout).
4. `new_chunk_seen = (X.chunks[prev_shard_index].height_included == X.height)` (:128-139, :203).
5. Count 0 → X is a block **without** a new chunk for the shard: push `ApplyOldChunk(get_apply_chunk_block_context(X, header(X.prev_hash), false), shard_uid)` (:210-216). Count 1 → X is `last_chunk_block` or a block before it after the last-last chunk: push to `blocks_after_last_last_chunk` (:219). Count 2 → stop (:221).
6. Stop also if X is genesis (:225-227); otherwise step to `X.prev` (:229-243).

Result: implicit transitions in **forward** order (:246); `blocks_after_last_last_chunk` newest first, whose first element is `last_chunk_block` (the block that included the last new chunk, B2); the walk also *reads* the block B1 containing the last-last new chunk (to see its chunk mask) and one header before each visited block.

Every read here is of blocks hash-linked from `prev_block_hash`, plus epoch-manager answers keyed by block hash.

## 5. Source receipt proofs (`validate_source_receipt_proofs`, `chunk_validation.rs:449-527`)

* Genesis among the source blocks ⇒ it must be the only block and the proof map must be empty; receipts `[]` (:456-469).
* For each source block S (newest first), for each **new** chunk C of S in shard-index order (`iter_new`, `block.rs:762-764`):
  look up `source_receipt_proofs[C.chunk_hash]` (missing ⇒ error), then `validate_receipt_proof` (:529-563):
  `from_shard_id == C.shard_id`, `to_shard_id == current_target_shard_id`,
  `verify_path(C.prev_outgoing_receipts_root, path, SHA256(u64 to_shard_id ‖ borsh(Vec<Receipt>)))`
  (`sharding.rs:980-987, 1225-1226`; `merkle.rs:113-144`: `Left ⇒ SHA256(h ‖ acc)`, `Right ⇒ SHA256(acc ‖ h)`, no
  length/index constraint). Leaf hashing therefore applies SHA-256 twice.
* `filter_incoming_receipts_for_shard(target_layout, target_shard, proofs)` keeps only receipts routed to the target shard under the **final** layout; it never drops a proof (`chain/chain/src/store/mod.rs:252-273`). No-op without resharding.
* `shuffle_receipt_proofs(proofs, S.prev_hash)` (`chain/chain/src/sharding.rs:9-21`): `ChaCha20Rng::from_seed(S.prev_hash)` (rand_chacha 0.3.1: 20 rounds, 64-bit counter from 0, zero nonce), then rand 0.8.5 `SliceRandom::shuffle`: `for i in (1..len).rev() { swap(i, gen_range(0..i+1 as u32)) }` with Lemire widening-multiply rejection on `next_u32` (rand-0.8.5 `src/seq/mod.rs:586-592, 659-665`, `src/distributions/uniform.rs:507-554`). Re-implemented in Python and checked against nearcore's test vector (`sharding.rs:29-33`).
* Append each proof's receipts in shuffled order; `current_target_shard_id = get_prev_shard_id_from_prev_hash(S.prev_hash, ·).1`.
* Finally `source_receipt_proofs.len() == number of new chunks visited` (:518-525) (after duplicate-key collapse).

The receipts themselves come **only** from the witness; they are authenticated by the
`prev_outgoing_receipts_root` of chunk headers in the chain (context).

## 6. The main transition (`validate_chunk_state_witness_impl`, `chunk_validation.rs:565-631`)

`apply_new_chunk` (`chain/chain/src/update_shard.rs:123-187`) → `NightshadeRuntime::apply_chunk`
(`chain/chain/src/runtime/mod.rs:1201-1280`) → `process_state_update` (`runtime/mod.rs:198-432`) → `Runtime::apply`
(`runtime/runtime/src/lib.rs:1717-1819`; internals in `docs/research/nearcore-boundary.md` §1-§6).

**Block context** (`chain/chain/src/chain.rs:2896-2935`; `chain/chain/src/types.rs:365-394`) for block B (B2 for the main
transition, M for an implicit one), from B's header and **all** of B's chunk slots:

| `ApplyState` field | value |
|---|---|
| `block_height`, `prev_block_hash`, `block_timestamp`, `random_seed` | `B.height`, `B.prev_hash`, `B.raw_timestamp`, `B.random_value` |
| `gas_price` | new chunk: `header(B.prev_hash).next_gas_price`; old chunk: `B.next_gas_price` (legacy, `chain.rs:2902-2911`) |
| `congestion_info` | `BTreeMap<ShardId, ExtendedCongestionInfo>` over **every** slot of B: `(slot.congestion_info, missed = B.height − slot.height_included)` (`block.rs:770-788`) |
| `bandwidth_requests` | every slot's `bandwidth_requests`, missing chunks included (`block.rs:790-804`) |
| `epoch_id`, `epoch_height`, `shard_id`, `current_protocol_version`, `config` | epoch manager: `get_epoch_id_from_prev_block(B.prev_hash)` etc. (`runtime/mod.rs:228-283`); `config = runtime_config_store.get_config(pv)` (PV 86 uses the PV 85 file) |
| `gas_limit` | last new chunk's `gas_limit` (`update_shard.rs:159-172`) |
| `is_new_chunk` | true (main) / false (implicit) |

**Trusted epoch inputs inside `process_state_update`** (`runtime/mod.rs:228-342, 583-622`):
`ValidatorAccountsUpdate` iff `is_next_block_epoch_start(B.prev_hash)` (stake returns and rewards from
`compute_stake_return_info`, `chain/epoch-manager/src/lib.rs:1269-1309`; protocol treasury from genesis);
`proposed_split` via `compute_proposed_split` (DynamicResharding, mainnet `epoch_configs/mainnet/85.json`
`dynamic_resharding_config`) which runs only if `is_next_block_possibly_last_in_epoch(B.height, B.prev_hash)` and
`can_reshard` hold, and then reads the trie root's `memory_usage` and possibly `find_trie_split`
(`runtime/mod.rs:1731-1767`, `core/store/src/trie/split.rs`). Inside `Runtime::apply` the
`EpochInfoProvider` supplies `shard_layout(epoch)` (bandwidth scheduler, congestion control, receipt routing),
`chain_id()`, `minimum_stake(prev)` (stake actions) and validator stakes (contract host functions).

**Recording limit.** Validation re-runs with `recording_reads_with_proof_size_limit(main_storage_proof_size_soft_limit = 4 000 000)`
(`runtime/mod.rs:1258`), so the delayed-receipt decisions driven by the proof-size estimate are reproduced exactly.
Storage errors other than missing trie values panic (`runtime/mod.rs:1270-1279`); a receipt that fails
`validate_receipt` panics (`runtime/mod.rs:362-367`) — a panicking validator never endorses.

**`ChunkExtra`** (`ApplyChunkResult::to_chunk_extra`, `types.rs:166`, `ChunkExtra::new` `types.rs:922`; sums at `runtime/mod.rs:372-403`):

| field | value |
|---|---|
| `state_root` | `ApplyResult.state_root` |
| `outcome_root` | `merklize([o.to_hashes() for o in outcomes])` |
| `validator_proposals` | deduped proposals of the chunk |
| `gas_used` | Σ `outcome.gas_burnt` |
| `gas_limit` | the last new chunk's `gas_limit` |
| `balance_burnt` | `tx_burnt + other_burnt + slashed_burnt − subsidized` (checked) |
| `congestion_info` | own congestion info after `finalize_allowed_shard` (§9.4) |
| `bandwidth_requests` | generated from the outgoing buffers (§9.5) |
| `proposed_split` | as above |

Early check (`chunk_validation.rs:622-631`): `chunk_extra.state_root == main_state_transition.post_state_root`,
otherwise **Err** (the comment says it is for diagnostics, but it is a rejection).

## 7. Implicit transitions (`chunk_validation.rs:662-750`)

* `implicit_transition_params.len() == witness.implicit_transitions.len()` (:662-670).
* `ApplyOldChunk(M, shard_uid)` (:678-701): `apply_old_chunk` (`update_shard.rs:190-235`) with `state_root =
  chunk_extra.state_root`, `last_validator_proposals = chunk_extra.validator_proposals`, `gas_limit =
  chunk_extra.gas_limit`, no receipts or transactions, storage = `transition.base_state`. In `Runtime::apply`
  a missing chunk runs: validator-account update (if `M` starts an epoch), the delayed-queue *load*, the
  **bandwidth scheduler** (writes key `0x0f`, `lib.rs:1767`), then returns `missing_chunk_apply_result`
  (`lib.rs:1773-1779, 2937-2984`). Only `new_root` is kept; congestion info stays the main transition's (:699);
  all other `ChunkExtra` fields are untouched (:736-737).
* `Resharding(boundary, mode, child)` (:702-733): `retain_split_shard` on the parent trie and
  `ReshardingManager::get_child_congestion_info`.
* After each: `chunk_extra.state_root == transition.post_state_root` or **Err** (:738-749).

## 8. Final comparison against the endorsed header

`validate_chunk_with_chunk_extra_and_receipts_root(&chunk_extra, header, &outgoing_receipts_root)` (`validate.rs:133-188`), with
`outgoing_receipts_root = merklize(build_receipts_hashes(outgoing_receipts, witness_shard_layout))`
(`chunk_validation.rs:633-646, 754`; `chain/chain/src/chain.rs:4102-4130`: one leaf per shard of the layout in index order,
`SHA256(borsh((shard_id u64, Vec<Receipt>)))` with receipts routed by `receiver_shard_id` = `account_id_to_shard_id`
(`partition_point(|b| b <= id)` over boundary accounts, `shard_layout/v2.rs:265-268`), then hashed again by `merklize`):

| header field | must equal | error |
|---|---|---|
| `prev_state_root` | `chunk_extra.state_root` (after implicit transitions) | `InvalidStateRoot` |
| `prev_outcome_root` | `chunk_extra.outcome_root` | `InvalidOutcomesProof` |
| `prev_validator_proposals` | `chunk_extra.validator_proposals` (length and elementwise) | `InvalidValidatorProposals` |
| `gas_limit` | `chunk_extra.gas_limit` (= the last new chunk's gas limit) | `InvalidGasLimit` |
| `prev_gas_used` | `chunk_extra.gas_used` | `InvalidGasUsed` |
| `prev_balance_burnt` | `chunk_extra.balance_burnt` | `InvalidBalanceBurnt` |
| `prev_outgoing_receipts_root` | `outgoing_receipts_root` | `InvalidReceiptsProof` |
| `congestion_info` | all 4 fields incl. `allowed_shard` (`congestion_info.rs:204-213`) | `validate_congestion_info` |
| `bandwidth_requests` | `Option` equality (`validate.rs:280`) | `validate_bandwidth_requests` |
| `proposed_split` | `chunk_extra.proposed_split` (`validate.rs:176`) | `InvalidChunkHeaderShardSplit` |
| `tx_root` | `merklize(new_transactions).root` (`chunk_validation.rs:763-766`) | `InvalidTxRoot` |
| `encoded_merkle_root`, `encoded_length` | Reed–Solomon of `TransactionReceipt(new_transactions, outgoing_receipts)` (§8.1) | `InvalidChunkEncoded*` |

### 8.1 Encoded merkle root (`validate.rs:233-260`; `core/primitives/src/reed_solomon.rs:18-78`)

`bytes = borsh((Vec<SignedTransaction> new_transactions, Vec<Receipt> outgoing_receipts))`; `encoded_length = |bytes|`;
`L = ceil(|bytes| / d)`; zero-pad to `d·L`; data part `k` = `bytes[kL, (k+1)L)`; parity parts from
reed-solomon-erasure 6.0.0 `galois_8`: `M = V · (V[0..d])⁻¹` with `V[r][c] = r^c` over GF(2⁸) (`0⁰ = 1`, polynomial
`0x11D`, generator 2) (`src/core.rs:430-509, 872-882`; `src/matrix.rs:263-276`; `build.rs:11-39`);
`encoded_merkle_root = merklize(parts)` with leaf `SHA256(u32le(L) ‖ part)` (`sharding.rs:1218-1222`).
`d = num_data_parts`, `p = num_total_parts − d`, where `num_total_parts = max(2, num_block_producer_seats at the
genesis protocol version)` and `num_data_parts = 1 if total ≤ 3 else (total − 1)/3`
(`chain/epoch-manager/src/adapter.rs:63-70, 855-863`; ReedSolomon built at `chunk_validation_actor.rs:100-102, 136-138`).
Mainnet: 100 seats ⇒ `d = 33`, `p = 67` (`core/primitives/res/epoch_configs/mainnet/29.json:3`). With `total ≤ 3`
(`d = 1`) every parity part equals the single data part.

---

## 9. Multi-shard: bandwidth scheduler and congestion control

### 9.1 What every chunk application reads from other shards

All of it comes from the **chunk slots of the block being applied** (B2 or M), via `ApplyState`:

* `congestion_info[s]` and `missed_chunks_count[s]` for every shard `s` (block.rs:770-788);
* `bandwidth_requests[s]` for every shard (block.rs:790-804);
* the shard layout of the epoch; `prev_block_hash` (scheduler RNG seed).

Nothing about another shard's *state* is read. These values are authenticated by the block hash (chunk slots via
`chunk_headers_root`, §2.4), so in the v3 claim they are **context authenticated by hashes**, and the scheduler and
congestion computations on them are **inside the relation**.

### 9.2 The scheduler (`runtime/runtime/src/bandwidth_scheduler/{mod.rs:44-141, scheduler.rs:200-562, distribute_remaining.rs:22-87}`)

1. Load state `0x0f` (default `V1{[], 0^32}`); shard statuses per entry of `congestion_info` (BTreeMap order): `last_chunk_missing = missed > 0`, `allowed_sender_shard_index = index(allowed_shard)`, `is_fully_congested = congestion_level == 1.0` (mod.rs:59-93).
2. `params`: `base = min((max_shard_bandwidth − max_single_grant) / max(1, n−1), max_base_bandwidth)` (integer; `core/primitives/src/bandwidth_scheduler.rs:304-352`); PV 86: 4 500 000 / 4 194 304 / 4 500 000 / 100 000 (`runtime_configs/74.yaml:2-5`); request values `values[i] = base + (max_single_grant − base)·(i+1)/40` (`bandwidth_scheduler.rs:145-167`).
3. Allowances of the previous state mapped to shard indexes; unknown shards dropped (scheduler.rs:214-229).
4. `is_link_allowed(s, r)`: false if `r` unknown, `r` missed its last chunk, or `s` known and missed its last chunk; if `r` fully congested, only `s == allowed_sender(r)`; else true (scheduler.rs:506-546).
5. Requests: per sender (BTreeMap by ShardId), per request: increases from the bitmap over `base` (scheduler.rs:254-276, 599-642).
6. `increase_allowances`: every link, `a = min(a ⊕ max_shard_bandwidth/n, max_allowance)`; `grant_base_bandwidth`: `try_grant(link, base)` on every link in sender-major order (`try_grant` requires the link allowed and both budgets; subtracts budgets and allowance) (scheduler.rs:323-345, 467-497).
7. `process_bandwidth_requests`: buckets keyed by allowance, highest first; each bucket **shuffled** with `ChaCha20Rng::from_seed(prev_block_hash)` (one RNG for the whole run, mod.rs:115, scheduler.rs:291); grant the next increase or drop the request (scheduler.rs:347-388).
8. `distribute_remaining_bandwidth` (no allowance change) (distribute_remaining.rs:22-87).
9. Write `link_allowances` for every link (sender-major) and `sanity_check_hash = SHA256(prev ‖ SHA256(borsh(all_shard_ids)))` (scheduler.rs:548-562; mod.rs:120-137).

The grants of links `(own, *)` bound the bytes this chunk may forward to each shard (including itself) in
`ReceiptSink` (`runtime/runtime/src/congestion_control.rs:86-142, 403-468`); the rest of the schedule only
influences state through the stored allowances and hash.

### 9.3 Floating point: exact inventory and modelling decision

Consensus-relevant floats exist **only** in `core/primitives/src/congestion_info.rs`; the scheduler itself,
its parameters, request values and request generation are integer:

| id | location | computation | reached by |
|---|---|---|---|
| F1 | `clamped_f64_fraction` :474-477 | `if max ≤ v {1.0} else {(v as f64) / (max as f64)}` | F2–F5 |
| F2–F4 | :331-345 | F1 of `delayed_receipts_gas` / 4·10¹⁷, `buffered_receipts_gas` / 10¹⁶, `receipt_bytes` / 10⁹ | `congestion_level` |
| F5 | :68-77 | `0.0` if `missed ≤ 1` else F1(missed, 125) | `congestion_level` |
| F6 | :44-54 | `f64::max` of F2–F5 | F7, F8 |
| F7 | :95-100 | `level == 1.0` (`is_fully_congested`) | scheduler link status; red light in `outgoing_gas_limit` |
| F8 | `mix` :484-502 | `round(left·(1.0 − r) + right·r) as u64` (`left = max_outgoing_gas` 3·10¹⁷, `right = min_outgoing_gas` 10¹⁵) | `outgoing_gas_limit` (:80-93) → `ReceiptSink` forward-or-buffer |

Only `as` conversions of integers, `/`, `*`, `−`, `+`, `max`, `==` and `round` (half away from zero) occur — no
transcendental functions, no NaN (max > 0 asserted), no FMA contraction in Rust — so every result is fixed by IEEE 754
binary64 round-to-nearest-even. Non-consensus floats (transaction admission `reject_tx_congestion_threshold`,
metrics) are listed in the research notes but are not reached by `Runtime::apply` during validation.

**Decision.** Model binary64 *exactly* rather than bounding it away:

* A non-negative finite double is `m · 2^e` with `m < 2^53`; `toF64(q)` for a non-negative rational `q` is
  round-to-nearest-even onto that grid (all values here are normal or zero; no overflow is reachable: inputs
  ≤ 2¹²⁸). Each Rust operation is "compute the exact rational result, then `toF64`"; `round` and `as u64` are exact
  integer functions of a double. This is IEEE 754 §4.3/§5 by definition, so the Lean model is a transcription,
  not an approximation.
* F7 reduces to an **integer** predicate: for `0 < a, b` doubles `a / b` rounds to `1.0` iff `a = b` (if `a < b` then
  `a ≤ b − ulp⁻(b)` and `1 − a/b ≥ 2⁻⁵³`, more than the half-ulp `2⁻⁵⁴` below 1). So F1 = 1.0 iff
  `v ≥ max` or `toF64(v) = toF64(max)`, i.e. `v` lies within the rounding interval of `max` — e.g. for
  `max = 4·10¹⁷` (ulp 64) every `v ≥ 4·10¹⁷ − 32` counts as fully congested even though `v < max`.
  The scheduler therefore needs **no** float arithmetic beyond `toF64` on integers.
* F8 is needed only to compute `outgoing_gas_limit`; it is modelled with the same exact `toF64`.

### 9.4 Own congestion info after a new chunk (`lib.rs:2723-2869`)

Starts from the shard's own slot in B's `congestion_info` (header value of the previous chunk's result), adjusted by
delayed-queue and outgoing-buffer changes; then
`allowed_shard = all_shards[(B.height + shard_index(own)) mod n]` (wrapping add; layout order) — always set,
congested or not (`lib.rs:2760-2772`, `congestion_info.rs:360-384`).

### 9.5 Bandwidth requests generated (`congestion_control.rs:503-607`)

Per target shard in layout order, from the outgoing-buffer receipt-group metadata; an empty buffer yields no request;
`BandwidthRequests::V1` with the (possibly empty) list is stored in `ChunkExtra` and compared with the header.

---

## 10. Classification: chain context vs witness

This is the table the v3 claim is built from. *Authenticated* = fixed by a hash the validator already trusts
(ultimately `chunk_header.prev_block_hash` being a block in its store); *trusted* = an answer of the validator's
epoch manager / store / genesis config that is not a function of hashes the claim can carry.

| input used by validation | where it comes from | class |
|---|---|---|
| endorsed chunk header inner (all fields) | the chunk being endorsed | **claim** (the statement) |
| `epoch_id` (witness field, endorsement metadata) | `get_epoch_id_from_prev_block(prev)` | **claim**, trusted |
| protocol version of the epoch(s), runtime config | epoch manager; pinned `RuntimeConfigStore` | **claim** (pv), pinned constants |
| `chain_id` | genesis config via `EpochInfoProvider` | **claim**, trusted |
| prev block and every block of the backward walk: header (`prev_hash, height, timestamp, random_value, next_gas_price, epoch ids …`) | chain store | **claim**, authenticated by the hash chain from `prev_block_hash` |
| chunk slots of those blocks: `(inner, height_included)` (new-chunk test, `tx_root`, `gas_limit`, `prev_state_root`, proposals, `prev_outgoing_receipts_root`, congestion infos, bandwidth requests of **all** shards) | chain store | **claim**, authenticated by each block's `chunk_headers_root` |
| shard layout per epoch; `is_next_block_epoch_start`; parent-shard map; resharding events | epoch manager | **claim**, trusted |
| `ValidatorAccountsUpdate` (stake returns, rewards, last proposals, treasury) at epoch starts | epoch manager / genesis | **claim**, trusted |
| `proposed_split` gate: dynamic-resharding config, `is_next_block_possibly_last_in_epoch`, `can_reshard` | epoch manager | **claim**, trusted |
| `minimum_stake(prev)`, validator stakes (contract host functions) | epoch manager | **claim**, trusted |
| tx validity-period flags for `transactions` | chain store + genesis `transaction_validity_period` | **claim**, trusted |
| genesis `ChunkExtra` (only when the last new chunk is the genesis chunk) | chain store | **claim**, trusted |
| Reed–Solomon `(d, p)` | genesis epoch config | **claim**, trusted |
| pre-state trie nodes (main + each implicit transition) | `base_state` | **witness** (hash-linked to `prev_state_root` / the running root) |
| incoming receipts | `source_receipt_proofs` | **witness** (authenticated by `prev_outgoing_receipts_root` of context chunk slots) |
| `transactions` (last new chunk) | witness | **witness** (authenticated by context `tx_root`) |
| `new_transactions` | witness | **witness** (authenticated by the claim's `tx_root`) |
| `applied_receipts_hash`, transition `post_state_root`s | witness | **witness** (checked; redundant) |
| contract code | `ChunkContractAccesses` responses, merged into `base_state` | **witness** (hash-linked through `code_hash`) |
| everything computed: receipt order (shuffle), scheduler, congestion, runtime semantics, outcome/receipt/RS roots | — | **inside the relation** |

## 11. Reuse for a future AIR (zk-formal L5/L6)

Everything the relation hashes is SHA-256 over byte strings (block hash, chunk hash, merkle trees, receipt-proof
leaves, trie nodes, RS-part leaves): the L5 SHA bus contract (`sha_bus_sound`) covers it unchanged. The trie walks,
`PTrie.upsert` (bandwidth state write), account codec and Transfer semantics are exactly the NEAR v1/v2 machinery that
L6 arithmetizes. New AIR components a chunk-validation AIR would need: borsh parsing of headers/witness (variable
length), ChaCha20 (32-bit ARX), GF(2⁸) RS encoding (table lookups), and the exact-f64 integer predicate (§9.3).

## 12. Unverified / open items

* Whether mainnet has performed a dynamic split at PV 86 (layout V3) — irrelevant to the statement, relevant to which mainnet chunks are in a domain.
* Mainnet `transaction_validity_period` (believed 86 400) — only enters through the trusted flags.
* zstd multi-frame behaviour (transport only).
* `TriePrefetcher` on recorded storage (performance only).
