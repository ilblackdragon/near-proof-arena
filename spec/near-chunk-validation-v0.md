# `near/pv86/chunk-validation/v0` — NEAR stateless chunk validation as an arena statement

Claim/witness formats: `spec/claim-v3.md` (`near-arena-claim-v3`,
`near-arena-witness-v3`). Source map with citations:
`docs/research/chunk-validation-boundary.md` (cited below as **[B §n]**).
Pinned nearcore `2.13.4` = `44f7ae6cd7ef08bab604e20a473bf77e35d4c993`,
protocol version **86**, runtime parameters
`RuntimeConfigStore::new(None).get_config(86)`.

## 0. What changed and why

The v1/v2 statements (`spec/near-transfer-receipt-v1.md`, `-v2.md`) prove a
*slice* of `Runtime::apply` in a custom claim format, with a single-shard
restriction in v2. A proof of such a claim cannot replace anything a NEAR node
does: no node ever asks "is this receipt batch's projected root X?".

v3 states **exactly what a chunk validator establishes before it signs a
`ChunkEndorsement`**:

> **Rel(c, w)** ⇔ nearcore 2.13.4's chunk validator, whose chain store and
> epoch manager answer as recorded in `c`, accepts the `ChunkStateWitness` in
> `w` for the chunk header in `c` — i.e. `pre_validate_chunk_state_witness`
> and `validate_chunk_state_witness` both return `Ok`, after the actor-level
> checks (`epoch_id`, `prev_block_hash`) pass.

The endorsement signs `chunk_hash` (a function of `c.chunk_inner`) and
`epoch_id` [B §1]. So a party holding a valid proof for `c` may sign the
endorsement that a validator re-executing the witness would sign — the proof is
a **drop-in replacement for re-execution**, provided the party built `c` from
its own chain state (§4).

Subsets are **domain restrictions**: `Rel_Dk := Rel ∧ InDk` with the same
claim and witness formats (§6). A `Dk` prover validates the chunks in `Dk`
and refuses (cannot prove) the others; a node can run a `Dk` prover and fall
back to re-execution outside `Dk`.

## 1. Parties and trust

| input | role | how the consumer obtains / checks it |
|---|---|---|
| `c.chunk_inner` | the chunk to endorse | it is the header it was asked to endorse |
| `c.epoch_id`, `c.protocol_version`, `c.chain_id`, section C | trusted chain/epoch facts | its own epoch manager, store, genesis config |
| `c` section B (block headers, chunk slots) | chain context | authenticated inside `Rel` by hashes back to `chunk_inner.prev_block_hash`; the consumer checks only that this block is in its store (the validator's own precondition, [B §1]) |
| `w` | the `ChunkStateWitness` (+ contract code) | private; never trusted — every byte is checked by `Rel` |

`Rel` never consults anything outside `(c, w)`. Every place where nearcore
asks its store or epoch manager is answered from `c`, and every answer that is
hash-derivable is checked against hashes rather than trusted.

## 2. Constants

Runtime config: pinned (as v2, plus congestion-control constants), committed by
`runtime_config_digest_v3` (`spec/claim-v3.md` §4). Consensus constants used
outside `Runtime::apply`: `MAX_UNCOMPRESSED_STATE_WITNESS_SIZE` = 64 MiB,
`max_transaction_size` = 1 572 864, `main_storage_proof_size_soft_limit` =
4 000 000, bandwidth-scheduler and congestion parameters [B §9].

## 3. The relation `Rel(c, w)`

Each step names the nearcore code it transcribes. A step "fails" where nearcore
returns `Err` **or panics** (a panicking validator never endorses).

### 3.1 Decoding and actor-level checks

1. `w` decodes (`spec/claim-v3.md` §3); `|state_witness| ≤ 64 MiB`; `state_witness` decodes as nearcore borsh `ChunkStateWitness::V2` with no trailing bytes [B §2.2]; contract code blobs are appended to `main_state_transition.base_state` as `TrieValues` (`partial_witness_tracker.rs:692-696`).
2. `borsh(W.chunk_header.inner) = c.chunk_inner` (byte equality of the tagged inner). `W.chunk_header.height_included` and `.signature` are unconstrained (nearcore never checks them) [B §1].
3. `W.epoch_id = c.epoch_id` (`chunk_validation_actor.rs:384-391`).
4. `c` is well-formed (hash discipline of `spec/claim-v3.md` §2.1; epoch table covers exactly the referenced epochs; `protocol_version = epochs[epoch_id].protocol_version`).

### 3.2 Chain context derived from `c` (the backward walk, `chunk_validation.rs:144-253`)

Let `H = c.chunk_inner`, `s₀ = H.shard_id`, `blk[0..n)` = section B, `L(e)` = shard layout of epoch `e`.

* `s₀` is a shard of `L(c.epoch_id)` (:173-176).
* For the block *after* `blk[i]` the epoch is `c.epoch_id` for `i = 0` and `blk[i-1].epoch_id` otherwise (`get_epoch_id_from_prev_block`, `chain/epoch-manager/src/adapter.rs:170-179`); whether it starts an epoch is `c.epoch_start_after[i]`, checked for consistency with those epoch ids (`spec/claim-v3.md` §2.2).
* `prev_shard(i, s)` = parent of `s` if the block after `blk[i]` starts an epoch whose layout differs from `L(blk[i].epoch_id)`, else `s` (`adapter.rs:271-289`); resharding transitions per `get_resharding_transition` (:255-305).
* Walk `i = 0, 1, …` with `seen = 0`: `new(i) := blk[i].slots[index(shard_i)].height_included = blk[i].height`; `seen=0 ∧ ¬new(i)` ⇒ `blk[i]` is an **implicit block**; `new(i)` with `seen` becoming 1 ⇒ `blk[i]` is **B2** (`last_chunk_block`); `seen = 1` ⇒ source block; `seen` becoming 2 ⇒ stop (`blk[i]` = B1); a genesis block (`prev_hash = 0`) also stops.
* Required: `n_blocks` = index of the stop block + 1 (the segment is exactly what the walk reads).
* `apply_facts` has one entry per applied block (B2, then the implicit blocks oldest first); `validator_update` is `Some` iff that block starts an epoch.

### 3.3 Pre-validation (`chunk_validation.rs:310-444`)

5. `validate_version(H, protocol_version)`: V3 with inner V4, or inner V5 (DynamicResharding ≤ 86) [B §2.1].
6. Every `W.new_transactions[i]` passes `check_valid_for_config` [B §3 P2].
7. Source receipts (§3.4) → `R`; `SHA256(borsh(Vec R)) = W.applied_receipts_hash`.
8. `merklize(W.transactions).root = B2.slots[idx].tx_root`.
9. `|c.tx_valid| = |W.transactions|`.
10. Main-transition parameters: if B2 is genesis, `c.genesis_chunk_extra` is `Some` and is the `ChunkExtra`; else `NewChunkData` from B2's slot for the shard (`gas_limit`, `prev_state_root`, `prev_validator_proposals`), `W.transactions` with `c.tx_valid`, `R`, block context `ctx(B2, prev(B2), new=true)` (§3.5).

### 3.4 Source receipt proofs (`chunk_validation.rs:449-527`)

For each source block `S` (newest first), each new chunk `C` of `S` in shard-index order: the proof `W.source_receipt_proofs[chunk_hash(C)]` exists, `from_shard_id = C.shard_id`, `to_shard_id` = current target shard, and `verify_path(C.prev_outgoing_receipts_root, path, SHA256(u64 to_shard ‖ borsh(Vec<Receipt>)))`; then filter by the final layout, `shuffle_receipt_proofs(·, S.prev_hash)` (ChaCha20 + rand 0.8.5 Fisher–Yates, exact algorithm [B §5]), append. Finally `|map| = #proofs visited` (after duplicate-key collapse). Genesis source block ⇒ only block, empty map, `R = []`.

### 3.5 Main transition

`ctx(X, P, new)` = `ApplyState` for block X with parent header P [B §6 table]:
height/prev_hash/timestamp/random_seed of X; `gas_price = new ? P.next_gas_price : X.next_gas_price`;
`congestion_info[s] = (slot_s.congestion_info, X.height − slot_s.height_included)` and
`bandwidth_requests[s] = slot_s.bandwidth_requests` over **all** slots of X; epoch fields from `c.epochs`;
`ValidatorAccountsUpdate` from `apply_facts` (filtered to the shard as `process_state_update` does);
`proposed_split` = `None` if the split gate is closed, else nearcore's `check_dynamic_resharding` on the pre-state trie.

11. `(ChunkExtra E, outgoing O) := apply(ctx(B2, prev(B2), true), base_state = W.main_state_transition.base_state, root = B2-slot.prev_state_root, R, W.transactions, c.tx_valid)` — the semantics of `NightshadeRuntime::apply_chunk` + `Runtime::apply` with recorded storage and the 4 MB proof-size recording limit [B §6]; any `Err`/panic fails. A trie lookup that the witness does not determine fails (nearcore: `MissingTrieValue` → `Err`).
12. `E.state_root = W.main_state_transition.post_state_root` (:622-631).

### 3.6 Implicit transitions (`chunk_validation.rs:662-750`)

13. `|W.implicit_transitions|` = number of implicit blocks (+ resharding transitions).
14. For each implicit block M (oldest first) with its transition `T`: `E.state_root := new_root of apply(ctx(M, prev(M), false), base = T.base_state, root = E.state_root, [], [])` (a missing-chunk apply: validator update if M starts an epoch, bandwidth scheduler, nothing else [B §7]); `E.congestion_info` unchanged; `E.state_root = T.post_state_root`. Resharding transitions per [B §7].

### 3.7 Comparison with the endorsed header (`validate.rs:133-188`, `chunk_validation.rs:751-778`)

15. `H.prev_state_root = E.state_root`, `H.prev_outcome_root = E.outcome_root`, `H.prev_validator_proposals = E.validator_proposals`, `H.gas_limit = E.gas_limit`, `H.prev_gas_used = E.gas_used`, `H.prev_balance_burnt = E.balance_burnt`, `H.congestion_info = E.congestion_info` (all four fields), `H.bandwidth_requests = E.bandwidth_requests`, `H.proposed_split = E.proposed_split`.
16. `H.prev_outgoing_receipts_root = merklize(build_receipts_hashes(O, L(c.epoch_id))).root` (after resharding reassignment if layouts differ).
17. `H.tx_root = merklize(W.new_transactions).root`.
18. `(parts, len) = RS_{c.rs_data_parts, c.rs_total_parts − c.rs_data_parts}(borsh((W.new_transactions, O)))`: `H.encoded_merkle_root = merklize(parts).root` and `H.encoded_length = len` [B §8.1].

`Rel(c, w)` holds iff steps 1–18 succeed.

## 4. Drop-in correctness criterion

Let a node in chain state Σ (store + epoch manager + genesis) receive witness
`W` for chunk header `H` with `H.prev_block_hash` in its store. Let
`claimOf(Σ, H)` be the claim built from Σ (the oracle command
`near-arena-oracle claim --scope v3` is the reference builder). The statement
is designed so that

> **(DI)** `Rel(claimOf(Σ, H), (W, codes))` ⇔ the node's
> `ChunkValidationActor` (witness path) sends an endorsement for `H`.

(DI) is the property tested by the v3 oracle (§7): nearcore's own
`pre_validate_chunk_state_witness` + `validate_chunk_state_witness` are the
reference judge, and every implementation of `Rel` (Lean, Python) must agree
with them on every generated case, positive and negative.

**Explicitly not part of `Rel`** (also not established by the validator):
the chunk producer's signatures (chunk header, partial-witness parts),
witness delivery and Reed–Solomon *decoding* of witness parts, chunk
finality/data availability of anything, validator assignment ("am I a
validator for this chunk"), orphan handling, the shortcut path's database
contents (§1 of [B]; it decides the same predicate on a correct database).

**Consumer obligations.** A consumer must build `claim.bin` itself from its
own Σ (never accept a claim built by someone else): section C and `epoch_id`
are *trusted* values that `Rel` cannot check (some are unused in a given
domain, e.g. `minimum_stake` in D0, but must still be the true values for (DI)).

## 5. Floating point

Exactly as decided in [B §9.3]: binary64 is modelled exactly (exact rational
result, round-to-nearest-even onto the 53-bit grid; `round` half away from
zero; saturating `as u64`). Only `congestion_info.rs` F1–F8 use floats. For
the scheduler, `is_fully_congested` reduces to the integer predicate
`v ≥ max ∨ toF64(v) = toF64(max)` (proof sketch in [B §9.3]); `mix` (outgoing
gas limit) is evaluated with the exact model. No approximation is introduced.

## 6. Domain ladder

`InDk(c, w)` is defined on (a) claim fields and (b) witness content that is
determined by the chain under SHA-256 collision resistance (the applied
receipts `R`, `W.transactions`, `W.new_transactions`, the pre-state trie under
the root) plus (c) the execution trace of `Rel`. So membership is a property
of the *chunk*, not of how the witness happens to be encoded.

`Rel_Dk := Rel ∧ InDk`; `D0 ⊂ D1 ⊂ D2 ⊂ D3 ⊂ D∞ = Rel`.

### D0 — Transfer receipts, multi-shard, no transactions

Claim-level (decidable from `c` alone):

| id | condition | reason |
|---|---|---|
| `c.pv86` | `protocol_version = 86` | pinned config |
| `c.single_epoch` | every header in B has `epoch_id = c.epoch_id`; `epochs` has one entry; `epoch_start_after` all 0 | no validator updates, no resharding, one layout |
| `c.layout` | `L(epoch_id)` is ShardLayout V2 or V3, `1 ≤ shards ≤ 64` | routing by boundary accounts |
| `c.headers` | block headers V6; chunk inners V4/V5 | PV 86 formats |
| `c.no_split_gate` | every `apply_facts[i].split_gate = None`, `validator_update = None` | no trie-split search |
| `c.not_genesis` | B2 is not the genesis block (`genesis_chunk_extra = None`) | genesis `ChunkExtra` path |
| `c.no_tx_flags` | `tx_valid = []` | no transactions |
| `c.segment` | `n_blocks ≤ 32` | size bound |
| `c.own_congestion_zero` | the shard's congestion info in B2's slot has `delayed_receipts_gas = buffered_receipts_gas = receipt_bytes = 0` | equivalent (on a real chain) to: own delayed queue and outgoing buffers empty before the chunk |
| `c.gas_limit` (A1) | the `gas_limit` of B2's own-shard slot is `≤ 10^15` (1000 Tgas, mainnet genesis) | bounds the applied receipts (`n ≤ 4481`) for a succinct proof; nearcore copies the genesis gas limit into every chunk forever (`chunk_producer.rs:393`, `validate.rs:154`, `chain_update.rs:472,519`, `update_shard.rs:224`; V3-D0-DESIGN §10.1), so a real chain is either wholly in or wholly out |

Witness/execution-level:

| id | condition | reason |
|---|---|---|
| `w.no_txs` | `W.transactions = []`, `W.new_transactions = []` | no tx verification, no local receipts |
| `w.no_code` | contract code list empty | no WASM |
| `w.size` | `|state_witness| ≤ 8 MiB`; revealed `base_state` bytes of the main transition ≤ 3 000 000 | recorded-proof estimate stays below 4 000 000, so no receipt is delayed for proof size |
| `w.proof_routing` (A2) | every receipt of every *used* source receipt proof (the entry `lookupLast` selects for a new source chunk) routes, under `L(epoch_id)`, to the validated shard | no receipt is Merkle-hashed but filtered out (proof-size bound); holds on every honest single-epoch witness: proofs are built per target shard with the same layout (`chain.rs:4132-4150`, `receipt.rs:438-447`, V3-D0-DESIGN §10.1). A foreign receipt with a valid path is accepted by nearcore (it filters) but is outside D0 |
| `r.shape` | every receipt in `R`: `ReceiptEnum::Action` (tag 0), exactly one `Transfer` action, no input data ids, no output data receivers, ED25519/SECP256K1 signer key, valid named receiver (no implicit-account creation) | v1 receipt shape |
| `w.proof_shape` | every receipt in every `source_receipt_proofs` entry — including an entry overridden by a later duplicate key — has the D0 receipt shape | the D0 decoder does not model the full receipt type universe; only adversarially crafted witnesses (duplicate keys) can violate it without violating `r.shape` |
| `r.refunds` | predecessor may be `system` (refund receipts are allowed, unlike v1). For a gas refund (`signer_id = receiver_id`): no gas key for `signer_public_key`, and the access key is absent or `FullAccess` (so `try_refund_allowance` writes nothing) | refund path without key writes |
| `r.success` | every receipt succeeds: receiver exists as AccountV1, no balance overflow, storage stake satisfied, burn fits u128 | failure/rollback path |
| `e.compute` | the compute limit (`gas_limit`) is not reached before the last receipt | delayed queue |
| `e.queues_empty` | delayed queue, every outgoing buffer, the promise-yield queue are empty in the pre-state (absent indices or `first = next`) | queue processing |
| `e.forwarded` | every generated receipt (gas/deposit refunds) is forwarded by `ReceiptSink` (granted bandwidth and outgoing gas limit suffice), i.e. nothing is buffered | buffer writes, bandwidth requests |
| `e.distinct_ids` | receipt ids pairwise distinct | outcome/refund id collisions |
| `e.scheduler_state` | `0x0f` absent or decodes as `BandwidthSchedulerState::V1` | `apply` aborts |

Everything else is **inside** D0 and must be formalized: arbitrary numbers of
shards and boundary accounts, cross-shard incoming receipts from any shard,
source receipt proofs and the shuffle, any number of implicit transitions
(missing chunks), the full multi-shard bandwidth scheduler including bandwidth
requests from other shards, the ChaCha20 tie-break and arbitrary congestion
infos of other shards (exact f64), refund routing and the outgoing-receipts
root, the outcome root, gas and balance burnt, own congestion info with
`allowed_shard`, bandwidth requests (empty), and the Reed–Solomon encoded
merkle root for any `(d, p)`.

### D1 — + Transfer transactions

Lifts `w.no_txs`, `c.no_tx_flags`. Allowed: `W.transactions`,
`W.new_transactions` of Transfer-only `SignedTransaction`s (V0 or V1, ED25519
signatures — verified inside `Rel` as nearcore does in
`verify_and_charge_tx_ephemeral`), nonce and access-key checks (full-access
keys), balance and gas pre-payment, local receipts (receiver on the same
shard), invalid-validity-period transactions skipped per `tx_valid`,
`check_valid_for_config`, `tx_root`. Still no gas keys, no function-call keys,
no delegate actions.

### D2 — + all non-WASM actions and queues

Lifts `r.shape`, `r.success`, `e.compute`, `e.queues_empty`, `e.forwarded`,
`c.own_congestion_zero`, `c.single_epoch`, `c.no_split_gate` partially:
CreateAccount, AddKey, DeleteKey, DeleteAccount, Stake (uses
`minimum_stake`), Delegate/DelegateV2, gas keys, implicit-account creation,
failures with rollback and deposit refunds, function-call access-key
allowances, delayed queue, outgoing buffers and bandwidth requests, epoch
boundaries with `ValidatorAccountsUpdate`. Still no `FunctionCall`,
`DeployContract`, global contracts, data/yield/resume receipts.

### D3 — + WASM

Lifts the remaining action restrictions: `FunctionCall` (near-vm-runner
Wasmtime semantics, gas metering, host functions incl. `epoch_height`,
validator stakes, `chain_id`), `DeployContract`, global contracts, `Data`,
`PromiseYield`/`PromiseResume`/V2 receipts, yield timeouts, contract code
distribution (`w.no_code` lifted).

### D∞ — everything

Lifts `c.no_split_gate` (dynamic-resharding split search) and the genesis main
transition, and admits resharding implicit transitions (`retain_split_shard`,
child congestion info), i.e. `Rel_D∞ = Rel`.

### Mainnet coverage (honest)

A mainnet chunk is in D0 only if the shard's previous chunk **and** the chunk
itself carry no transactions, every incoming receipt is a plain Transfer (or
refund), and nothing was delayed or buffered. On today's busy mainnet shards
this is rare; D0 is the first rung that is *a real validator's statement for a
real multi-shard chain* (its chunks, contexts and witnesses are exactly
mainnet's formats), not yet a useful fraction of mainnet traffic. D1 (Transfer
transactions) is the first rung expected to cover a measurable fraction of
real chunks.

## 7. Reference oracle (`oracle/v3`, binary `near-arena-oracle-v3`)

A separate crate (`oracle/v3/`, depends on nearcore's `integration-tests`), so the frozen
v1/v2 oracle and its lock file are untouched.

* **Chains.** nearcore's own `TestEnv` (8 validator clients, real `NightshadeRuntime` with
  `RuntimeConfigStore::new(None)` = mainnet PV 86 parameters, real epoch manager, real block
  and chunk production, chunk-state-witness production and chunk endorsement), 4/5/6 shards
  (`ShardLayout::multi_shard_custom`, boundary accounts), `num_block_producer_seats` ∈
  {8, 100, 16, 3} ⇒ Reed–Solomon (2,8), (33,100) = mainnet, (5,16), (1,3); random
  Transfer transactions on a random subset of shards each height (cross-shard receivers,
  failing receivers, implicit receivers, two-action transactions, bursts of 400–900),
  randomly missing chunks, forced missing chunks of the burst's target shard for 3 heights
  (buffering ⇒ bandwidth requests and non-zero congestion of other shards), one chain with a
  40-height gap of one shard (segment > 32 blocks), one chain with a 10 Tgas gas limit
  (delayed receipts; in D0 under A1), one chain (index 8) with a 1500 Tgas gas limit (every chunk
  outside D0 by A1 `c.gas_limit`), 30-block epochs (validator updates at epoch starts). A `FakeClock` and a
  fixed genesis time make every run byte-reproducible from the seed.
* **Witnesses.** The `ChunkStateWitness` values the chunk producers hand to the partial-witness
  layer (`DistributeStateWitnessRequest`), serialized with nearcore borsh — the real bytes. They
  are also delivered to the chunk validators of the `TestEnv` as usual (endorsements flow).
* **Claims.** Built by `oracle/v3/src/claim.rs` from the producing node's chain store and epoch
  manager, mirroring `get_state_witness_block_range`; every block hash is recomputed from the
  claim's header parts and checked against nearcore's.
* **Reference judge.** `oracle/v3/src/judge.rs`: actor-level epoch check, then
  `pre_validate_chunk_state_witness` + `validate_chunk_state_witness` (the witness path; panics
  count as reject), with the claim's Reed–Solomon parameters. Every honest witness (3 992 in the
  reported run) is accepted.
* **D0 classifier.** `oracle/v3/src/d0.rs`: an independent Rust predicate using a tracking
  node's full state and stored execution outcomes.
* **Mutants** (`oracle/v3/src/mutate.rs`), each judged by nearcore (or false by the claim
  format for hash-authenticated context): every compared header field (claim and witness
  header changed together), unchecked fields (`height_created`, `height_included`, transition
  `block_hash`), dropped / corrupted / extra / duplicated (both orders) / unsorted
  receipt-proof entries, dropped and junk `base_state` values, **every single recorded trie
  value dropped in turn** (read-set faithfulness), wrong post roots, applied-receipts hash,
  epoch id, trailing byte, dropped / corrupted implicit transitions, context mutations (header
  bytes, slot heights, slot inners, missing or extra block, epoch-start flag), trusted facts
  (Reed–Solomon parameters; `chain_id` and `minimum_stake`, which D0 does not read).
  **A2 mutant** (`w.foreign_routed_receipt`, every accepted D0 case whose segment starts at B2):
  a D0-shaped receipt routed to another shard is appended to a source proof of B2, and the source
  chunk's `prev_outgoing_receipts_root`, its chunk hash (the map key), B2's `chunk_headers_root`
  and hash, and the endorsed chunk's `prev_block_hash` are recomputed. Every value nearcore's
  validator reads is then consistent and the foreign receipt is filtered out, so `Rel` holds *by
  construction* (nearcore cannot judge it directly: the mutated block is not in its store); the
  expected verdict is `out_of_domain` (`w.proof_routing`).
* **Leaf vectors** (`near-arena-oracle-v3 vectors`, `oracle/fixtures/v3/vectors/`): nearcore's
  `ChaCha20Rng` stream and `shuffle_receipt_proofs`; `CongestionControl::congestion_level`
  (f64 bits), `is_fully_congested`, `outgoing_gas_limit`; `reed_solomon_encode` + encoded merkle
  root for 8 parameter sets incl. (33,100) and (85,256); the bandwidth-scheduler state written
  by a real `Runtime::apply` of a missing chunk (600 random multi-shard contexts with requests,
  congestion and missed chunks).

## 8. Formalization (`spec/lean/v3`, Lake package `NearSpecV3`)

A separate Lake package requiring `NearSpec` and `ArenaCore` by path: no file of the pinned
v1/v2 package (`spec/lean/lakefile.toml`, `NearSpec.lean`, `NearSpec/*`) is modified.

| module | content | evidence |
|---|---|---|
| `ChaCha20` | ChaCha20Rng (rand_chacha 0.3.1), Lemire `gen_index`, rand 0.8.5 `shuffle` | 412/412 nearcore vectors |
| `GF256`, `ReedSolomon` | GF(2⁸) (0x11D), the crate's Vandermonde × inverse matrix (same Gaussian elimination), parts, encoded merkle root | 72/72 vectors (8 parameter sets); `decide +kernel` on two vectors; systematic form proved for t ≤ 8, d = 1 ⇒ parity = data |
| `F64` | exact binary64 for non-negative values (RNE), `round`, `as u64`, bit pattern | via `Congestion` vectors (bit-exact) |
| `Congestion` | congestion level, `is_fully_congested`, `outgoing_gas_limit`; integer characterization of "fully congested" | 3000/3000 vectors + 34 129-point threshold sweep (the characterization is tested, not proved) |
| `BandwidthScheduler` | full n-shard scheduler: allowances, link status, base grants, requests with the shared ChaCha20 tie-break, `distribute_remaining`, state + sanity hash, grants | 600/600 post-state vectors (grants are not observable in a vector; checked only through forward/buffer decisions in the difftest) |
| `Wire`, `ClaimV3`, `WitnessV3`, `Layout` | strict nearcore-borsh decoders (lenient last-wins `HashMap`), claim-v3 codec | `ClaimV3Props`: `decodeClaim_encode`, `Claim.encode_injective` (proved) |
| `TrieBuild` | partial trie from `PartialState` by hash lookup (fuel 400) | read-set mutants |
| `RuntimeD0` | `Runtime::apply` for new and missing chunks in D0 (reuses `NearSpec.TransferV1.applyReceipt`, `PTrie.find/set/upsert`, `outcomeRoot`) | difftest |
| `ChunkValidationV0` | `checkD0`, `RelD0` (steps 1–18 + D0 conditions) | difftest; `Examples.RealCase` |
| `ChallengeV3` | `ArenaCore.ChallengeSpec` instance (`Rel = RelD0 c.encode w`) | builds |
| `PrepD0` | the claim/hint side of a D0 verifier (V3-D0-DESIGN §1, §2.1, §6.1): `Hint`, `Prep`, `prepD0`, `Prep.encode`, `hintOf`, built only from the functions above | `nearspec-v3-test-prep` on every public fixture and difftest case |

**Non-vacuity (kernel).** `NearSpecV3.Examples.RealCase` (`lake build NearSpecV3.Examples.RealCase`,
≈ 2.5 min): `decide +kernel` proves `RelD0` on two real cases (a 4-shard chunk with one incoming
cross-shard receipt and Reed–Solomon (2,8); a 4-shard chunk with two incoming receipts, one
implicit transition and Reed–Solomon (5,16)) and on nearcore's accepted `dup_key_last_good`
mutant, and `¬ RelD0` on two nearcore-rejected mutants (`prev_state_root` changed; duplicated
proof key with the corrupt value last). Axioms: `propext`, `Quot.sound`.

**Compiled SHA-256 (A5).** `Wire`, `TrieBuild`, `BandwidthScheduler` and `ReedSolomon` import
`ArenaCore.SHA256Fast`, whose kernel-proved `@[csimp]` lemma `sha256 = sha256Fast` makes every
compiled `sha256` call in `NearSpecV3` use the fast implementation; statements and proofs still
see only `ArenaCore.sha256`. (Calls compiled inside the frozen `NearSpec` package, e.g. trie node
hashing, keep the reference implementation.)

Reuse for an AIR: every hash is `ArenaCore.sha256` (L5's SHA bus contract applies unchanged);
the trie and receipt semantics are v1/v2's (`PTrie`, `upsert` with its proofs,
`TransferV1.applyReceipt`, `outcomeRoot`), which L6 arithmetizes.

## 9. Relation to v1/v2

v1 (`near/pv86/receipt-transfer-batch/v0`) and v2 (`…/v1`) remain immutable:
their files, challenges and TreeDigests are frozen and nothing here edits
them. Conceptually, v2's relation is a fragment of D0's step 11 for the
degenerate context "one shard, no requests, zero congestion, a batch given by
the judge" — but its claim (projected roots, receipt commitments) is not a
chunk-validation claim, so a v2 proof cannot be converted into a v3 proof or
an endorsement. Future work targets v3 only.

## 10. Results: what is formalized, tested, and out of D0

**3-way differential test** (`spec/difftest-report-v3.json`; nearcore oracle vs compiled Lean
`nearspec-v3-check` vs independent Python `oracle/tools/spec_check_v3.py`), seed 4243, 8 chains
× 120 blocks: **9 904 cases, 0 disagreements** — 907 honest D0 cases (all accepted by all three),
1 856 honest out-of-domain cases (all classified out of D0 by both checkers), 7 141 mutants (1 176
accepted by nearcore, 5 965 rejected; both checkers agree on every one, incl. 1 384 single-node
drops: nearcore reads every recorded value and so does the Lean/Python model). D0 coverage: 631
cases with incoming receipts (cross-shard), 62 with implicit transitions, 98 with bandwidth
requests of other shards in the context, 476 with non-zero congestion of other shards, 66 with
several source blocks; Reed–Solomon (33,100) 253, (2,8) 271, (5,16) 227, (1,3) 156; 4/5/6 shards.
Public subset with its own report: `oracle/fixtures/v3/public/` (`difftest.json`, 0 disagreements).

**Proved:** claim codec round trip and injectivity; `RelD0` (and its negation) on real cases by
kernel evaluation; Reed–Solomon systematic form for small parameters; v2's trie lemmas (reused).
**Tested, not proved:** that the Lean transcription equals nearcore (difftest + leaf vectors);
the integer form of `is_fully_congested`; that `upsert` builds nearcore's canonical trie (as v2).
**Not directly observable:** scheduler grants (only through forwarding decisions).

**D0 exclusions exercised by honest out-of-domain cases:** `w.no_txs`, `c.no_tx_flags`,
`c.own_congestion_zero`, `e.queues_empty`, `e.forwarded`, `e.compute`, `r.success`, `r.shape`,
`c.single_epoch`, `c.no_split_gate` (validator updates), `c.not_genesis`, `c.segment`. Not
reachable in the generated chains (stated, not exercised): `c.pv86` (all PV 86), `c.layout`
(≤ 64 shards V2/V3 only), `c.headers` (PV 86 produces only V6 / V4–V5), `w.size` (> 3 MB of
state), `w.no_code`, `r.refunds` (needs function-call or gas-key signers), `e.distinct_ids`
(impossible on a real chain), and the dynamic-resharding split gate (the test epoch config has
no `dynamic_resharding_config`).

**Findings.** (1) The validator never checks `height_created`, `height_included`, the chunk
producer's signature or the transitions' `block_hash` (mutants accepted by nearcore; the
endorsement metadata does carry `height_created`). (2) `source_receipt_proofs` decoding is
lenient (unsorted keys and duplicates accepted, last value wins). (3) System (refund) receipts
burn no tokens but still report `gas_burnt = G` in their outcome and in the chunk's `gas_used`.
(4) Every recorded trie value is read (single-node drops are always rejected): the witness is
minimal.

**Trusted facts** (spec/claim-v3.md §2.4) are only consistency-checked; a proof is meaningful
only to a verifier that built (or checked) them from its own chain state.
