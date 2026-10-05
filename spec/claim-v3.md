# Claim encoding v3 — `near-arena-claim-v3` / `near-arena-witness-v3`

Canonical byte formats for the statement **`near/pv86/chunk-validation/v0`**:
*"`validate_chunk_state_witness` of nearcore 2.13.4 accepts this witness for
this chunk header, in this chain context"* (semantics:
`spec/near-chunk-validation-v0.md`; nearcore map:
`docs/research/chunk-validation-boundary.md`). Pinned nearcore `2.13.4` =
`44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, protocol version 86.

**One format for every domain.** The full relation and every domain
restriction `D0 ⊂ D1 ⊂ D2 ⊂ D3 ⊂ D∞` (§6 of the spec) use exactly these two
files. A domain never adds, removes or reinterprets a field; it only restricts
which values occur. A claim is the same bytes whichever domain's prover
handles it, so a `Dk` prover is a drop-in validator for the chunks in `Dk`.

This format is unrelated to v1/v2 (`spec/claim-v1.md`, `spec/claim-v2.md`),
which stay frozen. Every file starts with a v3 format tag; v1/v2 files never
decode as v3 and vice versa.

| file | who sees it | role |
|---|---|---|
| `claim.bin` | everyone; the only statement input of `verify` | the endorsed chunk + the chain context the validator relies on |
| `witness.bin` | prover only | the real `ChunkStateWitness` bytes (+ contract code, empty below D3) |
| `params.bin` | judge-run `prepare` | challenge-level parameters (domain id, runtime-config digest) |

There is no `request.bin`: the claim *is* the job. Unlike v1/v2 the claim has
no "output" fields computed by the judge — the outputs of re-execution are the
`prev_*` fields of the endorsed chunk header, and the statement is that they
are correct.

## 1. Conventions

As v1/v2: fixed-width little-endian integers; `bytes` = `u32` length ‖ raw
bytes; `hash` = 32 raw bytes; `Vec<T>` = `u32` count ‖ elements; `Option<T>` =
`u8` 0 | `u8` 1 ‖ T; strict decoding (truncation, trailing bytes, length past
the end, unknown tags, values out of range → reject); one encoding per value.
"nearcore borsh of `T`" means exactly the bytes nearcore's `borsh` produces for
`T` at the pinned commit, and decoding with nearcore's own rules.

## 2. `claim.bin` — `near-arena-claim-v3`

```
bytes   format_id      = "near-arena-claim-v3"
bytes   statement_id   = "near/pv86/chunk-validation/v0"
u32     protocol_version                     protocol version of epoch_id (trusted)
bytes   chain_id                             1..64 bytes, 0x21..0x7e (trusted; genesis)

# A. The endorsed chunk
hash    epoch_id                             = get_epoch_id_from_prev_block(prev_block_hash) (trusted);
                                               the witness's epoch_id and the endorsement metadata's epoch_id
bytes   chunk_inner                          nearcore borsh of the TAGGED ShardChunkHeaderInner of the endorsed chunk

# B. Chain segment (authenticated by hashes, newest first)
u32     n_blocks                             ≥ 1
BlockRec × n_blocks

# C. Trusted chain/epoch facts
u16     rs_data_parts                        num_data_parts()   ┐ Reed–Solomon code of chunk bodies
u16     rs_total_parts                       num_total_parts()  ┘ (genesis epoch config)
Vec<EpochRec>     epochs                     strictly ascending by epoch_id
Vec<u8>           epoch_start_after          n_blocks flags: is_next_block_epoch_start(block_hash(blocks[i]))
Vec<ApplyFacts>   apply_facts                one per applied block, chronological (main block first, then implicit blocks)
Vec<u8>           tx_valid                   one 0/1 flag per witness `transactions[i]` (validity period)
Option<bytes>     genesis_chunk_extra        nearcore borsh of ChunkExtra; Some iff the last new chunk is the genesis chunk
```

Derived (not encoded): `chunk_hash = SHA256(SHA256(chunk_inner) ‖ chunk_inner.encoded_merkle_root)`;
`prev_block_hash`, `shard_id`, `height_created` = fields of `chunk_inner`.
These, with `epoch_id`, are exactly what a `ChunkEndorsement` signs.

### 2.1 `BlockRec`

```
u8      header_version          nearcore borsh tag of BlockHeader (V6 = 5 at PV 86)
hash    prev_hash
bytes   inner_lite              nearcore borsh of BlockHeaderInnerLite
bytes   inner_rest              nearcore borsh of the version's BlockHeaderInnerRest*
Vec<ChunkSlot> slots            one per shard index of the block, in index order
ChunkSlot = bytes inner (TAGGED ShardChunkHeaderInner) ‖ u64 height_included
```

`block_hash(r) = SHA256( SHA256( SHA256(inner_lite) ‖ SHA256(inner_rest) ) ‖ prev_hash )`
(`block_header.rs:781-791`). The block signature is **not** included (it is not
hashed and not used by validation). A `ChunkSlot` is exactly the preimage of the
`ChunkHashHeight` leaf of the block's `chunk_headers_root`; the chunk producer's
signature is not included (not hashed, not used).

**Hash discipline** (checked by the relation, so a claim violating it is false):

* `block_hash(blocks[0]) = chunk_inner.prev_block_hash`;
* `blocks[i].prev_hash = block_hash(blocks[i+1])` for `i + 1 < n_blocks`;
* `merklize([ChunkHashHeight(chunk_hash(s.inner), s.height_included) | s ∈ blocks[i].slots]) = blocks[i].inner_rest.chunk_headers_root`;
* the segment is **exactly** the blocks the validator's backward walk reads
  (`chunk_validation.rs:144-253`): from the prev block back to and including the
  block holding the last-but-one new chunk of the shard, or back to genesis if
  that comes first (spec §3.2). So `n_blocks` is determined by the chain; no
  block may be added or omitted.

Hence everything in section B is a function of `chunk_inner.prev_block_hash`
(under SHA-256 collision resistance). A consumer who knows that block is in its
chain needs to check nothing else in section B.

### 2.2 `EpochRec`

```
hash    epoch_id
u32     protocol_version
u64     epoch_height
bytes   shard_layout            nearcore borsh of ShardLayout
Vec<(bytes account_id, u128 stake)> validators     the epoch's validator stakes, ascending by account id
```

The table holds exactly the epochs referenced by the claim: `epoch_id` and the
`epoch_id` of every block header in section B (strictly ascending, no extras).
`protocol_version` of `epoch_id` must equal the top-level `protocol_version`.

`epoch_start_after[i]` is the epoch manager's `is_next_block_epoch_start` for
`blocks[i]` (true for the genesis block, `chain/epoch-manager/src/lib.rs:1617-1620`).
It is trusted, but `Rel` checks it against the authenticated headers wherever
they determine it: the epoch of the block after `blocks[i]` (`c.epoch_id` for
`i = 0`, `blocks[i-1].epoch_id` otherwise) must be `blocks[i].next_epoch_id` if
the flag is 1 and `blocks[i].epoch_id` if it is 0
(`get_epoch_id_from_prev_block`, `adapter.rs:170-179`).

### 2.3 `ApplyFacts` (per applied block X: the main block B2, then each implicit block M)

```
Option<ValidatorUpdateFacts> validator_update      Some iff X is the first block of its epoch
u128    minimum_stake                              EpochInfoProvider::minimum_stake(X.prev_hash)
Option<SplitGate> split_gate                       Some iff compute_proposed_split's gate is open for X
ValidatorUpdateFacts = Vec<(bytes account, u128)> stake_info       ascending by account
                     ‖ Vec<(bytes account, u128)> validator_rewards ascending by account
                     ‖ Option<bytes> protocol_treasury_account
SplitGate = u64 memory_usage_threshold ‖ u64 min_child_memory_usage ‖ u64 max_number_of_shards
          ‖ Vec<u64> force_split_shards ‖ Vec<u64> block_split_shards
```

`validator_update` holds the *unfiltered* epoch-manager answers
(`compute_stake_return_info(X.prev_hash)`, genesis treasury); the per-shard
filtering and `last_proposals` are computed inside the relation exactly as
`process_state_update` does (`chain/chain/src/runtime/mod.rs:229-271`).
"Gate open" means: DynamicResharding enabled at the epoch's protocol version,
the epoch config has a `dynamic_resharding_config`,
`is_next_block_possibly_last_in_epoch(X.height, X.prev_hash)` and
`can_reshard(X.prev_hash, ·)` (`runtime/mod.rs:583-622`).

### 2.4 Classification of every claim value

**Authenticated** values are checked by `Rel` against hashes; **trusted** values
are answers of the consumer's own epoch manager / store / genesis config that no
hash in the claim determines. Wherever a trusted value is partly derivable from
the authenticated segment, `Rel` checks that part (column "checked by `Rel`").

| # | value | class | checked by `Rel` | read by rungs |
|---|---|---|---|---|
| A1 | `chunk_inner` | the statement | version (`validate_version`), every `prev_*`/root field vs re-execution | all |
| A2 | section B (headers, slots) | authenticated by `chunk_inner.prev_block_hash` | hash chain, `chunk_headers_root`, segment = walk | all |
| T1 | `epoch_id` | trusted | = `W.epoch_id`; = `blocks[0].epoch_id` or `blocks[0].next_epoch_id` per `epoch_start_after[0]`; must be in `epochs` | all |
| T2 | `protocol_version` | trusted | = `epochs[epoch_id].protocol_version` | all (D0–D3: must be 86) |
| T3 | `chain_id` | trusted | — | D2 (implicit/ETH accounts, signatures over chain id are not used at 86 [unverified for DelegateV2]), D3 (`chain_id` host function) |
| T4 | `rs_data_parts`, `rs_total_parts` | trusted (genesis epoch config) | `data = (total ≤ 3 ? 1 : (total − 1)/3)`, `2 ≤ total ≤ 256` | all (encoded merkle root) |
| T5 | `epochs[e].protocol_version` | trusted | see T2; all equal 86 below D∞ | all |
| T6 | `epochs[e].shard_layout` | trusted | `chunk_inner.shard_id` ∈ layout; slot count of every block = number of shards of its epoch | all (routing, scheduler, receipt roots) |
| T7 | `epochs[e].epoch_height` | trusted | — | D3 (`epoch_height` host function) |
| T8 | `epochs[e].validators` | trusted | — | D3 (`validator_stake`, `validator_total_stake`) |
| T9 | `epoch_start_after[i]` | trusted | consistent with header epoch ids (§2.2); 1 for a genesis block | all (D0: must be 0 for every applied block's parent ⇒ excludes epoch starts) |
| T10 | `apply_facts[i].validator_update` | trusted | `Some` iff the applied block starts an epoch (T9) | D2+ |
| T11 | `apply_facts[i].minimum_stake` | trusted | — | D2+ (Stake action) |
| T12 | `apply_facts[i].split_gate` | trusted | `None` if DynamicResharding is off at the epoch's version | D∞ (D0–D3 require `None`) |
| T13 | `tx_valid` | trusted (store + genesis `transaction_validity_period`) | length = `|W.transactions|`; all 1 if B2 is genesis | D1+ |
| T14 | `genesis_chunk_extra` | trusted | `Some` iff B2 is the genesis block | D∞ |

`Rel` can only check the trusted values for internal consistency; it cannot
check that they are *true*. Consequently:

> **A proof for `claim.bin` is meaningful only to a verifier who built section C
> (and `epoch_id`, `protocol_version`, `chain_id`) from its own chain state, or
> independently checked each trusted item against its own epoch manager and
> store.** A claim produced by a third party must never be presented as
> "validated" on the strength of a proof alone: a false trusted value (e.g. a
> wrong shard layout or wrong Reed–Solomon parameters) yields a true `Rel` for a
> chunk no honest validator would endorse. Values not read by a rung (e.g. T11
> in D0) must still be the true values for the drop-in criterion
> (`spec/near-chunk-validation-v0.md` §4).

These are exactly the values `validate_chunk_state_witness` obtains from the
store and the epoch manager (`docs/research/chunk-validation-boundary.md` §10).

## 3. `witness.bin` — `near-arena-witness-v3` (prover only)

```
bytes   format_id      = "near-arena-witness-v3"
bytes   state_witness  nearcore borsh of ChunkStateWitness, ≤ 64 MiB
                       (exactly the bytes ChainStore::create_state_witness produces and the chunk
                        producer compresses and distributes; no re-encoding)
Vec<bytes> contract_code     code blobs received via ChunkContractAccesses; appended to
                             main_state_transition.base_state before validation (partial_witness_tracker.rs:692-696);
                             empty in D0–D2
```

`state_witness` is decoded with nearcore's rules
(`docs/research/chunk-validation-boundary.md` §2.2), including the lenient
`HashMap` decoding (unsorted keys accepted, a duplicate key keeps the last
value). The witness is **not** canonical: `base_state` may hold extra nodes,
`ChunkStateTransition.block_hash`, the header's `height_included` and
`signature`, and the merkle-path shape are not checked by nearcore and are not
checked by the relation either.

## 4. `params.bin`

```
bytes "near-arena-params-v3" ‖ bytes "near/pv86/chunk-validation/v0" ‖ u32 86
‖ bytes domain_id ("D0" | "D1" | "D2" | "D3" | "Dinf")
‖ hash runtime_config_digest_v3
```

`runtime_config_digest_v3 = sha256(JCS(params JSON))` of the pinned
`RuntimeConfigStore::new(None).get_config(86)` description (as v2's, plus the
congestion-control parameters used by §9 of the boundary map:
`max_congestion_{incoming,outgoing}_gas`, `max_congestion_memory_consumption`,
`max_congestion_missed_chunks`, `{max,min}_outgoing_gas`,
`allowed_shard_outgoing_gas`, `main_storage_proof_size_soft_limit`). Emitted by
`near-arena-oracle params --scope v3`.

## 5. Size bounds

`max_claim_bytes = 1 048 576` (D0 bounds: `n_blocks ≤ 32`, ≤ 64 shards).
`max_witness_bytes = 64 MiB + 4 KiB + Σ code` (D0: ≤ 8 MiB, see spec §6).

## 6. Relation to the arena interfaces

`ArenaCore.ChallengeSpec` for domain `k`: `Claim` = decoded `claim.bin`;
`Witness` = `witness.bin` bytes; `Rel = Rel_Dk := Rel ∧ InDk` (spec §6);
`Domain c := ClaimDk c ∧ ∃ w, Rel_Dk c w`; `encodeClaim`/`decodeClaim` = this
format with the round-trip law. Because `Rel_Dk ⇒ Rel`, a proof admitted in any
domain establishes the full chunk-validation statement.
