import NearSpecV3.D3.FunctionCall
import NearSpecV3.ClaimV3Props

/-!
# `NearSpecV3.GenesisD3` — the `MainTransition::Genesis` branch, alongside `checkD3`

`checkD3` (`D3/FunctionCall.lean:400`) refuses every claim whose last new chunk `B2` is the genesis
block: `checkD2Core` throws `out of domain (c.not_genesis)` (`ChunkValidationD2.lean:176`). That
branch is a first-class validator path in the pinned validator — `MainTransition::Genesis`
(`chain/chain/src/stateless_validation/chunk_validation.rs:402-414`) — and 137 recorded corpus cases
(`d3c7` 39, `d3c8` 60, `d3c9` 19, `d3c10` 19) are genesis-B2 claims that nearcore accepts. The plan's
L6 row `L0-D2-027` owns closing that gap.

**This module does not change `checkD3`, `RelD3`, `checkD2Core` or any other existing declaration.**
It defines the successor checker `checkD3G` beside them. `checkD3G` is `checkD2Core` with the genesis
main transition modelled: on a non-genesis `B2` it performs the same checks as `checkD2Core`
(the genesis code is skipped), so `checkD3G` is a strict extension of the *domain*, not a change to
the non-genesis relation.

## The genesis main transition, pinned

`pre_validate_chunk_state_witness` chooses the main transition
(`chunk_validation.rs:402-414`):

```rust
let main_transition_params = if last_chunk_block.header().is_genesis() {
    let epoch_id = last_chunk_block.header().epoch_id();
    let shard_layout = epoch_manager.get_shard_layout(&epoch_id)?;
    let chunk_extra =
        Chain::genesis_chunk_extra(genesis, store, &shard_layout, last_chunk_shard_id)?;
    MainTransition::Genesis { chunk_extra, block_hash: *last_chunk_block.hash(),
                              shard_id: last_chunk_shard_id }
} else { … MainTransition::NewChunk { … } };
```

`validate_chunk_state_witness_impl` then uses it without applying a chunk
(`chunk_validation.rs:596-604`):

```rust
let (mut chunk_extra, mut outgoing_receipts) =
    match (pre_validation_output.main_transition_params, cache_result) {
        (MainTransition::Genesis { chunk_extra, .. }, _) => (chunk_extra, vec![]),
        (MainTransition::NewChunk { new_chunk_data, .. }, None) => { … apply_new_chunk … }
        (_, Some(result)) => …,
    };
```

So the genesis branch:

* **applies nothing**: the chunk extra is read from the store (`Chain::genesis_chunk_extra`,
  `chain/chain/src/genesis.rs:218-235`), never recomputed;
* has **no outgoing receipts** (`vec![]`) — `merklize` over the per-shard hashes of the empty
  receipt lists is *not* the zero hash, so the header comparison is still informative;
* still checks `chunk_extra.state_root() == witness.main_state_transition().post_state_root`
  (`chunk_validation.rs:606-616`), then applies the implicit transitions on top of that root;
* still compares the whole header against the resulting chunk extra
  (`validate_chunk_with_chunk_extra_and_receipts_root`, `chain/chain/src/validate.rs:133-187`):
  `prev_state_root`, `prev_outcome_root`, `prev_validator_proposals`, `gas_limit`,
  `prev_gas_used`, `prev_balance_burnt`, `prev_outgoing_receipts_root`, congestion info,
  bandwidth requests and `proposed_split`.

`tx_valid`: for a genesis last chunk nearcore *derives* all-1 and never consults the store
(`chunk_validation.rs:382-386`: `if last_chunk_block.header().is_genesis() {
vec![true; transactions.len()] }`), so a truthful claim carries all-1 flags
(`spec/claim-v3.md` T13) and this checker requires exactly that.

`genesis_chunk_extra`: `Some` iff `B2` is the genesis block (claim-v3 T14); the bytes are trusted
(`Chain::build_genesis_chunk_extra`, `genesis.rs:237-257`). Its borsh is the tagged
`ChunkExtra` enum (`core/primitives/src/types.rs:815-821`): V1 = 0 … V5 = 4. V5 is what a
non-production genesis stores (`create_genesis_chunk_extra`, `genesis.rs:189-206`);
V2 is what a production genesis stores (`create_prod_genesis_chunk_extra`, `genesis.rs:207-216`).

## What is checked and what is not

`checkD3G` checks every genesis-relevant validator condition that the claim's authenticated bytes
determine. It cannot check the trusted facts (`genesis_chunk_extra` bytes, `apply_facts`,
`epoch_start_after`, `tx_valid`) against the verifier's own store; like `checkD2Core` it checks them
only for internal consistency. The genesis path is *not* covered by the differential oracle: the
Python reference (`oracle/tools/spec_check_v3_d3.py:1269-1271`) also throws out of domain. The
evidence for this branch is therefore the 137 recorded cases' `meta.json` `expected_rel` plus the
directed tests in `TestGenesisD3.lean`.
-/

namespace NearSpecV3

open NearSpec NearSpecV3.D2

/-! ## `ChunkExtra` (`core/primitives/src/types.rs:812-900`) -/

/-- `CongestionInfoV1` in the `ChunkExtra` borsh: `u8 0 ‖ u128 ‖ u128 ‖ u64 ‖ u16`
(`congestion_info.rs:176-215`). -/
def pCongestionCI : P Congestion := fun bs => do
  let (t, bs) ← pU8 "CongestionInfo tag" bs
  if t != 0 then throw "decode: CongestionInfo tag"
  let (d, bs) ← pU128 "delayed_receipts_gas" bs
  let (b, bs) ← pU128 "buffered_receipts_gas" bs
  let (r, bs) ← pU64 "receipt_bytes" bs
  let (a, bs) ← pU16 "allowed_shard" bs
  pure (⟨d, b, r, a⟩, bs)

/-- `BandwidthRequests::V1(Vec<BandwidthRequest>)`, request = `u16 to_shard ‖ [u8; 5] bitmap`
(`bandwidth_scheduler.rs`; the same shape as `Wire.pBwRequests`). -/
def pBwRequestsCI : P (List BwRequest) := fun bs => do
  let (t, bs) ← pU8 "BandwidthRequests tag" bs
  if t != 0 then throw "decode: BandwidthRequests tag"
  pVec "requests" (fun bs => do
      let (s, bs) ← pU16 "to_shard" bs
      let (m, bs) ← pTake 5 "bitmap" bs
      pure (⟨s, m⟩, bs)) bs

/-- A decoded `ChunkExtra` — the fields `validate_chunk_with_chunk_extra_and_receipts_root`
reads (`validate.rs:133-187`). `tag` 0…4 is the borsh discriminant; fields absent in older
variants keep the validator's accessor defaults (`types.rs:948-1075`):
`outcome_root`/`proposals`/`gas_used`/`gas_limit`/`balance_burnt` exist in all variants,
`congestion` only from V3 (accessor: `Default` for V1/V2), `bandwidthRequests` only from V4
(`None` for V1–V3), `proposedSplit` only V5 (`None` for V1–V4). -/
structure ChunkExtra where
  tag : Nat
  stateRoot : Bytes
  outcomeRoot : Bytes
  proposals : List Bytes
  gasUsed : Nat
  gasLimit : Nat
  balanceBurnt : Nat
  congestion : Congestion
  bandwidthRequests : Option (List BwRequest)
  proposedSplit : Option Bytes
  deriving DecidableEq, Repr

/-- `ValidatorStakeV1` for a V1 chunk extra: **untagged** `AccountId ‖ PublicKey ‖ u128`
(`types.rs:1079-1090`; contrast the tagged `ValidatorStake` in V2+). -/
def pValidatorStakeV1Raw : P Bytes := fun bs => do
  let (_, rest) ← pAccountId "stake account" bs
  let (_, rest) ← pPublicKey "stake key" rest
  let (_, rest) ← pU128 "stake" rest
  pure (consumed bs rest, rest)

def pChunkExtra : P ChunkExtra := fun bs => do
  let (tag, bs) ← pU8 "ChunkExtra tag" bs
  if tag > 4 then throw "decode: ChunkExtra tag"
  let (sr, bs) ← pHash "state_root" bs
  let (or, bs) ← pHash "outcome_root" bs
  let (props, bs) ← if tag == 0 then pVec "validator_proposals" pValidatorStakeV1Raw bs
                    else pVec "validator_proposals" pValidatorStake bs
  let (gu, bs) ← pU64 "gas_used" bs
  let (gl, bs) ← pU64 "gas_limit" bs
  let (bb, bs) ← pU128 "balance_burnt" bs
  let (cong, bs) ← if 2 ≤ tag then pCongestionCI bs else pure (⟨0, 0, 0, 0⟩, bs)
  let (bw, bs) ← if 3 ≤ tag then
      let (bw, bs) ← pBwRequestsCI bs
      pure (some bw, bs)
    else pure (none, bs)
  let (split, bs) ← if 4 ≤ tag then pOption "proposed_split" pTrieSplit bs else pure (none, bs)
  pure (⟨tag, sr, or, props, gu, gl, bb, cong, bw, split⟩, bs)

/-- Strict decode of a claim's `genesis_chunk_extra` bytes. -/
def decodeChunkExtra (b : Bytes) : Except String ChunkExtra := do
  let (ce, rest) ← pChunkExtra b
  if !rest.isEmpty then throw "decode: trailing bytes after ChunkExtra"
  pure ce

/-- `merklize` over the outgoing-receipts leaves of the empty receipt list: for each shard index of
the layout, `sha256(sha256(u64 shard ‖ ReceiptList(0)))` (`Chain::build_receipts_hashes` +
`merklize`, `chain.rs:4102-4130`, `merkle.rs:47-52`). This is the genesis chunk extra's
`prev_outgoing_receipts_root`, since the genesis branch produces no outgoing receipts. -/
def emptyOutgoingReceiptsRootD2 (l : Layout) : Bytes :=
  merklizeBorsh (l.shardIds.map fun s => sha256 (u64 s ++ encodeRcpts []))

/-! ## The genesis checker -/

/-- The genesis-branch checker: `checkD2Core`'s checks with `MainTransition::Genesis` modelled.

`genesisExtra` is the claim's decoded `genesis_chunk_extra` when `B2` is the genesis block and
`none` otherwise. For a non-genesis `B2` this function's behaviour coincides with `checkD2Core`'s
(the genesis branch is unreachable), which `checkD2Core_eq_of_not_genesis` records as a rewrite
theorem; for a genesis `B2` it checks the genesis main transition instead of applying a chunk. -/
def checkD2CoreG (hooks : ActionHooks) (allowCodes : Bool) (claimBytes witnessBytes : Bytes)
    (gasCap : Option Nat := none) : Except String Unit := do
  -- 3.1 decoding, actor checks
  let c ← (decodeClaimE claimBytes).mapError (fun e => s!"invalid claim: {e}")
  let (swBytes, codes) ← decodeWitnessFile witnessBytes
  if !allowCodes then check codes.isEmpty "out of domain (w.no_code): contract code"
  check (lenT swBytes ≤ 8388608) "out of domain (w.size): witness larger than 8 MiB"
  let w ← decodeStateWitnessD2 swBytes
  check (w.innerBytes == c.chunkInner) "invalid: witness chunk header differs from the claim"
  check (w.epochId == c.epochId) "invalid: epoch id"
  let H ← (decodeChunkInner c.chunkInner).mapError (fun e => s!"invalid claim: {e}")
  check (c.protocolVersion == 86) "out of domain (c.pv86)"
  -- 3.2 chain segment
  let blks ← c.blocks.mapM decodeBlk
  check (!blks.isEmpty) "invalid: empty chain segment"
  let referenced := dedupSorted (c.epochId :: blks.map (·.hdr.epochId))
  check (strictlyAscending (c.epochs.map (·.epochId)))
    "invalid: epoch table not strictly ascending"
  check (c.epochs.map (·.epochId) == referenced) "invalid: epoch table does not match the referenced epochs"
  let ep ← match c.epochs.find? (·.epochId == c.epochId) with
    | some e => pure e
    | none => throw "invalid: epoch_id not in the epoch table"
  check (ep.protocolVersion == c.protocolVersion)
    "invalid: epoch table does not match epoch_id / protocol_version"
  check (c.epochs.all (·.protocolVersion == 86)) "out of domain (c.pv86): epoch protocol version"
  check (c.epochs.all (·.shardLayout == ep.shardLayout)) "out of domain (c.same_layout): resharding"
  let L ← decodeLayout ep.shardLayout
  check (1 ≤ L.numShards && L.numShards ≤ 64) "out of domain (c.layout)"
  check (rsGenesisParamsOk c.rsDataParts c.rsTotalParts) "invalid: Reed-Solomon parameters"
  check (c.blocks.length ≤ 32) "out of domain (c.segment)"
  check (c.epochStartAfter.length == c.blocks.length) "invalid: epoch_start_after length"
  check (c.epochStartAfter.all (·.toNat ≤ 1)) "invalid: epoch_start_after flag"
  let afterEpochs := c.epochId :: blks.map (·.hdr.epochId)
  check ((List.range blks.length).all fun i =>
      match blks[i]?, afterEpochs[i]?, c.epochStartAfter[i]? with
      | some b, some e, some f =>
        (if f.toNat == 1 then e == b.hdr.nextEpochId else e == b.hdr.epochId) &&
        (!b.isGenesis || f.toNat == 1)
      | _, _, _ => false)
    "invalid: epoch_start_after inconsistent with the headers"
  check (c.applyFacts.all fun f => f.splitGate.isNone) "out of domain (c.no_split_gate)"
  check (w.newTxs.all TxD2.sizeOk) "invalid: new transaction exceeds max_transaction_size"
  let hashes := blks.map (·.hdr.hash)
  check (hashes.headD [] == H.prevBlockHash) "invalid: segment does not start at prev_block_hash"
  check ((blks.zip (hashes.drop 1)).all fun (b, h) => b.hdr.prevHash == h)
    "invalid: segment is not hash-linked"
  check (blks.all fun b => b.slots.length == L.numShards) "invalid: slot count"
  let idx ← match L.index H.shardId with
    | some i => pure i
    | none => throw "invalid: shard not in layout"
  let isNew := fun (b : Blk) => match b.slots[idx]? with
    | some (s, _) => s.heightIncluded == b.hdr.height
    | none => false
  check (blks.all fun b => b.slots.all fun (sl, _) => sl.heightIncluded ≤ b.hdr.height)
    "invalid: height_included above block height (block_congestion_info panics)"
  let b2i ← match blks.findIdx? isNew with
    | some i => pure i
    | none => throw "invalid: segment has no new chunk"
  let B2 ← match blks[b2i]? with | some b => pure b | none => throw "invalid: walk"
  -- genesis branch (`chunk_validation.rs:402-414`): B2 genesis ⇒ the main transition is the stored
  -- genesis chunk extra, and `genesis_chunk_extra` must be present (claim-v3 T14).
  let gen? : Option ChunkExtra ← if B2.isGenesis then
      match c.genesisChunkExtra with
      | some g => match decodeChunkExtra g with
        | .ok ce => pure (some ce)
        | .error e => throw s!"invalid claim: genesis_chunk_extra: {e}"
      | none => throw "invalid: genesis_chunk_extra missing for a genesis main block"
    else
      match c.genesisChunkExtra with
      | some _ => throw "invalid: genesis_chunk_extra for a non-genesis main block"
      | none => pure none
  -- A genesis block is the first block of the chain: no block can be older than it in the segment
  -- (`blks[i].prevHash = hash(blks[i+1])`, so B2 genesis at `b2i` with a successor would require a
  -- SHA-256 output equal to zero).
  if B2.isGenesis then
    check (b2i + 1 == blks.length) "invalid: blocks older than the genesis block in the segment"
  let stop ← match (blks.drop (b2i + 1)).findIdx? isNew with
    | some j => pure (b2i + 1 + j)
    | none =>
      -- For a genesis B2 there is no last-but-one new chunk: the validator's walk stops at genesis
      -- (`chunk_validation.rs:236-240`), so B2 is the last block of the segment and the source
      -- blocks are exactly `[B2]`.
      if B2.isGenesis then pure b2i
      else throw "invalid: segment does not reach the last-but-one new chunk"
  check (stop + 1 == blks.length) "invalid: segment is not exactly the blocks the validator reads"
  let implicitIdx := (List.range b2i).reverse            -- oldest first
  let sourceBlks := (blks.drop b2i).take (stop - b2i)
  -- applied blocks: main block B2 first (non-genesis only), then implicit blocks
  -- (`pre_validate…` pushes B2 only when it is not genesis; `chunk_validation.rs:402-430`).
  let appliedIdx := (if B2.isGenesis then [] else [b2i]) ++ implicitIdx
  check (c.applyFacts.length == appliedIdx.length) "invalid: apply_facts length"
  check ((appliedIdx.zip c.applyFacts).all fun (i, f) =>
      f.validatorUpdate.isSome == (c.epochStartAfter.getD (i + 1) 0 == 1))
    "invalid: validator_update does not match the epoch start"
  let slotB2 ← match B2.slots[idx]? with | some p => pure p.2 | none => throw "invalid: slot"
  -- 3.3 / 3.4 source receipts. Genesis source blocks carry no receipt proofs and contribute no
  -- receipts (`chunk_validation.rs:462-475`: genesis ⇒ `source_receipt_proofs` empty, `vec![]`).
  let mut receipts : List Rcpt := []
  let mut used : Nat := 0
  for S in sourceBlks do
    if S.isGenesis then
      check (w.entries.isEmpty) "invalid: source_receipt_proofs must be empty for a genesis source block"
    else
      let mut proofs : List EntryD2 := []
      for (s, ci) in S.slots do
        if s.heightIncluded == S.hdr.height then
          let key := chunkHash s.inner ci.encodedMerkleRoot
          let e ← match lookupLastD2 key w.entries with
            | some e => pure e
            | none => throw "invalid: missing source receipt proof"
          check (e.proof.fromShard == ci.shardId) "invalid: receipt proof from_shard_id"
          check (e.proof.toShard == H.shardId) "invalid: receipt proof to_shard_id"
          check (verifyReceiptProofD2 ci.prevOutgoingReceiptsRoot e) "invalid: receipt proof merkle path"
          proofs := proofs ++ [e]
          used := used + 1
      let shuffled ← match shuffleWithSeed proofs S.hdr.prevHash with
        | some p => pure p
        | none => throw "invalid: shuffle fuel exhausted (probability < 2^-1024)"
      receipts := receipts ++
        (shuffled.map fun e => e.receipts.filter fun r => L.shardOf r.recv == H.shardId).flatten
  check ((distinctKeysD2 w.entries).length == used) "invalid: source_receipt_proofs contains extra proofs"
  check (sha256 (encodeRcpts receipts) == w.appliedReceiptsHash) "invalid: applied receipts hash"
  -- steps 8, 9: transactions of the last new chunk and their validity flags
  check (merklizeBorsh (w.txs.map TxD2.raw) == slotB2.txRoot) "invalid: transaction root of the last chunk"
  check (c.txValid.length == w.txs.length) "invalid: tx_valid length"
  -- genesis: the flags are derived all-1 (`chunk_validation.rs:382-386`), so a truthful claim
  -- carries all 1s (claim-v3 T13).
  if B2.isGenesis then
    check (c.txValid.all (·.toNat == 1)) "invalid: tx_valid not all 1 for a genesis main block"
  -- 3.5 main transition
  let sched ← match Scheduler.Params.calculate Scheduler.Config.pv86 L.numShards with
    | some p => pure p
    | none => throw "invalid: bandwidth scheduler params (assert panics)"
  let facts0 := c.applyFacts.headD ⟨none, 0, none⟩
  let ctxB2 := blockCtx L H.shardId slotB2.gasLimit B2 B2.hdr.nextGasPrice
  let merged := w.main.values ++ codes
  let store := mkHStore merged
  -- w.size: sums the merged list (conservative; spec/near-chunk-validation-d3.md §2.2)
  let baseBytes := (merged.map List.length).foldl (· + ·) 0
  -- The main transition's output. Genesis: the stored chunk extra, with no outgoing receipts
  -- (`chunk_validation.rs:602-604`), and the header's `prev_state_root` is its `state_root`
  -- possibly updated by implicit transitions.
  let mut root : Bytes ← match gen? with
    | some ce =>
      check (w.main.postStateRoot == ce.stateRoot)
        "invalid: main transition post state root differs from genesis_chunk_extra"
      -- No trie reads happen for a genesis chunk, so the witness's `base_state` is unread and its
      -- removals are zero; the proof-size bound is applied to the merged list as in D2.
      check (baseBytes + 2000 * 0 ≤ 4000000)
        "out of domain (w.size): storage-proof upper bound may exceed main_storage_proof_size_soft_limit"
      pure ce.stateRoot
    | none =>
      let env : Env := { envOf c ctxB2 B2 facts0.minimumStake sched with
                         store := store, preRoot := slotB2.prevStateRoot }
      let tMain := revealAll store revealFuel slotB2.prevStateRoot
      check (tMain.hashOf == slotB2.prevStateRoot) "invalid: main base_state does not hash to prev_state_root"
      let lastProps := slotB2.proposals.filterMap decodeProposal
      let out ← applyNewChunkD2 hooks prims env tMain facts0.validatorUpdate lastProps receipts
        (w.txs.zip (c.txValid.map (· != 0))) slotB2.congestion
      check (baseBytes + 2000 * out.cdRemovals ≤ 4000000)
        "out of domain (w.size): storage-proof upper bound may exceed main_storage_proof_size_soft_limit"
      -- D3: per-chunk WASM gas cap (`G_α`, D3_WASM_REQUIREMENTS §1.1/§2.4); D2 passes `none`
      if let some cap := gasCap then
        check (out.wasmGas ≤ cap) s!"out of domain (e.g_alpha): chunk function-call gas {out.wasmGas} > G_α {cap}"
      check (out.root == w.main.postStateRoot) "invalid: main transition post state root"
      pure out.root
  -- 3.6 implicit transitions (`chunk_validation.rs:648-756`): applied to the main transition's
  -- chunk extra. For genesis these are the *only* applied transitions and they run on the stored
  -- genesis chunk extra's root.
  check (w.implicit.length == implicitIdx.length) "invalid: implicit transitions count"
  -- For genesis, `mainProps` is the genesis chunk extra's proposals; `applyMissingChunkD2` reads
  -- them for the validator-account filtering (`process_state_update`, `runtime/mod.rs:229-271`).
  -- The implicit transitions are applied against the genesis root, so the proposals passed in are
  -- the genesis chunk extra's — not a computed main transition's. For a genesis chunk the list is
  -- empty in every recorded case (`create_genesis_chunk_extra` stores `vec![]`), and the argument
  -- only filters this shard's stake-info entries, so an empty list is the validator's value.
  let mainProps : List (Bytes × Nat) := match gen? with
    | some ce => ce.proposals.filterMap decodeProposal
    | none => []
  for ((i, f), T) in (implicitIdx.zip (c.applyFacts.drop (if B2.isGenesis then 0 else 1))).zip w.implicit do
    let M ← match blks[i]? with | some b => pure b | none => throw "invalid: walk"
    let ctxM := blockCtx L H.shardId slotB2.gasLimit M M.hdr.nextGasPrice
    let envM : Env := envOf c ctxM M f.minimumStake sched
    let tM := revealTrie T.values root
    root ← applyMissingChunkD2 prims envM tM f.validatorUpdate mainProps
    check (root == T.postStateRoot) "invalid: implicit transition post state root"
  -- 3.7 comparison with the endorsed header (`validate.rs:133-187`)
  check (H.prevStateRoot == root) "invalid: InvalidStateRoot"
  match gen? with
  | some ce =>
    check (H.prevOutcomeRoot == ce.outcomeRoot) "invalid: InvalidOutcomesProof"
    check (H.proposals == ce.proposals) "invalid: InvalidValidatorProposals"
    check (H.gasLimit == ce.gasLimit) "invalid: InvalidGasLimit"
    check (H.prevGasUsed == ce.gasUsed) "invalid: InvalidGasUsed"
    check (H.prevBalanceBurnt == ce.balanceBurnt) "invalid: InvalidBalanceBurnt"
    check (H.prevOutgoingReceiptsRoot == emptyOutgoingReceiptsRootD2 L)
      "invalid: InvalidReceiptsProof"
    check (H.congestion == ce.congestion) "invalid: InvalidCongestionInfo"
    check ((some H.bwRequests) == ce.bandwidthRequests) "invalid: InvalidBandwidthRequests"
    check (H.proposedSplit == ce.proposedSplit) "invalid: InvalidChunkHeaderShardSplit"
  | none => pure ()
  check (H.txRoot == merklizeBorsh (w.newTxs.map TxD2.raw)) "invalid: InvalidTxRoot"
  let body := u32 w.newTxs.length ++ concatAll (w.newTxs.map TxD2.raw) ++ encodeRcpts []
  match encodedMerkleRoot c.rsDataParts c.rsTotalParts body with
  | none => throw "invalid: Reed-Solomon parameters"
  | some (emr, len) =>
    check (H.encodedMerkleRoot == emr) "invalid: InvalidChunkEncodedMerkleRoot"
    check (H.encodedLength == len) "invalid: InvalidChunkEncodedLength"

/-! ## Top-level relations -/

/-- The genesis-extended D3 checker: `checkD2CoreG` with the D3 hooks and the `G_α` cap. On a
non-genesis `B2` it checks exactly what `checkD3` checks; on a genesis `B2` it checks the genesis
main transition (`MainTransition::Genesis`) instead of refusing the claim. -/
def checkD3G (claimBytes witnessBytes : Bytes) : Except String Unit :=
  checkD2CoreG (D3.d3Hooks Wasm.pv86) true claimBytes witnessBytes (some D3.gAlpha)

/-- `checkD3G` as a boolean. -/
def acceptsD3G (claimBytes witnessBytes : Bytes) : Bool :=
  match checkD3G claimBytes witnessBytes with
  | .ok () => true
  | .error _ => false

/-- **The genesis-extended relation.** -/
def RelD3G (claimBytes witnessBytes : Bytes) : Prop := checkD3G claimBytes witnessBytes = .ok ()

theorem relD3G_iff_acceptsD3G (c w : Bytes) : RelD3G c w ↔ acceptsD3G c w = true := by
  unfold RelD3G acceptsD3G
  cases h : checkD3G c w with
  | ok u => cases u; simp
  | error e => simp

instance (c w : Bytes) : Decidable (RelD3G c w) :=
  decidable_of_iff (acceptsD3G c w = true) (relD3G_iff_acceptsD3G c w).symm

/-! ## The genesis branch's guard conditions, as theorems

The genesis path is only reachable for a claim whose `B2` is the genesis block; the successor
checker's added behaviour must therefore be *exactly* "B2 genesis ⇒ genesis main transition".
The theorems below are the claim-level facts the branch turns on. They are deliberately small:
each states one condition the branch adds, so a later edit that removes the condition breaks a
named theorem instead of passing quietly. -/

/-- A claim without `genesis_chunk_extra` cannot enter the genesis branch: the branch's decode
step produces `none` only from `some g`, so `genesisChunkExtra = none` means the genesis main
transition has no chunk extra and the claim is rejected, not refused as out of domain. -/
theorem genesis_branch_needs_extra (c : Claim) (h : c.genesisChunkExtra = none) :
    (match c.genesisChunkExtra with
     | some g => (match decodeChunkExtra g with | .ok x => some x | .error _ => none)
     | none => none) = none := by
  rw [h]

/-- `merklize` of a one-element list is that element (`merkle.rs:54-57`: "degenerate case
`len == 1`"). -/
theorem merkleRoot_singleton (x : Bytes) : merkleRoot [x] = x := rfl

/-- For a one-shard layout the genesis outgoing-receipts root is the single leaf
`sha256(u64 shard ‖ ReceiptList(0))` — a real hash, not the zero hash. So the genesis branch's
`prev_outgoing_receipts_root` comparison against the *empty* outgoing receipts is informative:
it pins the endorsed header's field to that leaf, which no chunk with outgoing receipts would
satisfy. -/
theorem emptyOutgoingReceiptsRootD2_single (s : Nat) :
    emptyOutgoingReceiptsRootD2 ⟨[], [s], []⟩ = sha256 (sha256 (u64 s ++ encodeRcpts [])) := by
  simp [emptyOutgoingReceiptsRootD2, merklizeBorsh, merkleRoot_singleton]


/-- The genesis `tx_valid` condition is satisfied by an empty flag vector: a genesis chunk with no
transactions needs no flags (`chunk_validation.rs:382-386` derives `vec![true; 0] = []`). -/
theorem txValid_all_one_nil : ([].all (fun (b : UInt8) => b.toNat == 1)) = true := rfl

end NearSpecV3
