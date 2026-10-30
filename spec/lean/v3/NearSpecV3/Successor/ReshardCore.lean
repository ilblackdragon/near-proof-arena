import NearSpecV3.Successor.RuntimeCore
import NearSpecV3.Successor.TrieSplit
import NearSpecV3.Successor.LayoutReach

/-!
# `NearSpecV3.Successor.ReshardCore` — the validator's walk across a shard-layout boundary

`checkD2CoreWithObs` reads the whole chain segment in the *witness* epoch's layout: one slot count,
one shard index, one shard id for every block, and (for the resharding driver) a split decision taken
from the witness layout's split map alone, at every implicit block. That is the validator's walk only
while every block of the segment has the witness epoch's layout. Validator-generated split fixtures
(`docs/evidence/lean-chunk-completion/resharding-fixtures/`) showed four consequences: a child's first
chunk is excluded (`c.same_layout` in the genesis-capable prefix) or rejected (`slot count`, `shard
not in layout`), and every post-split child witness with an old-chunk implicit transition is rejected
because that transition is mistaken for a split.

This module is the resharding tiers' non-genesis checker. It follows
`get_state_witness_block_range` (`chain/chain/src/stateless_validation/chunk_validation.rs:144-253`)
position by position:

* each block is read in **its own epoch's layout** (slot count, the slot index of the shard);
* the shard id is carried through the walk with `get_prev_shard_id_from_prev_hash`
  (`chain/epoch-manager/src/adapter.rs:271-289`): at a block after which a new epoch with a different
  layout starts, a child maps to its parent;
* at such a block, before the first new chunk, `get_resharding_transition` (`:258-305`) adds a
  resharding transition for a split child, *before* the old-chunk transition of the same block;
* the main transition runs in the **main block's** layout and shard (`last_chunk_shard_layout`,
  `last_chunk_shard_id`), its receipts are taken with the per-block target shard of
  `validate_source_receipt_proofs` (`:457-524`), and each implicit transition runs in its block's
  layout with the walk position's shard (`ShardContext { shard_uid }`, `:675-700`);
* a resharding transition retains the child's half of the parent trie and replaces the congestion
  info by the child's (`get_child_congestion_info`, `chain/chain/src/resharding/manager.rs:297-383`:
  the left child keeps the parent's, the right child subtracts the parent's buffered-receipt totals
  read from the parent trie's receipt-group queues, both finalized to the child's own shard);
* the outgoing receipts of a main transition in another layout are reassigned
  (`reassign_outgoing_receipts_for_resharding`, `chain/chain/src/store/mod.rs:459-484`: the child
  with the lowest shard id gets all of them) before the outgoing-receipts root and the encoded chunk
  are computed in the witness layout (`:620-640`).

The split gate is decided: the main transition's `proposed_split` is recomputed from the claim's
split-gate fact and the pre-state trie (`TrieSplit.expectedProposedSplit`, a transcription of
`check_dynamic_resharding` and `find_trie_split`) and compared with the chunk header.

Only dynamic (V3) layout changes are decided; a V2 layout change is static resharding. Genesis
segments keep the signed genesis path and its `c.same_layout` exclusion.

## Why the remaining layout and protocol-version exclusions meet no honest PV86 claim (UQ-009)

* **V2 layout change.** `LayoutReach.no_v2_change_of_dynamic`: a layout change between two PV86 epochs
  is a `derive_v3` result when `config(86)` is dynamic, and the mainnet store's entry for 86 is
  `epoch_configs/mainnet/85.json`, which is dynamic (no `shard_layout`). V2 layouts themselves are
  decided: the parent layout of mainnet's first dynamic split is the static V2 layout of `81.json`
  (`next_next_shard_layout` keeps the previous layout while dynamic resharding is not yet enabled,
  `lib.rs:699-701`), and the fixtures' parent layout is V2 too.
* **Genesis segment with a layout change.** `LayoutReach.genesis_segment_one_layout`.
* **A PV85 (or older) epoch in a PV86 witness.** Every claim epoch must be PV86 (`c.pv86`). The
  pinned mainnet upgrade schedule has one entry, PV86 from 2026-07-20 (`core/primitives/src/
  version.rs:58-66`); before that date a 2.13.4 node votes for the next epoch's version, and from it
  for 86 (`upgrade_schedule.rs:127-158`); the voted version is adopted as soon as it holds the stake
  threshold, without intermediate steps (`chain/epoch-manager/src/lib.rs:567-579`). The previous
  release (2.12.0) had `STABLE_PROTOCOL_VERSION = 84`. So mainnet went from PV84 directly to PV86 and
  never had a PV85 epoch (archival RPC: block 207,762,733 is in a PV84 epoch with the static
  9-shard V2 layout, block 207,762,734 in a PV86 epoch with the same layout). A 2.13.4 node votes 86
  for ever after (`upgrade_schedule.rs:134-136`), so every later mainnet epoch is PV86. A PV86
  witness can reference the last PV84 epoch only when its segment reaches that epoch: the chunks at
  the start of the first PV86 epoch, which are finalized history validated by the PV84 rules for their
  main transition, not a witness the pinned binary can still be asked to validate. PV85→PV86 segments
  exist only on other networks (testnet schedules PV86 for 2026-12-31) and in the generator's local
  chains, whose genesis is PV85; they are not part of the pinned mainnet target.
-/
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2

/-- `ReshardingEventType::from_shard_layout` for a V3 layout (`event_type.rs:58-120`): the split is
`recent_split()`, the single entry `last_split ↦ last_split_children`. The V3 split map keeps every
earlier split too, so it is *not* scanned for two-child entries (that scan is the V2 rule). -/
def splitEventV3 (next : Layout) : Except String (Option SplitShardParams) :=
  match next.lastSplit with
  | none => .ok none
  | some parent =>
    match next.lastSplitChildren with
    | [_] => .ok none
    | [l, r] =>
      match next.splitBoundary l with
      | some bd => .ok (some ⟨parent, l, r, bd⟩)
      | none => .error "invalid: shard not found in shard layout"
    | _ => .error "invalid: invalid number of children in shard split map"

/-! ## The walk -/

/-- An implicit transition, as the walk pushes it (`ImplicitTransitionParams`). -/
inductive WalkTransition where
  /-- `ApplyOldChunk` of block `idx` (segment index, newest first) with the walk position's shard. -/
  | old (idx : Nat) (shard : Nat)
  /-- `Resharding` of the child `shard` with this boundary and retain mode. -/
  | split (boundary : Bytes) (mode : RetainMode) (shard : Nat)
  deriving Repr

/-- The walk's result: the main block's index, shard and layout bytes, the source blocks with their
target shards (`validate_source_receipt_proofs`' `current_target_shard_id`), the implicit transitions
oldest first, and the index of the block after which the walk stopped. -/
structure Walk where
  b2i : Nat
  mainShard : Nat
  mainLayout : Bytes
  sources : List (Nat × Nat)
  transitions : List WalkTransition
  stop : Nat

/-- The layout bytes of an epoch of the claim's epoch table. -/
def layoutBytesOf (c : Claim) (e : Bytes) : Except String Bytes :=
  match c.epochs.find? (·.epochId == e) with
  | some r => pure r.shardLayout
  | none => throw "invalid: epoch_id not in the epoch table"

def layoutOf (c : Claim) (e : Bytes) : Except String Layout := do
  decodeLayout (← layoutBytesOf c e)

/-- `get_state_witness_block_range` (`chunk_validation.rs:144-253`) over the decoded segment. Block `i`
is the walk's `prev_block`; the epoch of the block after it is `afterEpochs[i]`. -/
def walkSegment (c : Claim) (blks : List Blk) (afterEpochs : List Bytes) (shard0 : Nat) :
    Except String Walk := do
  let mut shard := shard0
  let mut seen : Nat := 0
  let mut pushed : List WalkTransition := []
  let mut sources : List (Nat × Nat) := []
  let mut main : Option (Nat × Nat × Bytes) := none
  let mut stop : Option Nat := none
  for i in List.range blks.length do
    let b ← match blks[i]? with | some b => pure b | none => throw "invalid: walk"
    let eAfter ← match afterEpochs[i]? with | some e => pure e | none => throw "invalid: walk"
    let lbAfter ← layoutBytesOf c eAfter
    let lbOwn ← layoutBytesOf c b.hdr.epochId
    let lAfter ← decodeLayout lbAfter
    let lOwn ← decodeLayout lbOwn
    check (b.slots.length == lOwn.numShards) "invalid: slot count"
    let boundary := c.epochStartAfter.getD i 0 == 1 && lbAfter != lbOwn
    if boundary then
      -- a layout change is decided only for a V3 (dynamic resharding) layout; a V2 change between
      -- PV86 epochs is unreachable under the mainnet configs (`LayoutReach.no_v2_change_of_dynamic`)
      check lAfter.lastSplit.isSome "out of domain (c.layout): V2 layout change (static resharding)"
    -- get_resharding_transition: only before the first new chunk, only at a layout boundary
    if seen == 0 && boundary then
      match ← splitEventV3 lAfter with
      | some p =>
        if p.leftChild == shard then pushed := pushed ++ [.split p.boundaryAccount .left shard]
        else if p.rightChild == shard then pushed := pushed ++ [.split p.boundaryAccount .right shard]
        else pure ()
      | none => pure ()
    -- get_prev_shard_id_from_prev_hash
    let prevShard ← if boundary then
        match lAfter.parentV3 shard with
        | some p => pure p
        | none => throw "invalid: shard not in layout"
      else pure shard
    let prevIndex ← match lOwn.index prevShard with
      | some x => pure x
      | none => throw "invalid: shard not in layout"
    let isNew := match b.slots[prevIndex]? with
      | some (s, _) => s.heightIncluded == b.hdr.height
      | none => false
    if seen == 0 then
      main := some (i, prevShard, lbOwn)
    let seen' := seen + (if isNew then 1 else 0)
    if seen' == 0 then pushed := pushed ++ [.old i shard]
    else if seen' == 1 then sources := sources ++ [(i, prevShard)]
    else
      stop := some i
      break
    if b.isGenesis then
      throw "out of domain (c.not_genesis): resharding walk reaches the genesis block"
    shard := prevShard
    seen := seen'
  -- `main` is overwritten while no chunk has been seen; its last value is the main block's.
  let some (b2i, ms, ml) := main | throw "invalid: segment has no new chunk"
  if sources.isEmpty then throw "invalid: segment has no new chunk"
  let some st := stop | throw "invalid: segment does not reach the last-but-one new chunk"
  pure { b2i, mainShard := ms, mainLayout := ml, sources, transitions := pushed.reverse, stop := st }

/-! ## The split transition's congestion (`manager.rs:297-383`) -/

/-- `ReceiptGroupsQueue::load` for every shard of the parent layout: the summed `total_gas` and
`total_size` of the queues present in the parent trie. A queue key the witness does not determine is
a missing trie value, as in the validator. -/
def parentBufferedTotals (t : PTrie) (parentLayout : Layout) : Except String (Nat × Nat) :=
  parentLayout.shardIds.foldlM (fun (acc : Nat × Nat) s => do
    match ← readKey t (nibbles (kGroupsData s)) "BufferedReceiptGroupsQueueData" with
    | none => pure acc
    | some raw =>
      match decodeMeta raw with
      | some m => pure (acc.1 + m.totalGas, acc.2 + m.totalSize)
      | none => throw (inconsistent "BufferedReceiptGroupsQueueData")) (0, 0)

/-- `get_child_congestion_info`: left keeps the parent's info; right subtracts the parent's buffered
totals (`.expect` panics on underflow, `assert_eq!` on a non-zero remainder); both are finalized to
the child's own shard (`finalize_allowed_shard` with seed = the child's index selects
`shard_ids[index]`, the child itself). -/
def childCongestion (parent : Congestion) (mode : RetainMode) (totals : Nat × Nat) (child : Nat) :
    Except String Congestion := do
  let c ← match mode with
    | .left => pure parent
    | .right =>
      if parent.bufferedGas < totals.1 then throw (panicked "Buffered gas must not exceed congestion info buffered gas")
      if parent.receiptBytes < totals.2 then throw (panicked "Buffered size must not exceed congestion info buffered size")
      let c := { parent with bufferedGas := parent.bufferedGas - totals.1,
                             receiptBytes := parent.receiptBytes - totals.2 }
      if c.bufferedGas != 0 then throw (panicked "right child keeps buffered gas")
      pure c
  pure { c with allowedShard := child }

/-! ## The checker -/

/-- The resharding tiers' non-genesis checker (see the module comment). Identical to
`checkD2CoreWithObs` on a segment whose blocks all have the witness layout, except that the split gate
is decided (recomputed) instead of excluded. -/
def checkReshardCoreObs (driver : ExecutionDriver) (hooks : ActionHooks) (allowCodes : Bool)
    (claimBytes witnessBytes : Bytes) (gasCap : Option Nat := none) : Except String Observable := do
  -- 3.1 decoding, actor checks
  let c ← (decodeClaimE claimBytes).mapError (fun e => s!"invalid claim: {e}")
  let (swBytes, codes) ←
    (if driver.compressedWitness then decodeWitnessFileV witnessBytes else decodeWitnessFile witnessBytes)
  if !allowCodes then check codes.isEmpty "out of domain (w.no_code): contract code"
  if driver.codeResponseCap then
    check (codeResponseBytes codes ≤ maxContractCodeResponseBytes)
      "out of domain (w.code_response_size): cold-fetched contract code exceeds MAX_UNCOMPRESSED_CONTRACT_CODE_RESPONSE_SIZE"
  if !driver.witnessUnbounded then
    check (lenT swBytes ≤ 8388608) "out of domain (w.size): witness larger than 8 MiB"
  let w ← driver.decodeWitness swBytes
  check (w.innerBytes == c.chunkInner) "invalid: witness chunk header differs from the claim"
  check (w.epochId == c.epochId) "invalid: epoch id"
  let H ← (decodeChunkInner c.chunkInner).mapError (fun e => s!"invalid claim: {e}")
  check (c.protocolVersion == 86) "out of domain (c.pv86)"
  -- 3.2 chain segment and epoch table
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
  let L ← decodeLayout ep.shardLayout
  for e in c.epochs do
    let l ← decodeLayout e.shardLayout
    if !driver.layoutUnbounded then
      check (1 ≤ l.numShards && l.numShards ≤ 64) "out of domain (c.layout)"
    else
      check (1 ≤ l.numShards) "out of domain (c.layout)"
  check (rsGenesisParamsOk c.rsDataParts c.rsTotalParts) "invalid: Reed-Solomon parameters"
  if !driver.segmentUnbounded then
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
  check (w.newTxs.all TxD2.sizeOk) "invalid: new transaction exceeds max_transaction_size"
  let hashes := blks.map (·.hdr.hash)
  check (hashes.headD [] == H.prevBlockHash) "invalid: segment does not start at prev_block_hash"
  check ((blks.zip (hashes.drop 1)).all fun (b, h) => b.hdr.prevHash == h)
    "invalid: segment is not hash-linked"
  -- the shard must exist in the witness epoch's layout (chunk_validation.rs:172-175)
  let _ ← match L.index H.shardId with
    | some i => pure i
    | none => throw "invalid: shard not in layout"
  check (blks.all fun b => b.slots.all fun (sl, _) => sl.heightIncluded ≤ b.hdr.height)
    "invalid: height_included above block height (block_congestion_info panics)"
  -- the walk
  let wk ← walkSegment c blks afterEpochs H.shardId
  check (wk.stop + 1 == blks.length) "invalid: segment is not exactly the blocks the validator reads"
  let B2 ← match blks[wk.b2i]? with | some b => pure b | none => throw "invalid: walk"
  check (!B2.isGenesis) "out of domain (c.not_genesis)"
  check c.genesisChunkExtra.isNone "invalid: genesis_chunk_extra for a non-genesis main block"
  let Lmain ← decodeLayout wk.mainLayout
  let mainIdx ← match Lmain.index wk.mainShard with
    | some i => pure i
    | none => throw "invalid: shard not in layout"
  let oldIdx := wk.transitions.filterMap fun t => match t with | .old i _ => some i | _ => none
  check (c.applyFacts.length == 1 + oldIdx.length) "invalid: apply_facts length"
  let appliedIdx := wk.b2i :: oldIdx
  check ((appliedIdx.zip c.applyFacts).all fun (i, f) =>
      f.validatorUpdate.isSome == (c.epochStartAfter.getD (i + 1) 0 == 1))
    "invalid: validator_update does not match the epoch start"
  let prevB2 ← match blks[wk.b2i + 1]? with | some b => pure b | none => throw "invalid: walk"
  let slotB2 ← match B2.slots[mainIdx]? with | some p => pure p.2 | none => throw "invalid: slot"
  -- 3.3 / 3.4 source receipts (validate_source_receipt_proofs, chunk_validation.rs:457-524)
  let mut receipts : List Rcpt := []
  let mut used : Nat := 0
  for (j, target) in wk.sources do
    let S ← match blks[j]? with | some b => pure b | none => throw "invalid: walk"
    let mut proofs : List EntryD2 := []
    for (s, ci) in S.slots do
      if s.heightIncluded == S.hdr.height then
        let key := chunkHash s.inner ci.encodedMerkleRoot
        let e ← match lookupLastD2 key w.entries with
          | some e => pure e
          | none => throw "invalid: missing source receipt proof"
        driver.validateRouting Lmain e.receipts
        check (e.proof.fromShard == ci.shardId) "invalid: receipt proof from_shard_id"
        check (e.proof.toShard == target) "invalid: receipt proof to_shard_id"
        check (verifyReceiptProofD2 ci.prevOutgoingReceiptsRoot e) "invalid: receipt proof merkle path"
        proofs := proofs ++ [e]
        used := used + 1
    let shuffled ← match shuffleWithSeed proofs S.hdr.prevHash with
      | some p => pure p
      | none => throw "invalid: shuffle fuel exhausted (probability < 2^-1024)"
    receipts := receipts ++
      (shuffled.map fun e => e.receipts.filter fun r => driver.receiptShard Lmain r == wk.mainShard).flatten
  check ((distinctKeysD2 w.entries).length == used) "invalid: source_receipt_proofs contains extra proofs"
  check (sha256 (encodeRcpts receipts) == w.appliedReceiptsHash) "invalid: applied receipts hash"
  -- steps 8, 9: transactions of the last new chunk and their validity flags
  check (merklizeBorsh (w.txs.map TxD2.raw) == slotB2.txRoot) "invalid: transaction root of the last chunk"
  check (c.txValid.length == w.txs.length) "invalid: tx_valid length"
  -- 3.5 main transition, in the main block's layout and shard
  let schedOf (l : Layout) : Except String Scheduler.Params :=
    match Scheduler.Params.calculate Scheduler.Config.pv86 l.numShards with
    | some p => pure p
    | none => throw "invalid: bandwidth scheduler params (assert panics)"
  let sched ← schedOf Lmain
  let facts0 := c.applyFacts.headD ⟨none, 0, none⟩
  let ctxB2 := blockCtx Lmain wk.mainShard slotB2.gasLimit B2 prevB2.hdr.nextGasPrice
  let merged := w.main.values ++ codes
  let store := mkHStore merged
  let env : Env := { envOf c ctxB2 B2 facts0.minimumStake sched with
                     store := store, preRoot := slotB2.prevStateRoot }
  let tMain := revealAll store revealFuel slotB2.prevStateRoot
  check (tMain.hashOf == slotB2.prevStateRoot) "invalid: main base_state does not hash to prev_state_root"
  -- the split gate (compute_proposed_split runs on the pre-state trie, runtime/mod.rs:284-292)
  let proposed ← TrieSplit.expectedProposedSplit facts0.splitGate Lmain.numShards wk.mainShard tMain
    (slotB2.prevStateRoot == NearSpecV3.D2.emptyRoot)
  let lastProps := slotB2.proposals.filterMap decodeProposal
  let out ← driver.apply hooks prims env tMain facts0.validatorUpdate lastProps receipts
    (w.txs.zip (c.txValid.map (· != 0))) slotB2.congestion
  let baseBytes := (merged.map List.length).foldl (· + ·) 0
  check (driver.sizeOk baseBytes out.cdRemovals)
    "out of domain (w.size): storage-proof upper bound may exceed main_storage_proof_size_soft_limit"
  if let some cap := gasCap then
    check (out.wasmGas ≤ cap) s!"out of domain (e.g_alpha): chunk function-call gas {out.wasmGas} > G_α {cap}"
  let mut root := out.root
  let mut congestion := out.congestion
  check (driver.blindOutputs || root == w.main.postStateRoot) "invalid: main transition post state root"
  -- 3.6 implicit transitions, oldest first
  check (w.implicit.length == wk.transitions.length) "invalid: implicit transitions count"
  let mainProps := out.proposals.map fun p => (p.acct, p.stake)
  let mut facts := c.applyFacts.drop 1
  for (tr, T) in wk.transitions.zip w.implicit do
    let tT := revealTrie T.values root
    match tr with
    | .old i shard =>
      let f ← match facts with | f :: _ => pure f | [] => throw "invalid: apply_facts length"
      facts := facts.drop 1
      let M ← match blks[i]? with | some b => pure b | none => throw "invalid: walk"
      let lM ← layoutOf c M.hdr.epochId
      let ctxM := blockCtx lM shard slotB2.gasLimit M M.hdr.nextGasPrice
      let envM : Env := envOf c ctxM M f.minimumStake (← schedOf lM)
      root ← applyMissingChunkD2 prims envM tT f.validatorUpdate mainProps
    | .split bd mode shard =>
      -- parent layout: the main block's epoch; child layout: the witness epoch's
      -- (`chunk_validation.rs:711-727`)
      let totals ← match mode with
        | .left => pure (0, 0)
        | .right => parentBufferedTotals tT Lmain
      congestion ← childCongestion congestion mode totals shard
      let _ ← match L.index shard with
        | some x => pure x
        | none => throw "invalid: shard not in layout"
      root ← splitRootE tT bd mode
    check (driver.blindOutputs || root == T.postStateRoot) "invalid: implicit transition post state root"
  -- outgoing receipts, reassigned to the witness layout (chunk_validation.rs:620-640)
  let outgoing ← if wk.mainLayout == ep.shardLayout then pure out.outgoing else
    match L.childrenV3 wk.mainShard with
    | some ch =>
      if ch.foldl Nat.min (ch.headD 0) == H.shardId then pure out.outgoing else pure []
    | none => throw "invalid: InvalidSplitShardsIds"
  -- 3.7 comparison with the endorsed header
  check (driver.blindOutputs || H.prevStateRoot == root) "invalid: InvalidStateRoot"
  check (driver.blindOutputs || H.prevOutcomeRoot == outcomeRootD1 out.outcomes) "invalid: InvalidOutcomesProof"
  check (driver.blindOutputs || H.proposals == out.proposals.map Proposal.encode) "invalid: InvalidValidatorProposals"
  check (H.gasLimit == slotB2.gasLimit) "invalid: InvalidGasLimit"
  check (driver.blindOutputs || H.prevGasUsed == out.gasUsed) "invalid: InvalidGasUsed"
  check (driver.blindOutputs || H.prevBalanceBurnt == out.balanceBurnt) "invalid: InvalidBalanceBurnt"
  check (driver.blindOutputs || H.prevOutgoingReceiptsRoot == driver.outgoingRoot L outgoing) "invalid: InvalidReceiptsProof"
  check (driver.blindOutputs || H.congestion == congestion) "invalid: InvalidCongestionInfo"
  check (driver.blindOutputs || H.bwRequests == out.bwRequests) "invalid: InvalidBandwidthRequests"
  check (H.proposedSplit == proposed) "invalid: InvalidChunkHeaderShardSplit"
  check (H.txRoot == merklizeBorsh (w.newTxs.map TxD2.raw)) "invalid: InvalidTxRoot"
  let body := u32 w.newTxs.length ++ concatAll (w.newTxs.map TxD2.raw) ++ encodeRcpts outgoing
  match encodedMerkleRoot c.rsDataParts c.rsTotalParts body with
  | none => throw "invalid: Reed-Solomon parameters"
  | some (emr, len) =>
    check (driver.blindOutputs || H.encodedMerkleRoot == emr) "invalid: InvalidChunkEncodedMerkleRoot"
    check (driver.blindOutputs || H.encodedLength == len) "invalid: InvalidChunkEncodedLength"
    return { stateRoot := root
             outcomeRoot := outcomeRootD1 out.outcomes
             gasBurnt := out.gasUsed
             balanceBurnt := out.balanceBurnt
             outgoingReceiptsRoot := driver.outgoingRoot L outgoing
             proposals := out.proposals.map Proposal.encode
             txRoot := merklizeBorsh (w.newTxs.map TxD2.raw)
             encodedMerkleRoot := emr
             encodedLength := len
             congestion := congestion
             bwRequests := out.bwRequests
             logs := out.outcomes.map (fun o => o.logs) |>.flatten
             receiptCount := outgoing.length
             wasmGas := out.wasmGas
             outcomes := out.outcomes
             outgoing := outgoing
             stateChanges := out.committed
             computeUsage := out.compute
             detail := out.detail }

def checkReshardCore (driver : ExecutionDriver) (hooks : ActionHooks) (allowCodes : Bool)
    (claimBytes witnessBytes : Bytes) (gasCap : Option Nat := none) : Except String Unit :=
  (checkReshardCoreObs driver hooks allowCodes claimBytes witnessBytes gasCap).map fun _ => ()

/-- Whether the claim's segment contains a genesis block (then the genesis-capable signed path, with
its `c.same_layout` exclusion, decides it). Undecodable claims go to the signed path too, which
reports the decoding error. -/
def segmentHasGenesis (claimBytes : Bytes) : Bool :=
  match decodeClaimE claimBytes with
  | .ok c => match c.blocks.mapM decodeBlk with
    | .ok blks => blks.any (·.isGenesis)
    | .error _ => true
  | .error _ => true

end NearSpecV3.Successor

namespace NearSpecV3.Successor.ReshardCoreTest
open NearSpecV3 NearSpecV3.Successor

/-- A V3 layout after two splits: parent 4 split into 2 and 3 earlier, parent 3 now into 5 and 6. The
split map keeps both entries; the latest split is `last_split = 3`. -/
def twoSplitLayout : Layout :=
  { boundaries := [[98], [109], [120]], shardIds := [1, 2, 5, 6],
    idToIndex := [(1, 0), (2, 1), (5, 2), (6, 3)],
    splitMap := [(3, [5, 6]), (4, [2, 3])], lastSplit := some 3,
    ancestorMap := [(2, [1, 4]), (5, [3, 4]), (6, [3, 4])] }

/-- `recent_split()` only: the earlier split's two-child entry is history, not a second split. -/
example : (match splitEventV3 twoSplitLayout with
    | .ok (some p) => p.parentShard == 3 && p.leftChild == 5 && p.rightChild == 6 && p.boundaryAccount == [120]
    | _ => false) = true := by decide

/-- Children and parents follow `ShardLayoutV3` (`v3.rs:330-354`). -/
example : twoSplitLayout.childrenV3 3 = some [5, 6] := by decide
example : twoSplitLayout.childrenV3 1 = some [1] := by decide
example : twoSplitLayout.childrenV3 4 = none := by decide
example : twoSplitLayout.parentV3 6 = some 3 := by decide
example : twoSplitLayout.parentV3 2 = some 2 := by decide
example : twoSplitLayout.parentV3 3 = none := by decide

/-- `find_middle_child`: the first child crossing the threshold, else the last non-empty child. -/
example : TrieSplit.findMiddleChild ([10, 0, 30] ++ List.replicate 13 0) 15 = some (2, 10) := by decide
example : TrieSplit.findMiddleChild ([10, 0, 30] ++ List.replicate 13 0) 100 = some (2, 10) := by decide
example : TrieSplit.findMiddleChild (List.replicate 16 0) 0 = none := by decide

end NearSpecV3.Successor.ReshardCoreTest
