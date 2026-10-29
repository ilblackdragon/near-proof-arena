import NearSpecV3.ChunkValidationD1
import NearSpecV3.ChunkValidationD1Out

/-!
# `NearSpecV3.D0SubD1.Work.Root.Phases` — the two checkers, cut into five phases each

`checkD0` and `checkD1CoreObs` are ~90-statement `Except String` do-blocks that are almost
line-for-line the same.  This module cuts *each* of them at five statement boundaries

| cut | after statement | D0 | D1 |
|---|---|---|---|
| A | claim + witness file + the two size gates | 5 | 5 |
| B | witness decode, header/epoch checks, chunk inner, layout | 22 | 23 |
| C | the chain walk and the source-receipt loop | 52 | 51 |
| D | the main transition | 67 | 66 |
| E | the rest (implicit transitions, header comparison, RS body) | 90 | 90 |

and emits, for each slice, a *continuation-passing* phase

`def d0Pj <free variables of slice j> (k : <free variables of the remainder → Except String Unit)`,
whose body is the **verbatim** slice followed by `k` applied to the values the remainder reads.
The phase's parameters are exactly the free variables of its slice and its continuation receives
exactly the free variables of the rest of the program — the *same name list in both checkers*,
because the two slices bind the same names (`PAR[j]` below is literally shared).

The continuations are built once, from the tail backwards

* `d0K3` = `d0PE` (nothing left), `d0K2` = `d0PD d0K3`, `d0K1` = `d0PC d0K2`, `d0K0` = `d0PB d0K1`;
* `d1K3` = `d1PE` (the observable is the answer), `d1K2` = `d1PD d1K3`, …,

which makes the chain identities **definitional** (`d0_chain`, `d1_chain`): no case analysis and
no rewriting of the checkers, only `rfl`.

With that, each phase is an independent simulation lemma of the form

*incoming values related by `r`, and continuations that agree on `r`-related outgoing values ⟹
D1's phase succeeds on `r`-related values whenever D0's phase does.*

`Phases/A … Phases/E` prove one such lemma each, and `Root` composes them along the chain.
-/

namespace NearSpecV3.D0SubD1.Work.Root

open NearSpec NearSpecV3

set_option maxHeartbeats 0
set_option linter.unusedVariables false


/-- D0 phase A: the statements of the 1-th slice, then `k`. -/

def d0PA (cb : Bytes) (wb : Bytes) (k : Claim → Bytes → Except String Unit) : Except String Unit := do
  let c ← (decodeClaimE cb).mapError (fun e => s!"invalid claim: {e}")
  let (swBytes, codes) ← decodeWitnessFile wb
  check codes.isEmpty "out of domain (w.no_code): contract code"
  check (lenT swBytes ≤ 8388608) "out of domain (w.size): witness larger than 8 MiB"
  k c swBytes


/-- D0 phase B: the statements of the 2-th slice, then `k`. -/

def d0PB (c : Claim) (swBytes : Bytes) (k : Claim → StateWitness → ChunkInner → Layout → Except String Unit) : Except String Unit := do
  let w ← decodeStateWitness swBytes
  check (w.innerBytes == c.chunkInner) "invalid: witness chunk header differs from the claim"
  check (w.epochId == c.epochId) "invalid: epoch id"
  let H ← (decodeChunkInner c.chunkInner).mapError (fun e => s!"invalid claim: {e}")
  -- claim-level D0 conditions and trusted-fact consistency
  check (c.protocolVersion == 86) "out of domain (c.pv86)"
  check (c.epochs.length == 1) "out of domain (c.single_epoch): more than one epoch"
  let ep := c.epochs.headD ⟨[], 0, 0, [], []⟩
  check (ep.epochId == c.epochId && ep.protocolVersion == c.protocolVersion)
    "invalid: epoch table does not match epoch_id / protocol_version"
  let L ← decodeLayout ep.shardLayout
  check (1 ≤ L.numShards && L.numShards ≤ 64) "out of domain (c.layout)"
  check (rsGenesisParamsOk c.rsDataParts c.rsTotalParts) "invalid: Reed-Solomon parameters"
  check (c.blocks.length ≤ 32) "out of domain (c.segment)"
  check (c.txValid.isEmpty) "out of domain (c.no_tx_flags)"
  check (c.epochStartAfter.length == c.blocks.length) "invalid: epoch_start_after length"
  check (c.epochStartAfter.all (· == 0)) "out of domain (c.single_epoch): epoch start"
  check (c.applyFacts.all fun f => f.validatorUpdate.isNone && f.splitGate.isNone)
    "out of domain (c.no_split_gate)"
  k c w H L


/-- D0 phase C: the statements of the 3-th slice, then `k`. -/

def d0PC (c : Claim) (w : StateWitness) (H : ChunkInner) (L : Layout) (k : Claim → StateWitness → ChunkInner → Layout → Nat → Blk → Blk → ChunkInner → List Blk → List Receipt → Except String Unit) : Except String Unit := do
  -- 3.2 chain segment: hashes, slots, walk
  let blks ← c.blocks.mapM decodeBlk
  check (!blks.isEmpty) "invalid: empty chain segment"
  check (blks.all fun b => b.hdr.epochId == c.epochId) "out of domain (c.single_epoch)"
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
  -- walk (chunk_validation.rs:144-253): implicit blocks before the first new chunk, then
  -- B2 (last new chunk), source blocks B2.., stop at B1 (the last-but-one new chunk)
  let b2i ← match blks.findIdx? isNew with
    | some i => pure i
    | none => throw "invalid: segment has no new chunk"
  let B2 ← match blks[b2i]? with | some b => pure b | none => throw "invalid: walk"
  check (!B2.isGenesis) "out of domain (c.not_genesis)"
  check c.genesisChunkExtra.isNone "invalid: genesis_chunk_extra for a non-genesis main block"
  let stop ← match (blks.drop (b2i + 1)).findIdx? isNew with
    | some j => pure (b2i + 1 + j)
    | none => throw "invalid: segment does not reach the last-but-one new chunk"
  check (stop + 1 == blks.length) "invalid: segment is not exactly the blocks the validator reads"
  let implicitBlks := (blks.take b2i).reverse                    -- oldest first
  let sourceBlks := (blks.drop b2i).take (stop - b2i)           -- newest first
  check (c.applyFacts.length == 1 + implicitBlks.length) "invalid: apply_facts length"
  let prevB2 ← match blks[b2i + 1]? with | some b => pure b | none => throw "invalid: walk"
  let slotB2 ← match B2.slots[idx]? with | some p => pure p.2 | none => throw "invalid: slot"
  -- 3.3 / 3.4 pre-validation: source receipts
  let mut receipts : List Receipt := []
  let mut used : Nat := 0
  for S in sourceBlks do
    let mut proofs : List ProofEntry := []
    for (s, ci) in S.slots do
      if s.heightIncluded == S.hdr.height then
        let key := chunkHash s.inner ci.encodedMerkleRoot
        let e ← match lookupLast key w.entries with
          | some e => pure e
          | none => throw "invalid: missing source receipt proof"
        check (e.proof.fromShard == ci.shardId) "invalid: receipt proof from_shard_id"
        check (e.proof.toShard == H.shardId) "invalid: receipt proof to_shard_id"
        check (verifyReceiptProof ci.prevOutgoingReceiptsRoot e) "invalid: receipt proof merkle path"
        proofs := proofs ++ [e]
        used := used + 1
    let shuffled ← match shuffleWithSeed proofs S.hdr.prevHash with
      | some p => pure p
      | none => throw "invalid: shuffle fuel exhausted (probability < 2^-1024)"
    -- filter_incoming_receipts_for_shard (store/mod.rs:252-273): keep receipts routed to the
    -- target shard under the (final) layout; proofs are never dropped
    receipts := receipts ++
      (shuffled.map fun e => e.receipts.filter fun r => L.shardOf r.receiverId == H.shardId).flatten
  check ((distinctKeys w.entries).length == used) "invalid: source_receipt_proofs contains extra proofs"
  check (sha256 (encodeReceipts receipts) == w.appliedReceiptsHash) "invalid: applied receipts hash"
  k c w H L idx B2 prevB2 slotB2 implicitBlks receipts


/-- D0 phase D: the statements of the 4-th slice, then `k`. -/

def d0PD (c : Claim) (w : StateWitness) (H : ChunkInner) (L : Layout) (idx : Nat) (B2 : Blk) (prevB2 : Blk) (slotB2 : ChunkInner) (implicitBlks : List Blk) (receipts : List Receipt) (k : Claim → StateWitness → ChunkInner → Layout → Nat → Blk → ChunkInner → List Blk → List Receipt → MainOut → Congestion → Except String Unit) : Except String Unit := do
  check (slotB2.txRoot == zeroHash32) "invalid: transaction root of the last chunk"
  -- D0 witness-level conditions
  check (decide (receipts.map Receipt.receiptId).Nodup) "out of domain (e.distinct_ids)"
  let baseBytes := (w.main.values.map List.length).foldl (· + ·) 0
  check (baseBytes ≤ 3000000) "out of domain (w.size): base_state larger than 3 MB"
  let own := slotB2.congestion
  check (own.delayedGas == 0 && own.bufferedGas == 0 && own.receiptBytes == 0)
    "out of domain (c.own_congestion_zero)"
  -- 3.5 main transition
  let ctxB2 := blockCtx L H.shardId slotB2.gasLimit B2 prevB2.hdr.nextGasPrice
  -- reveal paths: first pass for indices, then everything the D0 run reads
  let t0 := partialTrie w.main.values slotB2.prevStateRoot [keyBufferedIdx]
  let bshards ← match t0.find keyBufferedIdx with
    | some v => (bufferedShards v).mapError id
    | none => throw "invalid: MissingTrieValue (BufferedReceiptIndices)"
  let tMain := partialTrie w.main.values slotB2.prevStateRoot (mainKeys receipts bshards)
  check (tMain.hashOf == slotB2.prevStateRoot) "invalid: main base_state does not hash to prev_state_root"
  let out ← applyNewChunk prims ctxB2 tMain receipts
  k c w H L idx B2 slotB2 implicitBlks receipts out own


/-- D0 phase E: the statements of the 5-th slice, then `k`. -/

def d0PE (c : Claim) (w : StateWitness) (H : ChunkInner) (L : Layout) (idx : Nat) (B2 : Blk) (slotB2 : ChunkInner) (implicitBlks : List Blk) (receipts : List Receipt) (out : MainOut) (own : Congestion) : Except String Unit := do
  let mut root := out.trie.hashOf
  check (root == w.main.postStateRoot) "invalid: main transition post state root"
  -- 3.6 implicit transitions
  check (w.implicit.length == implicitBlks.length) "invalid: implicit transitions count"
  for (M, T) in implicitBlks.zip w.implicit do
    let ctxM := blockCtx L H.shardId slotB2.gasLimit M M.hdr.nextGasPrice
    let tM := partialTrie T.values root [keyDelayedIdx, keyBwState]
    let tM' ← applyMissingChunk prims ctxM tM
    root := tM'.hashOf
    check (root == T.postStateRoot) "invalid: implicit transition post state root"
  -- 3.7 comparison with the endorsed header
  let allowed := L.shardIds.getD ((B2.hdr.height + idx) % L.numShards) H.shardId
  let ownCongestion : Congestion := { own with allowedShard := allowed }
  check (H.prevStateRoot == root) "invalid: InvalidStateRoot"
  check (H.prevOutcomeRoot == outcomeRoot out.outcomes) "invalid: InvalidOutcomesProof"
  check H.proposals.isEmpty "invalid: InvalidValidatorProposals"
  check (H.gasLimit == slotB2.gasLimit) "invalid: InvalidGasLimit"
  check (H.prevGasUsed == out.gasUsed) "invalid: InvalidGasUsed"
  check (H.prevBalanceBurnt == out.tokensBurnt) "invalid: InvalidBalanceBurnt"
  check (H.prevOutgoingReceiptsRoot == outgoingReceiptsRoot L out.outgoing) "invalid: InvalidReceiptsProof"
  check (H.congestion == ownCongestion) "invalid: InvalidCongestionInfo"
  check H.bwRequests.isEmpty "invalid: InvalidBandwidthRequests"
  check H.proposedSplit.isNone "invalid: InvalidChunkHeaderShardSplit"
  check (H.txRoot == zeroHash32) "invalid: InvalidTxRoot"
  let body := u32 0 ++ encodeReceipts out.outgoing     -- borsh((Vec<SignedTransaction> = [], outgoing))
  match encodedMerkleRoot c.rsDataParts c.rsTotalParts body with
  | none => throw "invalid: Reed-Solomon parameters"
  | some (emr, len) =>
    check (H.encodedMerkleRoot == emr) "invalid: InvalidChunkEncodedMerkleRoot"
    check (H.encodedLength == len) "invalid: InvalidChunkEncodedLength"


/-- D1 phase A: the matching slice of `checkD1CoreObs`. -/

def d1PA (cb : Bytes) (wb : Bytes) (k : Claim → Bytes → Except String Observable) : Except String Observable := do
  let c ← (decodeClaimE cb).mapError (fun e => s!"invalid claim: {e}")
  let (swBytes, codes) ← decodeWitnessFile wb
  check codes.isEmpty "out of domain (w.no_code): contract code"
  check (lenT swBytes ≤ 8388608) "out of domain (w.size): witness larger than 8 MiB"
  k c swBytes


/-- D1 phase B: the matching slice of `checkD1CoreObs`. -/

def d1PB (c : Claim) (swBytes : Bytes) (k : Claim → StateWitnessD1 → ChunkInner → Layout → Except String Observable) : Except String Observable := do
  let w ← decodeStateWitnessD1 swBytes
  check (w.innerBytes == c.chunkInner) "invalid: witness chunk header differs from the claim"
  check (w.epochId == c.epochId) "invalid: epoch id"
  let H ← (decodeChunkInner c.chunkInner).mapError (fun e => s!"invalid claim: {e}")
  -- claim-level conditions and trusted-fact consistency (as D0, minus c.no_tx_flags)
  check (c.protocolVersion == 86) "out of domain (c.pv86)"
  check (c.epochs.length == 1) "out of domain (c.single_epoch): more than one epoch"
  let ep := c.epochs.headD ⟨[], 0, 0, [], []⟩
  check (ep.epochId == c.epochId && ep.protocolVersion == c.protocolVersion)
    "invalid: epoch table does not match epoch_id / protocol_version"
  let L ← decodeLayout ep.shardLayout
  check (1 ≤ L.numShards && L.numShards ≤ 64) "out of domain (c.layout)"
  check (rsGenesisParamsOk c.rsDataParts c.rsTotalParts) "invalid: Reed-Solomon parameters"
  check (c.blocks.length ≤ 32) "out of domain (c.segment)"
  check (c.epochStartAfter.length == c.blocks.length) "invalid: epoch_start_after length"
  check (c.epochStartAfter.all (· == 0)) "out of domain (c.single_epoch): epoch start"
  check (c.applyFacts.all fun f => f.validatorUpdate.isNone && f.splitGate.isNone)
    "out of domain (c.no_split_gate)"
  -- step 6: check_valid_for_config on new_transactions (size gate; no signature check)
  check (w.newTxs.all Tx.sizeOk) "invalid: new transaction exceeds max_transaction_size"
  k c w H L


/-- D1 phase C: the matching slice of `checkD1CoreObs`. -/

def d1PC (c : Claim) (w : StateWitnessD1) (H : ChunkInner) (L : Layout) (k : Claim → StateWitnessD1 → ChunkInner → Layout → Nat → Blk → Blk → ChunkInner → List Blk → List Receipt → Except String Observable) : Except String Observable := do
  -- 3.2 chain segment: hashes, slots, walk
  let blks ← c.blocks.mapM decodeBlk
  check (!blks.isEmpty) "invalid: empty chain segment"
  check (blks.all fun b => b.hdr.epochId == c.epochId) "out of domain (c.single_epoch)"
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
  check (!B2.isGenesis) "out of domain (c.not_genesis)"
  check c.genesisChunkExtra.isNone "invalid: genesis_chunk_extra for a non-genesis main block"
  let stop ← match (blks.drop (b2i + 1)).findIdx? isNew with
    | some j => pure (b2i + 1 + j)
    | none => throw "invalid: segment does not reach the last-but-one new chunk"
  check (stop + 1 == blks.length) "invalid: segment is not exactly the blocks the validator reads"
  let implicitBlks := (blks.take b2i).reverse
  let sourceBlks := (blks.drop b2i).take (stop - b2i)
  check (c.applyFacts.length == 1 + implicitBlks.length) "invalid: apply_facts length"
  let prevB2 ← match blks[b2i + 1]? with | some b => pure b | none => throw "invalid: walk"
  let slotB2 ← match B2.slots[idx]? with | some p => pure p.2 | none => throw "invalid: slot"
  -- 3.3 / 3.4 pre-validation: source receipts
  let mut receipts : List Receipt := []
  let mut used : Nat := 0
  for S in sourceBlks do
    let mut proofs : List ProofEntry := []
    for (s, ci) in S.slots do
      if s.heightIncluded == S.hdr.height then
        let key := chunkHash s.inner ci.encodedMerkleRoot
        let e ← match lookupLast key w.entries with
          | some e => pure e
          | none => throw "invalid: missing source receipt proof"
        check (e.proof.fromShard == ci.shardId) "invalid: receipt proof from_shard_id"
        check (e.proof.toShard == H.shardId) "invalid: receipt proof to_shard_id"
        check (verifyReceiptProof ci.prevOutgoingReceiptsRoot e) "invalid: receipt proof merkle path"
        proofs := proofs ++ [e]
        used := used + 1
    let shuffled ← match shuffleWithSeed proofs S.hdr.prevHash with
      | some p => pure p
      | none => throw "invalid: shuffle fuel exhausted (probability < 2^-1024)"
    receipts := receipts ++
      (shuffled.map fun e => e.receipts.filter fun r => L.shardOf r.receiverId == H.shardId).flatten
  check ((distinctKeys w.entries).length == used) "invalid: source_receipt_proofs contains extra proofs"
  check (sha256 (encodeReceipts receipts) == w.appliedReceiptsHash) "invalid: applied receipts hash"
  k c w H L idx B2 prevB2 slotB2 implicitBlks receipts


/-- D1 phase D: the matching slice of `checkD1CoreObs`. -/

def d1PD (c : Claim) (w : StateWitnessD1) (H : ChunkInner) (L : Layout) (idx : Nat) (B2 : Blk) (prevB2 : Blk) (slotB2 : ChunkInner) (implicitBlks : List Blk) (receipts : List Receipt) (k : Claim → StateWitnessD1 → ChunkInner → Layout → Nat → Blk → ChunkInner → List Blk → List Receipt → MainOutD1 → Congestion → Except String Observable) : Except String Observable := do
  -- steps 8, 9: transactions of the last new chunk and their validity flags
  check (merklizeBorsh (w.txs.map Tx.raw) == slotB2.txRoot) "invalid: transaction root of the last chunk"
  check (c.txValid.length == w.txs.length) "invalid: tx_valid length"
  -- witness-level domain conditions
  let baseBytes := (w.main.values.map List.length).foldl (· + ·) 0
  check (baseBytes ≤ 3000000) "out of domain (w.size): base_state larger than 3 MB"
  let own := slotB2.congestion
  check (own.delayedGas == 0 && own.bufferedGas == 0 && own.receiptBytes == 0)
    "out of domain (c.own_congestion_zero)"
  -- 3.5 main transition
  let ctxB2 := blockCtx L H.shardId slotB2.gasLimit B2 prevB2.hdr.nextGasPrice
  let t0 := partialTrie w.main.values slotB2.prevStateRoot [keyBufferedIdx]
  let bshards ← match t0.find keyBufferedIdx with
    | some v => (bufferedShards v).mapError id
    | none => throw "invalid: MissingTrieValue (BufferedReceiptIndices)"
  let tMain := partialTrie w.main.values slotB2.prevStateRoot
    (mainKeys receipts bshards ++ txKeys w.txs)
  check (tMain.hashOf == slotB2.prevStateRoot) "invalid: main base_state does not hash to prev_state_root"
  let out ← applyNewChunkD1 prims ctxB2 tMain receipts (w.txs.zip (c.txValid.map (· != 0)))
  k c w H L idx B2 slotB2 implicitBlks receipts out own


/-- D1 phase E: the matching slice of `checkD1CoreObs`. -/

def d1PE (c : Claim) (w : StateWitnessD1) (H : ChunkInner) (L : Layout) (idx : Nat) (B2 : Blk) (slotB2 : ChunkInner) (implicitBlks : List Blk) (receipts : List Receipt) (out : MainOutD1) (own : Congestion) : Except String Observable := do
  check (decide (out.localIds ++ receipts.map Receipt.receiptId).Nodup) "out of domain (e.distinct_ids)"
  let mut root := out.trie.hashOf
  check (root == w.main.postStateRoot) "invalid: main transition post state root"
  -- 3.6 implicit transitions
  check (w.implicit.length == implicitBlks.length) "invalid: implicit transitions count"
  for (M, T) in implicitBlks.zip w.implicit do
    let ctxM := blockCtx L H.shardId slotB2.gasLimit M M.hdr.nextGasPrice
    let tM := partialTrie T.values root [keyDelayedIdx, keyBwState]
    let tM' ← applyMissingChunk prims ctxM tM
    root := tM'.hashOf
    check (root == T.postStateRoot) "invalid: implicit transition post state root"
  -- 3.7 comparison with the endorsed header
  let allowed := L.shardIds.getD ((B2.hdr.height + idx) % L.numShards) H.shardId
  let ownCongestion : Congestion := { own with allowedShard := allowed }
  check (H.prevStateRoot == root) "invalid: InvalidStateRoot"
  check (H.prevOutcomeRoot == outcomeRootD1 out.outcomes) "invalid: InvalidOutcomesProof"
  check H.proposals.isEmpty "invalid: InvalidValidatorProposals"
  check (H.gasLimit == slotB2.gasLimit) "invalid: InvalidGasLimit"
  check (H.prevGasUsed == out.gasUsed) "invalid: InvalidGasUsed"
  check (H.prevBalanceBurnt == out.tokensBurnt) "invalid: InvalidBalanceBurnt"
  check (H.prevOutgoingReceiptsRoot == outgoingReceiptsRoot L out.outgoing) "invalid: InvalidReceiptsProof"
  check (H.congestion == ownCongestion) "invalid: InvalidCongestionInfo"
  check H.bwRequests.isEmpty "invalid: InvalidBandwidthRequests"
  check H.proposedSplit.isNone "invalid: InvalidChunkHeaderShardSplit"
  check (H.txRoot == merklizeBorsh (w.newTxs.map Tx.raw)) "invalid: InvalidTxRoot"
  let body := u32 w.newTxs.length ++ concatAll (w.newTxs.map Tx.raw) ++ encodeReceipts out.outgoing
  match encodedMerkleRoot c.rsDataParts c.rsTotalParts body with
  | none => throw "invalid: Reed-Solomon parameters"
  | some (emr, len) =>
    check (H.encodedMerkleRoot == emr) "invalid: InvalidChunkEncodedMerkleRoot"
    check (H.encodedLength == len) "invalid: InvalidChunkEncodedLength"
    -- The consensus outputs this checker computed and compared against the endorsed header. The
    -- comparison block above tests exactly these expressions (`root`, `out.*`, `ownCongestion`,
    -- `merklizeBorsh …`, and this arm's `emr`/`len`); the two empty-list fields are what D1 verifies
    -- the header's lists to be. See `NearSpecV3.ChunkValidationD1Out` for the projection theorems.
    return d1Outputs root out.outcomes out.gasUsed out.tokensBurnt L out.outgoing
      (merklizeBorsh (w.newTxs.map Tx.raw)) emr len ownCongestion


/-! ## The continuations (built once, from the tail backwards) -/


def d0K3 (c : Claim) (w : StateWitness) (H : ChunkInner) (L : Layout) (idx : Nat) (B2 : Blk) (slotB2 : ChunkInner) (implicitBlks : List Blk) (receipts : List Receipt) (out : MainOut) (own : Congestion) : Except String Unit :=
  d0PE c w H L idx B2 slotB2 implicitBlks receipts out own

def d1K3 (c : Claim) (w : StateWitnessD1) (H : ChunkInner) (L : Layout) (idx : Nat) (B2 : Blk) (slotB2 : ChunkInner) (implicitBlks : List Blk) (receipts : List Receipt) (out : MainOutD1) (own : Congestion) : Except String Observable :=
  d1PE c w H L idx B2 slotB2 implicitBlks receipts out own

def d0K2 (c : Claim) (w : StateWitness) (H : ChunkInner) (L : Layout) (idx : Nat) (B2 : Blk) (prevB2 : Blk) (slotB2 : ChunkInner) (implicitBlks : List Blk) (receipts : List Receipt) : Except String Unit :=
  d0PD c w H L idx B2 prevB2 slotB2 implicitBlks receipts d0K3

def d1K2 (c : Claim) (w : StateWitnessD1) (H : ChunkInner) (L : Layout) (idx : Nat) (B2 : Blk) (prevB2 : Blk) (slotB2 : ChunkInner) (implicitBlks : List Blk) (receipts : List Receipt) : Except String Observable :=
  d1PD c w H L idx B2 prevB2 slotB2 implicitBlks receipts d1K3

def d0K1 (c : Claim) (w : StateWitness) (H : ChunkInner) (L : Layout) : Except String Unit :=
  d0PC c w H L d0K2

def d1K1 (c : Claim) (w : StateWitnessD1) (H : ChunkInner) (L : Layout) : Except String Observable :=
  d1PC c w H L d1K2

def d0K0 (c : Claim) (swBytes : Bytes) : Except String Unit :=
  d0PB c swBytes d0K1

def d1K0 (c : Claim) (swBytes : Bytes) : Except String Observable :=
  d1PB c swBytes d1K1


/-! ## The chain identities are definitional -/

/-- `checkD0` is the five D0 phases in a row. -/
theorem d0_chain (cb wb : Bytes) : checkD0 cb wb = d0PA cb wb d0K0 := rfl

/-- `checkD1` is the five D1 phases in a row, projected to the verdict. -/
theorem d1_chain (cb wb : Bytes) : checkD1 cb wb = (d1PA cb wb d1K0).map (fun _ => ()) := by
  rw [checkD1]
  rfl

end NearSpecV3.D0SubD1.Work.Root
