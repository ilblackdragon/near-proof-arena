import NearSpecV3.ChunkValidationD2

/-!
# The pre-state root of the main transition (executable)

`keysD2 claim witness` is `NearSpecV3.checkD2` (= `checkD2Core d2Hooks false`) **verbatim** up
to the point where the relation reveals the main transition's recorded trie, returning the
root it reveals from (`prev_state_root` of the last new chunk). The witness normal form
(`normValsH`) keeps exactly the values that reveal looks up. Verbatim so that every step of
`checkD2` and of this function has the same syntax (`Normal.lean` evaluates them in
lockstep).
-/

namespace ReexecV3D2

open NearSpec NearSpecV3 NearSpecV3.D2

set_option linter.unusedVariables false in
def keysD2 (claimBytes witnessBytes : Bytes) : Except String Bytes := do
  -- 3.1 decoding, actor checks
  let c ← (decodeClaimE claimBytes).mapError (fun e => s!"invalid claim: {e}")
  let (swBytes, codes) ← decodeWitnessFile witnessBytes
  if !false then check codes.isEmpty "out of domain (w.no_code): contract code"
  check (lenT swBytes ≤ 8388608) "out of domain (w.size): witness larger than 8 MiB"
  let w ← decodeStateWitnessD2 swBytes
  check (w.innerBytes == c.chunkInner) "invalid: witness chunk header differs from the claim"
  check (w.epochId == c.epochId) "invalid: epoch id"
  let H ← (decodeChunkInner c.chunkInner).mapError (fun e => s!"invalid claim: {e}")
  check (c.protocolVersion == 86) "out of domain (c.pv86)"
  -- 3.2 chain segment
  let blks ← c.blocks.mapM decodeBlk
  check (!blks.isEmpty) "invalid: empty chain segment"
  -- epoch table: exactly the referenced epochs, ascending; one layout; PV 86
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
  -- epoch_start_after vs headers (spec/claim-v3.md §2.2)
  let afterEpochs := c.epochId :: blks.map (·.hdr.epochId)
  check ((List.range blks.length).all fun i =>
      match blks[i]?, afterEpochs[i]?, c.epochStartAfter[i]? with
      | some b, some e, some f =>
        (if f.toNat == 1 then e == b.hdr.nextEpochId else e == b.hdr.epochId) &&
        (!b.isGenesis || f.toNat == 1)
      | _, _, _ => false)
    "invalid: epoch_start_after inconsistent with the headers"
  check (c.applyFacts.all fun f => f.splitGate.isNone) "out of domain (c.no_split_gate)"
  -- step 6: check_valid_for_config on new_transactions (size gate; no signature check)
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
  check (!B2.isGenesis) "out of domain (c.not_genesis)"
  check c.genesisChunkExtra.isNone "invalid: genesis_chunk_extra for a non-genesis main block"
  let stop ← match (blks.drop (b2i + 1)).findIdx? isNew with
    | some j => pure (b2i + 1 + j)
    | none => throw "invalid: segment does not reach the last-but-one new chunk"
  check (stop + 1 == blks.length) "invalid: segment is not exactly the blocks the validator reads"
  let implicitIdx := (List.range b2i).reverse            -- oldest first
  let sourceBlks := (blks.drop b2i).take (stop - b2i)
  check (c.applyFacts.length == 1 + implicitIdx.length) "invalid: apply_facts length"
  -- validator_update present iff the applied block starts an epoch
  let appliedIdx := b2i :: implicitIdx
  check ((appliedIdx.zip c.applyFacts).all fun (i, f) =>
      f.validatorUpdate.isSome == (c.epochStartAfter.getD (i + 1) 0 == 1))
    "invalid: validator_update does not match the epoch start"
  let prevB2 ← match blks[b2i + 1]? with | some b => pure b | none => throw "invalid: walk"
  let slotB2 ← match B2.slots[idx]? with | some p => pure p.2 | none => throw "invalid: slot"
  -- 3.3 / 3.4 source receipts
  let mut receipts : List Rcpt := []
  let mut used : Nat := 0
  for S in sourceBlks do
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
  -- 3.5 main transition
  let sched ← match Scheduler.Params.calculate Scheduler.Config.pv86 L.numShards with
    | some p => pure p
    | none => throw "invalid: bandwidth scheduler params (assert panics)"
  let facts0 := c.applyFacts.headD ⟨none, 0, none⟩
  let ctxB2 := blockCtx L H.shardId slotB2.gasLimit B2 prevB2.hdr.nextGasPrice
  pure slotB2.prevStateRoot

end ReexecV3D2
