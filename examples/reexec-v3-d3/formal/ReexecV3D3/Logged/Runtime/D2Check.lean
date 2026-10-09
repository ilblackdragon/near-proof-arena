import ReexecV3D3.Logged.Runtime.D2Runtime
import NearSpecV3.ChunkValidationD2

namespace NearSpecV3.D2

open NearSpec NearSpecV3 ReexecV3D3.Logged

def liftEK {K α : Type} : Except String α → SM K α
  | .ok a => pure a
  | .error e => throw e

def checkK {K : Type} (b : Bool) (msg : String) : SM K Unit := if b then pure () else throw msg

/-- Tagged lookup in the main store and the implicit transitions' stores. -/
def storesOfW (main : HStore) (imps : List HStore) : Nat × Bytes → Option Bytes
  | (0, h) => hGet main h
  | (k + 1, h) => match imps[k]? with
    | some st => hGet st h
    | none => none

/-- The recorded stores of a witness file, as data: the main store (`base_state ++ code blobs`) and
each implicit transition's `base_state`. -/
def storesData (witnessBytes : Bytes) : Option (HStore × List HStore) :=
  match decodeWitnessFile witnessBytes with
  | .error _ => none
  | .ok (swBytes, codes) =>
    match decodeStateWitnessD2 swBytes with
    | .error _ => none
    | .ok w => some (mkHStore (w.main.values ++ codes), w.implicit.map fun T => mkHStore T.values)

def storeFn : Option (HStore × List HStore) → Nat × Bytes → Option Bytes
  | none, _ => none
  | some (main, imps), k => storesOfW main imps k

/-- The recorded stores of a witness file, tagged: `0` = main (`base_state ++ code blobs`), `k + 1` =
implicit transition `k`'s `base_state`. (Evaluate `storesData` once and use `storeFn`.) -/
def storesOf (witnessBytes : Bytes) : Nat × Bytes → Option Bytes := storeFn (storesData witnessBytes)

def checkD2CoreL (hooks : ActionHooksL) (allowCodes : Bool) (claimBytes witnessBytes : Bytes)
    (gasCap : Option Nat := none) : SM (Nat × Bytes) Unit := do
  -- 3.1 decoding, actor checks
  let c ← liftEK ((decodeClaimE claimBytes).mapError (fun e => s!"invalid claim: {e}"))
  let (swBytes, codes) ← liftEK (decodeWitnessFile witnessBytes)
  if !allowCodes then checkK codes.isEmpty "out of domain (w.no_code): contract code"
  checkK (lenT swBytes ≤ 8388608) "out of domain (w.size): witness larger than 8 MiB"
  let w ← liftEK (decodeStateWitnessD2 swBytes)
  checkK (w.innerBytes == c.chunkInner) "invalid: witness chunk header differs from the claim"
  checkK (w.epochId == c.epochId) "invalid: epoch id"
  let H ← liftEK ((decodeChunkInner c.chunkInner).mapError (fun e => s!"invalid claim: {e}"))
  checkK (c.protocolVersion == 86) "out of domain (c.pv86)"
  -- 3.2 chain segment
  let blks ← liftEK (c.blocks.mapM decodeBlk)
  checkK (!blks.isEmpty) "invalid: empty chain segment"
  -- epoch table: exactly the referenced epochs, ascending; one layout; PV 86
  let referenced := dedupSorted (c.epochId :: blks.map (·.hdr.epochId))
  checkK (strictlyAscending (c.epochs.map (·.epochId)))
    "invalid: epoch table not strictly ascending"
  checkK (c.epochs.map (·.epochId) == referenced) "invalid: epoch table does not match the referenced epochs"
  let ep ← match c.epochs.find? (·.epochId == c.epochId) with
    | some e => pure e
    | none => throw "invalid: epoch_id not in the epoch table"
  checkK (ep.protocolVersion == c.protocolVersion)
    "invalid: epoch table does not match epoch_id / protocol_version"
  checkK (c.epochs.all (·.protocolVersion == 86)) "out of domain (c.pv86): epoch protocol version"
  checkK (c.epochs.all (·.shardLayout == ep.shardLayout)) "out of domain (c.same_layout): resharding"
  let L ← liftEK (decodeLayout ep.shardLayout)
  checkK (1 ≤ L.numShards && L.numShards ≤ 64) "out of domain (c.layout)"
  checkK (rsGenesisParamsOk c.rsDataParts c.rsTotalParts) "invalid: Reed-Solomon parameters"
  checkK (c.blocks.length ≤ 32) "out of domain (c.segment)"
  checkK (c.epochStartAfter.length == c.blocks.length) "invalid: epoch_start_after length"
  checkK (c.epochStartAfter.all (·.toNat ≤ 1)) "invalid: epoch_start_after flag"
  -- epoch_start_after vs headers (spec/claim-v3.md §2.2)
  let afterEpochs := c.epochId :: blks.map (·.hdr.epochId)
  checkK ((List.range blks.length).all fun i =>
      match blks[i]?, afterEpochs[i]?, c.epochStartAfter[i]? with
      | some b, some e, some f =>
        (if f.toNat == 1 then e == b.hdr.nextEpochId else e == b.hdr.epochId) &&
        (!b.isGenesis || f.toNat == 1)
      | _, _, _ => false)
    "invalid: epoch_start_after inconsistent with the headers"
  checkK (c.applyFacts.all fun f => f.splitGate.isNone) "out of domain (c.no_split_gate)"
  -- step 6: check_valid_for_config on new_transactions (size gate; no signature check)
  checkK (w.newTxs.all TxD2.sizeOk) "invalid: new transaction exceeds max_transaction_size"
  let hashes := blks.map (·.hdr.hash)
  checkK (hashes.headD [] == H.prevBlockHash) "invalid: segment does not start at prev_block_hash"
  checkK ((blks.zip (hashes.drop 1)).all fun (b, h) => b.hdr.prevHash == h)
    "invalid: segment is not hash-linked"
  checkK (blks.all fun b => b.slots.length == L.numShards) "invalid: slot count"
  let idx ← match L.index H.shardId with
    | some i => pure i
    | none => throw "invalid: shard not in layout"
  let isNew := fun (b : Blk) => match b.slots[idx]? with
    | some (s, _) => s.heightIncluded == b.hdr.height
    | none => false
  checkK (blks.all fun b => b.slots.all fun (sl, _) => sl.heightIncluded ≤ b.hdr.height)
    "invalid: height_included above block height (block_congestion_info panics)"
  let b2i ← match blks.findIdx? isNew with
    | some i => pure i
    | none => throw "invalid: segment has no new chunk"
  let B2 ← match blks[b2i]? with | some b => pure b | none => throw "invalid: walk"
  checkK (!B2.isGenesis) "out of domain (c.not_genesis)"
  checkK c.genesisChunkExtra.isNone "invalid: genesis_chunk_extra for a non-genesis main block"
  let stop ← match (blks.drop (b2i + 1)).findIdx? isNew with
    | some j => pure (b2i + 1 + j)
    | none => throw "invalid: segment does not reach the last-but-one new chunk"
  checkK (stop + 1 == blks.length) "invalid: segment is not exactly the blocks the validator reads"
  let implicitIdx := (List.range b2i).reverse            -- oldest first
  let sourceBlks := (blks.drop b2i).take (stop - b2i)
  checkK (c.applyFacts.length == 1 + implicitIdx.length) "invalid: apply_facts length"
  -- validator_update present iff the applied block starts an epoch
  let appliedIdx := b2i :: implicitIdx
  checkK ((appliedIdx.zip c.applyFacts).all fun (i, f) =>
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
        checkK (e.proof.fromShard == ci.shardId) "invalid: receipt proof from_shard_id"
        checkK (e.proof.toShard == H.shardId) "invalid: receipt proof to_shard_id"
        checkK (verifyReceiptProofD2 ci.prevOutgoingReceiptsRoot e) "invalid: receipt proof merkle path"
        proofs := proofs ++ [e]
        used := used + 1
    let shuffled ← match shuffleWithSeed proofs S.hdr.prevHash with
      | some p => pure p
      | none => throw "invalid: shuffle fuel exhausted (probability < 2^-1024)"
    receipts := receipts ++
      (shuffled.map fun e => e.receipts.filter fun r => L.shardOf r.recv == H.shardId).flatten
  checkK ((distinctKeysD2 w.entries).length == used) "invalid: source_receipt_proofs contains extra proofs"
  checkK (sha256 (encodeRcpts receipts) == w.appliedReceiptsHash) "invalid: applied receipts hash"
  -- steps 8, 9: transactions of the last new chunk and their validity flags
  checkK (merklizeBorsh (w.txs.map TxD2.raw) == slotB2.txRoot) "invalid: transaction root of the last chunk"
  checkK (c.txValid.length == w.txs.length) "invalid: tx_valid length"
  -- 3.5 main transition
  let sched ← match Scheduler.Params.calculate Scheduler.Config.pv86 L.numShards with
    | some p => pure p
    | none => throw "invalid: bandwidth scheduler params (assert panics)"
  let facts0 := c.applyFacts.headD ⟨none, 0, none⟩
  let ctxB2 := blockCtx L H.shardId slotB2.gasLimit B2 prevB2.hdr.nextGasPrice
  -- E2: the recorded storage merged with the contract codes (`codes = []` unless `allowCodes`)
  let merged := w.main.values ++ codes
  let env : Env := { envOf c ctxB2 B2 facts0.minimumStake sched with
                     store := .tip, preRoot := slotB2.prevStateRoot }
  checkK true "invalid: main base_state does not hash to prev_state_root"
  let lastProps := slotB2.proposals.filterMap decodeProposal
  let out ← SM.mapKey (fun h => ((0 : Nat), h))
    ((applyNewChunkD2L hooks prims env facts0.validatorUpdate lastProps receipts
      (w.txs.zip (c.txValid.map (· != 0))) slotB2.congestion) slotB2.prevStateRoot)
  -- w.size: sums the merged list (conservative; spec/near-chunk-validation-d3.md §2.2)
  let baseBytes := (merged.map List.length).foldl (· + ·) 0
  checkK (baseBytes + 2000 * out.cdRemovals ≤ 4000000)
    "out of domain (w.size): storage-proof upper bound may exceed main_storage_proof_size_soft_limit"
  -- D3: per-chunk WASM gas cap (`G_α`, D3_WASM_REQUIREMENTS §1.1/§2.4); D2 passes `none`
  if let some cap := gasCap then
    checkK (out.wasmGas ≤ cap) s!"out of domain (e.g_alpha): chunk function-call gas {out.wasmGas} > G_α {cap}"
  let mut root := out.root
  checkK (root == w.main.postStateRoot) "invalid: main transition post state root"
  -- 3.6 implicit transitions
  checkK (w.implicit.length == implicitIdx.length) "invalid: implicit transitions count"
  let mainProps := out.proposals.map fun p => (p.acct, p.stake)
  for (((i, f), T), k) in ((implicitIdx.zip (c.applyFacts.drop 1)).zip w.implicit).zipIdx do
    let M ← match blks[i]? with | some b => pure b | none => throw "invalid: walk"
    let ctxM := blockCtx L H.shardId slotB2.gasLimit M M.hdr.nextGasPrice
    let envM : Env := envOf c ctxM M f.minimumStake sched
    root ← SM.mapKey (fun h => (k + 1, h)) ((applyMissingChunkD2L prims envM f.validatorUpdate mainProps) root)
    checkK (root == T.postStateRoot) "invalid: implicit transition post state root"
  -- 3.7 comparison with the endorsed header
  checkK (H.prevStateRoot == root) "invalid: InvalidStateRoot"
  checkK (H.prevOutcomeRoot == outcomeRootD1 out.outcomes) "invalid: InvalidOutcomesProof"
  checkK (H.proposals == out.proposals.map Proposal.encode) "invalid: InvalidValidatorProposals"
  checkK (H.gasLimit == slotB2.gasLimit) "invalid: InvalidGasLimit"
  checkK (H.prevGasUsed == out.gasUsed) "invalid: InvalidGasUsed"
  checkK (H.prevBalanceBurnt == out.balanceBurnt) "invalid: InvalidBalanceBurnt"
  checkK (H.prevOutgoingReceiptsRoot == outgoingReceiptsRootD2 L out.outgoing) "invalid: InvalidReceiptsProof"
  checkK (H.congestion == out.congestion) "invalid: InvalidCongestionInfo"
  checkK (H.bwRequests == out.bwRequests) "invalid: InvalidBandwidthRequests"
  checkK H.proposedSplit.isNone "invalid: InvalidChunkHeaderShardSplit"
  checkK (H.txRoot == merklizeBorsh (w.newTxs.map TxD2.raw)) "invalid: InvalidTxRoot"
  let body := u32 w.newTxs.length ++ concatAll (w.newTxs.map TxD2.raw) ++ encodeRcpts out.outgoing
  match encodedMerkleRoot c.rsDataParts c.rsTotalParts body with
  | none => throw "invalid: Reed-Solomon parameters"
  | some (emr, len) =>
    checkK (H.encodedMerkleRoot == emr) "invalid: InvalidChunkEncodedMerkleRoot"
    checkK (H.encodedLength == len) "invalid: InvalidChunkEncodedLength"


def checkD2L (claimBytes witnessBytes : Bytes) : SM (Nat × Bytes) Unit :=
  checkD2CoreL d2HooksL false claimBytes witnessBytes

end NearSpecV3.D2

