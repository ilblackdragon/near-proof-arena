import ZkFormal.V3.Fast.Chain
import ZkFormal.V3.Fast.RS
import NearSpecV3.PrepD0

/-!
# `prepD0` compiled with every fast path (candidate side)

Identical copies of `prepClaim`, `prepBody`, `prepD0`, `schedPub`, compiled after the
`@[csimp]` lemmas of `Fast.Hash` (SHA-256, `merkleRoot`), `Fast.Chain` (header chain,
chunk hashes, outgoing root) and `Fast.RS` (Reed–Solomon parity on arrays), and redirected
by `@[csimp]` lemmas proved by `rfl`. A verifier that imports this module and calls
`NearSpecV3.prepD0` runs the fast code; its statement is the spec's `prepD0`.
-/

namespace ZkFormal.V3.Fast

open NearSpec NearSpec.TransferV1 NearSpecV3

def schedPubF (ctx : ApplyCtx) : Option Scheduler.SchedPub :=
  Scheduler.pubOf Scheduler.Config.pv86 CongestionConfig.pv86 ctx.layout.shardIds
    (ctx.statuses.map fun (s, c, m) => (s, toCI c, m))
    (ctx.requests.map fun (s, rs) => (s, rs.map fun r => ⟨r.toShard, r.bitmap⟩))
    ctx.prevBlockHash

@[csimp] theorem schedPub_csimp : @schedPub = @schedPubF := rfl

def prepClaimF (cb : Bytes) : Except String PrepC := do
  -- 3.1 decoding (claim part)
  let c ← (decodeClaimE cb).mapError (fun e => s!"invalid claim: {e}")
  let H ← (decodeChunkInner c.chunkInner).mapError (fun e => s!"invalid claim: {e}")
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
  -- 3.2 chain segment
  let blks ← c.blocks.mapM decodeBlk
  check (!blks.isEmpty) "invalid: empty chain segment"
  check (blks.all fun b => b.hdr.epochId == c.epochId) "out of domain (c.single_epoch)"
  let hashes := blks.map (·.hdr.hash)
  check (hashes.headD [] == H.prevBlockHash) "invalid: segment does not start at prev_block_hash"
  check ((blks.zip (hashes.drop 1)).all fun (b, h) => b.hdr.prevHash == h)
    "invalid: segment is not hash-linked"
  check (blks.all fun b => b.slots.length == L.numShards) "invalid: slot count"
  -- A8 (claim-only, `ChunkValidationV0a.a8`): distinct `to_shard`s per chunk's requests
  check (blks.all fun b => b.slots.all fun (_, ci) => decide (ci.bwRequests.map (·.toShard)).Nodup)
    "out of domain (c.bw_requests): a chunk's bandwidth requests repeat a to_shard"
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
  -- A1
  check (slotB2.gasLimit ≤ maxGasLimitD0) "out of domain (c.gas_limit): chunk gas_limit above 10^15"
  -- 3.3 / 3.4: source lists in applied order
  let mut lists : List SrcList := []
  for S in sourceBlks do
    let mut srcs : List SrcList := []
    for (s, ci) in S.slots do
      if s.heightIncluded == S.hdr.height then
        srcs := srcs ++ [⟨chunkHash s.inner ci.encodedMerkleRoot, ci.shardId, ci.prevOutgoingReceiptsRoot⟩]
    let shuffled ← match shuffleWithSeed srcs S.hdr.prevHash with
      | some p => pure p
      | none => throw "invalid: shuffle fuel exhausted (probability < 2^-1024)"
    lists := lists ++ shuffled
  check (slotB2.txRoot == zeroHash32) "invalid: transaction root of the last chunk"
  let own := slotB2.congestion
  check (own.delayedGas == 0 && own.bufferedGas == 0 && own.receiptBytes == 0)
    "out of domain (c.own_congestion_zero)"
  -- scheduler public data per applied block (B2, then implicit oldest first)
  let ctxB2 := blockCtx L H.shardId slotB2.gasLimit B2 prevB2.hdr.nextGasPrice
  let ctxs := ctxB2 :: implicitBlks.map fun M => blockCtx L H.shardId slotB2.gasLimit M M.hdr.nextGasPrice
  let sched ← ctxs.mapM fun ctx => match schedPub ctx with
    | some p => pure p
    | none => throw "invalid: bandwidth scheduler aborted (StorageInconsistentState)"
  -- `allowed_shard` of the own congestion info (3.7); the header comparison itself runs in
  -- `prepBody`, after the execution-time conditions, in `checkD0`'s order
  let allowed := L.shardIds.getD ((B2.hdr.height + idx) % L.numShards) H.shardId
  pure {
    hdr := { K := implicitBlks.length, n := 0, own := H.shardId, ownIdx := idx,
             numShards := L.numShards, height := B2.hdr.height, gasPrice := prevB2.hdr.nextGasPrice,
             gasLimit := slotB2.gasLimit, prevStateRoot := slotB2.prevStateRoot,
             postStateRoot := H.prevStateRoot, outcomeRoot := H.prevOutcomeRoot,
             balanceBurnt := H.prevBalanceBurnt }
    lists, bnds := ownIntervals L H.shardId, sched, L, H, ctxB2,
    rsData := c.rsDataParts, rsTotal := c.rsTotalParts, allowed, ownCongestion := own }

@[csimp] theorem prepClaim_csimp : @prepClaim = @prepClaimF := rfl

def prepBodyF (pc : PrepC) (h : Hint) : Except String Prep := do
  let ctx := pc.ctxB2
  let refunds ← decodeBody h.body
  check (refunds.all fun r => (statusShards ctx).contains (ctx.layout.shardOf r.receiverId))
    "out of domain (e.forwarded): generated receipt buffered"
  check (fwdGasOk ctx refunds) "out of domain (e.forwarded): generated receipt buffered"
  check ((fwdLinks ctx refunds).all fun (_, d) => decide (d < fwdDemandMax))
    "out of domain (e.forwarded): forwarding demand above 2^24"
  check (h.n == 0 || (h.n - 1) * Params.G < ctx.gasLimit)
    "out of domain (e.compute): receipt delayed by the compute limit"
  -- 3.7 header comparison (claim/hint part), in `checkD0`'s order
  let H := pc.H
  check H.proposals.isEmpty "invalid: InvalidValidatorProposals"
  check (H.gasLimit == pc.hdr.gasLimit) "invalid: InvalidGasLimit"
  check (H.prevGasUsed == h.n * Params.G) "invalid: InvalidGasUsed"
  check (H.prevOutgoingReceiptsRoot == outgoingReceiptsRoot pc.L refunds) "invalid: InvalidReceiptsProof"
  check (H.congestion == { pc.ownCongestion with allowedShard := pc.allowed }) "invalid: InvalidCongestionInfo"
  check H.bwRequests.isEmpty "invalid: InvalidBandwidthRequests"
  check H.proposedSplit.isNone "invalid: InvalidChunkHeaderShardSplit"
  check (H.txRoot == zeroHash32) "invalid: InvalidTxRoot"
  let body := h.body
  match encodedMerkleRoot pc.rsData pc.rsTotal body with
  | none => throw "invalid: Reed-Solomon parameters"
  | some (emr, len) =>
    check (pc.H.encodedMerkleRoot == emr) "invalid: InvalidChunkEncodedMerkleRoot"
    check (pc.H.encodedLength == len) "invalid: InvalidChunkEncodedLength"
  pure { hdr := { pc.hdr with n := h.n }, lists := pc.lists, bnds := pc.bnds, sched := pc.sched,
         body, fwd := fwdLinks ctx refunds }

@[csimp] theorem prepBody_csimp : @prepBody = @prepBodyF := rfl

def prepD0F (cb : Bytes) (h : Hint) : Except String Prep := do
  let pc ← prepClaim cb
  prepBody pc h

@[csimp] theorem prepD0_csimp : @prepD0 = @prepD0F := rfl

end ZkFormal.V3.Fast
