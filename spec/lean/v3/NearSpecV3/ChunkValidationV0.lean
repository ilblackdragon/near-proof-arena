import NearSpecV3.WitnessV3
import NearSpecV3.RuntimeD0
import NearSpecV3.ChaCha20
import NearSpecV3.Congestion
import NearSpecV3.BandwidthScheduler
import NearSpecV3.ReedSolomon

/-!
# `NearSpecV3.ChunkValidationV0` — `Rel_D0(claim, witness)`

The statement `near/pv86/chunk-validation/v0` restricted to domain D0
(spec/near-chunk-validation-v0.md §3, §6): `checkD0 claimBytes witnessBytes`
returns

* `.ok ()` — `Rel(c, w) ∧ InD0(c, w)`: nearcore 2.13.4's chunk validator, with the
  store/epoch-manager answers recorded in the claim, accepts the witness for the
  endorsed chunk, and the chunk is in D0;
* `.error "invalid: …"` — `¬Rel(c, w)` (decoding, hash discipline, a nearcore check
  fails) for a claim/witness in D0 as far as decided;
* `.error "out of domain …"` — the case leaves D0 (then `Rel_D0` is false; `Rel` itself
  is not decided here).

`RelD0 c w := checkD0 c w = .ok ()`. Step numbers refer to spec §3.
Every hash is `NearSpec.sha256` (= `ArenaCore.sha256`), every trie operation is
NearSpec's `PTrie` (`find`, `set`, `upsert`, `hashOf`).
-/

namespace NearSpecV3

open NearSpec NearSpec.TransferV1

/-! ## Primitives wiring -/

def toCI (c : Congestion) : CongestionInfo := ⟨c.delayedGas, c.bufferedGas, c.receiptBytes, c.allowedShard⟩

def prims : Prims where
  sched i :=
    (Scheduler.run Scheduler.Config.pv86 CongestionConfig.pv86 i.shardIds i.prev
      (i.statuses.map fun (s, c, m) => (s, toCI c, m))
      (i.requests.map fun (s, rs) => (s, rs.map fun r => ⟨r.toShard, r.bitmap⟩))
      i.prevBlockHash).map fun o =>
      ⟨o.state, fun a b => ((o.granted.find? (·.1 == (a, b))).map (·.2)).getD 0⟩
  outGas c missed sender := Congestion.outgoingGasLimit CongestionConfig.pv86 (toCI c) missed sender

/-! ## Helpers -/

def check (b : Bool) (msg : String) : Except String Unit := if b then .ok () else .error msg

def zeroHash32 : Bytes := zeros 32

/-- `merklize` over items whose borsh is `b` (leaf = sha256(b)). -/
def merklizeBorsh (items : List Bytes) : Bytes := merkleRoot (items.map sha256)

/-- `compute_root_from_path` (`merkle.rs:131-144`). -/
def rootFromPath : Bytes → List (Bytes × Nat) → Bytes
  | acc, [] => acc
  | acc, (h, d) :: rest => rootFromPath (if d == 0 then sha256 (h ++ acc) else sha256 (acc ++ h)) rest

/-- `ReceiptProof::verify_against_receipt_root` (`sharding.rs:980-987`):
leaf item = `hash_borsh(ReceiptList(to_shard, receipts))`, then `verify_path` hashes it again. -/
def verifyReceiptProof (root : Bytes) (e : ProofEntry) : Bool :=
  let item := sha256 (u64 e.proof.toShard ++ encodeReceipts e.receipts)
  rootFromPath (sha256 item) e.proof.path == root

/-- `Chain::build_receipts_hashes` + `merklize` (`chain.rs:4102-4130`). -/
def outgoingReceiptsRoot (l : Layout) (rs : List Receipt) : Bytes :=
  merklizeBorsh (l.shardIds.map fun s =>
    sha256 (u64 s ++ encodeReceipts (rs.filter fun r => l.shardOf r.receiverId == s)))

/-- `ChunkHashHeight` leaf bytes. -/
def slotLeaf (s : ChunkSlot) (ci : ChunkInner) : Bytes :=
  chunkHash s.inner ci.encodedMerkleRoot ++ u64 s.heightIncluded

structure Blk where
  brec : BlockRec
  hdr : BlockHdr
  slots : List (ChunkSlot × ChunkInner)

def decodeBlk (r : BlockRec) : Except String Blk := do
  let hdr ← decodeBlockV6 r.headerVersion r.prevHash r.innerLite r.innerRest
  let slots ← r.slots.mapM fun s => do
    let ci ← decodeChunkInner s.inner
    pure (s, ci)
  check (merklizeBorsh (slots.map fun (s, ci) => slotLeaf s ci) == hdr.chunkHeadersRoot)
    "invalid: chunk slots do not match chunk_headers_root"
  pure ⟨r, hdr, slots⟩

def Blk.isGenesis (b : Blk) : Bool := b.hdr.prevHash == zeroHash32

/-- Block apply context (`get_apply_chunk_block_context`, chain.rs:2896-2935). -/
def blockCtx (l : Layout) (own gasLimit : Nat) (b : Blk) (gasPrice : Nat) : ApplyCtx :=
  { height := b.hdr.height, prevBlockHash := b.hdr.prevHash, gasPrice, gasLimit, layout := l, own,
    statuses := b.slots.map fun (s, ci) => (ci.shardId, ci.congestion, b.hdr.height - s.heightIncluded),
    requests := b.slots.map fun (_, ci) => (ci.shardId, ci.bwRequests) }

def rsGenesisParamsOk (d t : Nat) : Bool :=
  2 ≤ t && t ≤ 256 && d == (if t ≤ 3 then 1 else (t - 1) / 3)

/-! ## The D0 relation -/

def checkD0 (claimBytes witnessBytes : Bytes) : Except String Unit := do
  -- 3.1 decoding, actor checks
  let c ← (decodeClaimE claimBytes).mapError (fun e => s!"invalid claim: {e}")
  let (swBytes, codes) ← decodeWitnessFile witnessBytes
  check codes.isEmpty "out of domain (w.no_code): contract code"
  check (lenT swBytes ≤ 8388608) "out of domain (w.size): witness larger than 8 MiB"
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

/-- **The D0 relation** on canonical bytes. -/
def acceptsD0 (claimBytes witnessBytes : Bytes) : Bool :=
  match checkD0 claimBytes witnessBytes with
  | .ok () => true
  | .error _ => false

def RelD0 (claimBytes witnessBytes : Bytes) : Prop := acceptsD0 claimBytes witnessBytes = true

instance (c w : Bytes) : Decidable (RelD0 c w) := by unfold RelD0; infer_instance

end NearSpecV3
