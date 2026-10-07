import ZkFormal.NearV3.Assembly.Execution

/-!
Semantic factoring interface. `GoodV3` never calls `checkD0`, `checkD0a` or
`RelD0a`; it states source selection, exact state execution, ordinary byte/domain
bounds and header equality. `FactorSound` and `FactorComplete` below are OPEN
proposition types, not axioms or proved equivalences. The separate AIR bridge
must establish these semantic fields from checked views and explicitly budgeted
hash assumptions. Row capacity is not implied by this interface.
-/
namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

def sourceKeysV3 (k : WalkD0) : List Bytes :=
  k.sourceBlks.flatMap fun b => b.slots.filterMap fun (s, ci) =>
    if s.heightIncluded == b.hdr.height then some (chunkHash s.inner ci.encodedMerkleRoot)
    else none

structure SourceSemanticsV3 (k : WalkD0) (x : ExtV3) : Prop where
  /-- Every actual source selects an authenticated entry, never a filler. -/
  selected : ∀ b ∈ k.sourceBlks, ∀ s ci, (s, ci) ∈ b.slots →
    s.heightIncluded == b.hdr.height →
    ∃ e : SourceEntryV3, Sum.inl e ∈ x.dictionary ∧
      lookupLast (chunkHash s.inner ci.encodedMerkleRoot)
        (x.dictionary.map DictionaryEntryV3.entry) = some e.entry ∧
      e.fromShard = ci.shardId ∧ e.toShard = k.H.shardId ∧
      verifyReceiptProof ci.prevOutgoingReceiptsRoot e.entry = true
  shuffle : ∀ b ∈ k.sourceBlks, ∃ shuffled,
    shuffleWithSeed (b.slots.filterMap (fun (s, ci) =>
      if s.heightIncluded == b.hdr.height then
        lookupLast (chunkHash s.inner ci.encodedMerkleRoot)
          (x.dictionary.map DictionaryEntryV3.entry) else none)) b.hdr.prevHash = some shuffled
  dictionaryCount : (distinctKeys (x.dictionary.map DictionaryEntryV3.entry)).length =
    (sourceKeysV3 k).length
  applied : appliedReceipts k (stateWitnessOfV3 k x) = x.applied
  routing : ∀ e ∈ usedProofs k (stateWitnessOfV3 k x), ∀ r ∈ e.receipts,
    k.L.shardOf r.receiverId = k.H.shardId

/-- Comparisons with the endorsed header and the prepared body/hint. -/
structure HeaderSemanticsV3 (k : WalkD0) (h : Hint) (p : Prep)
    (m : MainExecutionV3) (last : Bytes) : Prop where
  stateRoot : k.H.prevStateRoot = last
  outcomeRoot : k.H.prevOutcomeRoot = NearSpec.outcomeRoot m.result.outcomes
  proposals : k.H.proposals.isEmpty = true
  gasLimit : k.H.gasLimit = k.slotB2.gasLimit
  gasUsed : k.H.prevGasUsed = m.result.gasUsed
  tokensBurnt : k.H.prevBalanceBurnt = m.result.tokensBurnt
  outgoingRoot : k.H.prevOutgoingReceiptsRoot = outgoingReceiptsRoot k.L m.result.outgoing
  congestion : k.H.congestion = { k.slotB2.congestion with
    allowedShard := k.L.shardIds.getD ((m.block.hdr.height + k.idx) % k.L.numShards) k.H.shardId }
  bandwidthRequests : k.H.bwRequests.isEmpty = true
  split : k.H.proposedSplit.isNone = true
  txRoot : k.H.txRoot = zeroHash32
  body : h.body = u32 0 ++ encodeReceipts m.result.outgoing
  preparedBody : p.body = h.body
  encoded : encodedMerkleRoot k.c.rsDataParts k.c.rsTotalParts h.body =
    some (k.H.encodedMerkleRoot, k.H.encodedLength)

structure GoodV3 (B : Nat) (cb : Bytes) (k : WalkD0) (h : Hint) (p : Prep) (x : ExtV3) : Prop where
  walk : walkD0 cb = .ok k
  prepared : prepD0 cb h = .ok p
  shape : V3.D0Shape (stateWitnessOfV3 k x)
  witnessBytes : (V3.encodeSW (stateWitnessOfV3 k x)).length ≤ 8388608
  mainStoreBytes : ((x.store 0).map List.length).foldl (· + ·) 0 ≤ 3000000
  source : SourceSemanticsV3 k x
  receiptCount : h.n = x.applied.length
  receiptIds : (x.applied.map Receipt.receiptId).Nodup
  mainTxRoot : k.slotB2.txRoot = zeroHash32
  ownCongestion : k.slotB2.congestion.delayedGas = 0 ∧
    k.slotB2.congestion.bufferedGas = 0 ∧ k.slotB2.congestion.receiptBytes = 0
  executions : ∃ m last, m.Valid k x ∧
    ImplicitRunV3 k x 1 m.result.trie.hashOf k.implicitBlks last ∧
    HeaderSemanticsV3 k h p m last
  gasLimit : k.slotB2.gasLimit ≤ maxGasLimitD0
  canonicalScheduler : (reads0f k (stateWitnessOfV3 k x)).all (canonical0f k.L) = true
  unfoldedBytes : unfoldBytes cb (witnessOfV3 k x) ≤ B
  distinctRequests : ∀ b ∈ k.blks, ∀ s ci, (s, ci) ∈ b.slots →
    (ci.bwRequests.map (·.toShard)).Nodup

theorem GoodV3.decode {B cb k h p x} (g : GoodV3 B cb k h p x) :
    decodeW (witnessOfV3 k x) = .ok (stateWitnessOfV3 k x) := by
  unfold decodeW witnessOfV3
  rw [V3.decodeWitnessFile_encode _ g.shape]
  simpa only [bind, Except.bind] using V3.decodeStateWitness_encode _ g.shape

theorem GoodV3.amendments {B cb k h p x} (g : GoodV3 B cb k h p x) :
    a1 cb = true ∧ a2 cb (witnessOfV3 k x) = true ∧
      canon0f cb (witnessOfV3 k x) = true ∧ a7 B cb (witnessOfV3 k x) = true ∧
      a8 cb = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [a1, g.walk] using g.gasLimit
  · simp only [a2, g.walk, g.decode]
    apply List.all_eq_true.mpr
    intro e he
    apply List.all_eq_true.mpr
    intro r hr
    exact beq_iff_eq.mpr (g.source.routing e he r hr)
  · simpa only [canon0f, g.walk, g.decode] using g.canonicalScheduler
  · simpa only [a7, decide_eq_true_eq] using g.unfoldedBytes
  · simp only [a8, g.walk]
    apply List.all_eq_true.mpr
    intro b hb
    apply List.all_eq_true.mpr
    rintro ⟨s, ci⟩ hs
    exact decide_eq_true (g.distinctRequests b hb s ci hs)

/-- Open proof obligation: semantic reconstructed views imply the frozen
amended checker accepts their concrete encoded witness. -/
def FactorSound : Prop := ∀ B cb k h p x,
  GoodV3 B cb k h p x → checkD0a B cb (witnessOfV3 k x) = .ok ()

/-- Open proof obligation: actual accepted witness bytes admit semantic views.
This does not assert a row bound or a complete AIR rendering theorem. -/
def FactorComplete : Prop := ∀ B cb w, checkD0a B cb w = .ok () →
  ∃ k h p x, GoodV3 B cb k h p x

end ZkFormal.NearV3.Assembly
