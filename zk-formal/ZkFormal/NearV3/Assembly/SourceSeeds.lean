import ZkFormal.NearV3.Assembly.AppliedSeeds
import ZkFormal.NearV3.Rcpt.Render.Srcp.FromProofFacts
import ZkFormal.NearV3.Rcpt.Link.CheckedSources
import ZkFormal.NearV3.Rcpt.Candidates.OrderedSources

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.SrcpGen

def sourceSeed (root : Bytes) (dup : Bool) (j q : Nat) (e : ProofEntry) : SourceEntryV3 :=
  {key := e.key, fromShard := e.proof.fromShard, toShard := e.proof.toShard,
   receipts := receiptListSeed e.receipts, path := blockOfProof root dup j q e}

theorem sourceSeed_entry {root : Bytes} {dup : Bool} {j q : Nat} {e : ProofEntry}
    (hr : ∀ r ∈ e.receipts, ReceiptSeedExact r)
    (hd : ∀ step ∈ e.proof.path, step.2 = 0 ∨ step.2 = 1) :
    (sourceSeed root dup j q e).entry = e := by
  have hp := (blockOfProof_leaf_path root dup j q e hd).2
  have hl : (receiptListSeed e.receipts).rs.map (fun r => r.toRcptV.toReceipt) = e.receipts := by
    simp only [receiptListSeed, List.map_map]
    conv => rhs; rw [← List.map_id e.receipts]
    apply List.map_congr_left
    exact hr
  change (blockOfProof root dup j q e).path.map
    (fun it => (Link3.toB it.sib, if it.dir then 1 else 0)) = e.proof.path at hp
  simp only [SourceEntryV3.entry, sourceSeed, hl, hp]

theorem decoded_sourceSeed_entry {bs : Bytes} {w : StateWitness}
    (hw : decodeStateWitness bs = .ok w) {e : ProofEntry} (he : e ∈ w.entries)
    (root : Bytes) (dup : Bool) (j q : Nat) : (sourceSeed root dup j q e).entry = e := by
  apply sourceSeed_entry
  · exact decodeStateWitness_receipt_seeds hw e he
  · intro step hs
    exact (decodeStateWitness_path_shape hw e he step hs).2

/-- Keep the original encoded dictionary order and all unused filler entries.
Source block metadata is seeded independently of the exact dictionary payload. -/
def sourceDictionarySeeds (keys : List Bytes) (entries : List ProofEntry) : List DictionaryEntryV3 :=
  entries.map fun e => if e.key ∈ keys then .inl (sourceSeed [] false 0 1 e) else .inr e

theorem sourceDictionarySeeds_entries {bs : Bytes} {w : StateWitness}
    (hw : decodeStateWitness bs = .ok w) (keys : List Bytes) :
    (sourceDictionarySeeds keys w.entries).map DictionaryEntryV3.entry = w.entries := by
  simp only [sourceDictionarySeeds, List.map_map]
  conv => rhs; rw [← List.map_id w.entries]
  apply List.map_congr_left
  intro e he
  dsimp only [Function.comp_def]
  split
  · exact decoded_sourceSeed_entry hw he [] false 0 1
  · rfl

theorem sourceDictionarySeeds_selected {k : WalkD0} {w : StateWitness} {bs : Bytes}
    (hd : decodeStateWitness bs = .ok w)
    (hv : ∀ b ∈ k.sourceBlks, ∀ x ∈ b.slots, SourceSlotValid w.entries k.H.shardId b x) :
    ∀ b ∈ k.sourceBlks, ∀ s ci, (s,ci) ∈ b.slots →
      s.heightIncluded == b.hdr.height →
      ∃ e : SourceEntryV3, Sum.inl e ∈ sourceDictionarySeeds (sourceKeysV3 k) w.entries ∧
        lookupLast (chunkHash s.inner ci.encodedMerkleRoot)
          ((sourceDictionarySeeds (sourceKeysV3 k) w.entries).map DictionaryEntryV3.entry) = some e.entry ∧
        e.fromShard = ci.shardId ∧ e.toShard = k.H.shardId ∧
        verifyReceiptProof ci.prevOutgoingReceiptsRoot e.entry = true := by
  intro b hb s ci hs hn
  obtain ⟨e,he,hf,ht,hp⟩ := hv b hb (s,ci) hs hn
  have hem := lookupLast_mem he
  have hek := Rcpt.Candidates.lookupLast_key he
  have hk : e.key ∈ sourceKeysV3 k := by
    rw [hek]
    apply List.mem_flatMap.mpr
    refine ⟨b,hb,?_⟩
    apply List.mem_filterMap.mpr
    refine ⟨(s,ci),hs,?_⟩
    simp only [hn, ↓reduceIte]
  have hm : Sum.inl (sourceSeed [] false 0 1 e) ∈ sourceDictionarySeeds (sourceKeysV3 k) w.entries := by
    apply List.mem_map.mpr
    exact ⟨e,hem,by simp only [hk, ↓reduceIte]⟩
  refine ⟨sourceSeed [] false 0 1 e,hm,?_,hf,ht,?_⟩
  · rw [sourceDictionarySeeds_entries hd, decoded_sourceSeed_entry hd hem]
    exact he
  · rwa [decoded_sourceSeed_entry hd hem]

end ZkFormal.NearV3.Assembly
