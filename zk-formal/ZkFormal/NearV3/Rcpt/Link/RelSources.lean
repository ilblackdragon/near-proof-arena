import ZkFormal.NearV3.Rcpt.Link.CheckedSources
import ZkFormal.NearV3.Rcpt.Link.SourceVerify

namespace ZkFormal.NearV3
open NearSpec NearSpecV3

/-- D0a itself supplies the actual decoded walk/witness, all source authentications,
and the raw receipt routing property used by deduplication. -/
theorem relD0a_sources_verified {budget : Nat} {cb wb : Bytes} (h : RelD0a budget cb wb) :
    ∃ k w, walkD0 cb = .ok k ∧ decodeW wb = .ok w ∧
      (∀ B ∈ k.sourceBlks, ∀ x ∈ B.slots, SourceSlotValid w.entries k.H.shardId B x) ∧
      (∀ e ∈ usedProofs k w, ∀ r ∈ e.receipts, k.L.shardOf r.receiverId = k.H.shardId) := by
  have ha := h.2.2.1
  unfold a2 at ha
  cases hk : walkD0 cb with
  | error err => simp [hk] at ha
  | ok k =>
    cases hw : decodeW wb with
    | error err => simp [hk, hw] at ha
    | ok w =>
      have hc : checkD0 cb wb = .ok () := by
        have hh := h.1
        unfold RelD0 acceptsD0 at hh
        cases he : checkD0 cb wb with
        | error err => simp [he] at hh
        | ok u => cases u; rfl
      refine ⟨k, w, rfl, rfl, checkD0_sources_verified hk hw hc, ?_⟩
      simpa only [hk, hw, List.all_eq_true, beq_iff_eq] using ha

/-- Equal actual source keys have equal checked roots, including occurrences in
separate source blocks. The conclusion uses no hash-injectivity assumption. -/
theorem checkedSource_roots_eq {entries : List ProofEntry} {own : Nat}
    {B C : Blk} {x y : ChunkSlot × ChunkInner}
    (hx : SourceSlotValid entries own B x) (hy : SourceSlotValid entries own C y)
    (hnx : x.1.heightIncluded == B.hdr.height) (hny : y.1.heightIncluded == C.hdr.height)
    (heq : chunkHash x.1.inner x.2.encodedMerkleRoot = chunkHash y.1.inner y.2.encodedMerkleRoot) :
    x.2.prevOutgoingReceiptsRoot = y.2.prevOutgoingReceiptsRoot := by
  obtain ⟨e, he, _, _, hv⟩ := hx hnx
  obtain ⟨f, hf, _, _, hw⟩ := hy hny
  exact source_roots_eq_of_lookupLast entries _ _ _ _ heq e f he hf hv hw

end ZkFormal.NearV3
