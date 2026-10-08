import ZkFormal.NearV3.Rcpt.Candidates.PreparedReceipts
import ZkFormal.NearV3.Assembly.PreparedSources

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3 Sched

private theorem forIn_permutation {α β : Type} (piece : α → List β)
    (f : α → List β → Except String (ForInStep (List β)))
    (hf : ∀ x acc step,f x acc=.ok step → ∃ ys,step=.yield ys ∧ (acc++piece x).Perm ys) :
    ∀ (xs : List α) (acc out : List β),forIn xs acc f=.ok out →
      (acc++xs.flatMap piece).Perm out
  | [],acc,out,h => by cases h; simp
  | x::xs,acc,out,h => by
    rw [List.forIn_cons] at h
    obtain ⟨step,hs,h⟩ := bind_ok h
    obtain ⟨ys,rfl,hp⟩ := hf x acc step hs
    have ih := forIn_permutation piece f hf xs ys out h
    have ht := hp.append_right (xs.flatMap piece)
    simpa only [List.flatMap_cons,List.append_assoc] using ht.trans ih

private theorem shuffleWithSeed_perm {α : Type} {xs ys : List α} {seed : Bytes}
    (h : shuffleWithSeed xs seed=some ys) : xs.Perm ys := by
  classical
  unfold shuffleWithSeed at h
  cases hs : shuffle xs (Rng.ofSeed seed) with
  | none => simp [hs] at h
  | some p =>
    have he : p.1=ys := by simpa [hs] using h
    rw [←he]
    exact (shuffle_perm hs).symm

/-- Successful preparation preserves all source occurrences, with multiplicity,
including repeated keys; only their per-block order is shuffled. -/
theorem preparedSourceLists_perm {blocks : List Blk} {out : List SrcList}
    (h : preparedSourceLists blocks=.ok out) :
    (blocks.flatMap (fun B => slotDescriptors B B.slots)).Perm out := by
  apply forIn_permutation (fun B => slotDescriptors B B.slots) _ ?_ blocks [] out h
  intro B acc step hs
  obtain ⟨srcs,hsrc,hs⟩ := bind_ok hs
  rw [slotSources_eq] at hsrc
  have he := Except.ok.inj hsrc
  subst srcs
  split at hs
  · rename_i shuffled hsh
    obtain ⟨_,he,hs⟩ := bind_ok hs
    cases he
    cases hs
    exact ⟨_,rfl,(shuffleWithSeed_perm hsh).append_left acc⟩
  · obtain ⟨_,he,_⟩ := bind_ok hs
    cases he

/-- Every native included slot occurs in the actually prepared public source list. -/
theorem prepD0_source_slot_mem {cb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    (hp : prepD0 cb hint=.ok p) (hw : walkD0 cb=.ok k)
    {B : Blk} (hB : B∈k.sourceBlks) {x : ChunkSlot × ChunkInner} (hx : x∈B.slots)
    (hn : x.1.heightIncluded == B.hdr.height) :
    (⟨chunkHash x.1.inner x.2.encodedMerkleRoot,x.2.shardId,x.2.prevOutgoingReceiptsRoot⟩ : SrcList)∈p.lists := by
  apply (preparedSourceLists_perm (Assembly.prepD0_source_lists hp hw)).mem_iff.mp
  apply List.mem_flatMap.mpr
  refine ⟨B,hB,List.mem_flatMap.mpr ⟨x,hx,?_⟩⟩
  simp [hn]

end ZkFormal.NearV3.Rcpt.Candidates
