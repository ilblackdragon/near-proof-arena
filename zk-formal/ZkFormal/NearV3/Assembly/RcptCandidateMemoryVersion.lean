import ZkFormal.NearV3.Assembly.RcptCandidateRepairedSound

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3Proof

/-- Every receipt issues the zero-byte account read, so its previous version
is present in the actual logical MEM receive stream. -/
theorem memory_version_read {ls : RcptV3Vs} {x : RcptE} (hx : x∈flatR ls) :
    [x.kslot,x.tprev,0,x.bef.getD 0 0,x.lk.getD 0 0,x.st.getD 0 0]∈rcptRecvs3 ls B_MEM := by
  rw [memoryReadMsgs_view]
  apply List.mem_flatMap.mpr
  refine ⟨x,hx,?_⟩
  exact List.mem_map.mpr ⟨0,by simp,rfl⟩

/-- Canonical previous versions come directly from physical field decoding,
independently of age arithmetic or semantic receipt wellformedness. -/
theorem extracted_previous_canonical {tr : Trace Fp} {tt : Nat} {bs : List ListBlock}
    {x : RcptE} (hx : x∈flatR (bs.map (ListBlock.view tr tt))) : x.tprev<P := by
  rw [flat_views] at hx
  obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx
  exact cv_lt _ _ _ _

/-- A bound on the versions of positively counted physical MEM receives yields
the exact no-wrap premise needed by repaired thirteen-bit age soundness. -/
theorem repaired_previous_of_mem_stream {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal ReceiptCandidateRouting.candidateTable tr tt pub)
    {e : Nat} {bs : List ListBlock} (hc : ListChain tr tt 0 bs e)
    (hmem : ∀ m : List Fp,
      0<tableBusCount ReceiptCandidateRouting.candidateTable.interactions tr tt pub B_MEM false m →
      (m.getD 1 0).toNat≤2^22) :
    ∀ x∈flatR (bs.map (ListBlock.view tr tt)), x.tprev≤2^22 := by
  intro x hx
  let m : Msg := [x.kslot,x.tprev,0,x.bef.getD 0 0,x.lk.getD 0 0,x.st.getD 0 0]
  have hm : m∈rcptRecvs3 (bs.map (ListBlock.view tr tt)) B_MEM := memory_version_read hx
  have ht := (repaired_view_traffic hL hc B_MEM m.toFp).2
  have hp : 0<tableBusCount ReceiptCandidateRouting.candidateTable.interactions tr tt pub B_MEM false m.toFp := by
    rw [ht]
    exact List.count_pos_iff.mpr (List.mem_map.mpr ⟨m,hm,rfl⟩)
  have hb := hmem m.toFp hp
  have hc' := extracted_previous_canonical hx
  simpa [m,Msg.toFp,Fp.toNat_ofNat,Nat.mod_eq_of_lt hc'] using hb

/-- Full repaired receipt soundness from actual physical MEM version bounds. -/
theorem repaired_sound_of_mem_stream {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal ReceiptCandidateRouting.candidateTable tr tt pub)
    {e : Nat} {bs : List ListBlock} (hc : ListChain tr tt 0 bs e)
    (hp : ReceiptPublicRanges pub)
    (hmem : ∀ m : List Fp,
      0<tableBusCount ReceiptCandidateRouting.candidateTable.interactions tr tt pub B_MEM false m →
      (m.getD 1 0).toNat≤2^22) :
    RcptV3Wf pub (bs.map (ListBlock.view tr tt)) ∧
      TableTraffic ReceiptCandidateRouting.candidateTable.interactions tr tt pub
        (rcptTraffic3 pub (bs.map (ListBlock.view tr tt))) :=
  repaired_view_sound_of_flat hL hc hp (repaired_previous_of_mem_stream hL hc hmem)

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
