import ZkFormal.NearV3.Render.Ups.CompactSuccessor
namespace ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Near.Render.EvI ZkFormal.Algebra ZkFormal.Air UpsGen
theorem compact_groupOk_by {insts : List UpsInst} (hpos : 0<insts.length)
    {H : Nat} (hH : compactR insts+1≤H) {es : List Expr}
    (hsub : ∀e∈es,e∈compactConstraints)
    (hW : ∀ i,i<insts.length → ∀ t,t<4 → ∀ q,q<compactR insts → (compactRecs insts).getD q default=(i,.w t) → ∀ C D P : Nat→Int,
      (∀ x,x<200 → C x=WC (inst insts i) t x) →
      (∀x,x<200 → D x=compactNextCell insts q x) →
      ∀ex∈es,((ev C D (if q=0 then 1 else 0) 0 1 P ex : Int) : Fp)=0)
    (hQ : ∀ i,i<insts.length → ∀ k p,k<nQ (inst insts i) → p<(part (inst insts i) k).q.length →
      ∀ q,q<compactR insts → (compactRecs insts).getD q default=(i,.q k p) → ∀ C D P : Nat→Int,
      (∀x,x<200 → C x=QC (inst insts i) (part (inst insts i) k) k p
        (fieldAt (part (inst insts i) k).shape p).1
        (fieldAt (part (inst insts i) k).shape p).2.1
        (fieldAt (part (inst insts i) k).shape p).2.2.1
        (fieldAt (part (inst insts i) k).shape p).2.2.2 (compactU insts q) x) →
      (∀x,x<200 → D x=compactNextCell insts q x) →
      ∀ex∈es,((ev C D (if q=0 then 1 else 0) 0 1 P ex : Int) : Fp)=0) : CompactGroupOk insts H es := by
  apply compact_groupOk_of hpos hH hsub
  intro q hq C D P hC hD e he
  have hm := compact_mem.mp (compact_get_mem hq)
  rcases hr : (compactRecs insts).getD q default with ⟨i,rk⟩
  rw [hr] at hm hC
  simp only at hm
  rcases compact_mem_I.mp hm.2 with ⟨t,ht,rfl⟩|⟨k,p,hk,hp,rfl⟩
  · exact hW i hm.1 t ht q hq hr C D P hC hD e he
  · exact hQ i hm.1 k p hk hp q hq hr C D P hC hD e he

end ZkFormal.NearV3.Render.UpsRelay
