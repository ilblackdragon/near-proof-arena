import ZkFormal.NearV3.Render.Ups.CompactFrame
import ZkFormal.NearV3.Render.Ups.GBool
import ZkFormal.NearV3.Render.Ups.GPlan

namespace ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Near.Render.EvI ZkFormal.Algebra ZkFormal.Air UpsGen

/-- Current-row constraints reuse the existing node/walk lemmas verbatim. -/
theorem compact_current_group {insts : List UpsInst} (hpos : 0<insts.length)
    {H : Nat} (hH : compactR insts+1≤H) {es : List Expr}
    (hsub : ∀e∈es,e∈compactConstraints)
    (hW : ∀ i,i<insts.length → ∀ t,t<4 → ∀ C D P : Nat→Int,∀ fst lst trn : Int,
      (∀ x,x<200 → C x=WC (inst insts i) t x) →
      ∀ex∈es,((ev C D fst lst trn P ex : Int) : Fp)=0)
    (hQ : ∀ i,i<insts.length → ∀ k p,k<nQ (inst insts i) → p<(part (inst insts i) k).q.length →
      ∀ u,∀ C D P : Nat→Int,∀ fst lst trn : Int,
      (∀x,x<200 → C x=QC (inst insts i) (part (inst insts i) k) k p
        (fieldAt (part (inst insts i) k).shape p).1
        (fieldAt (part (inst insts i) k).shape p).2.1
        (fieldAt (part (inst insts i) k).shape p).2.2.1
        (fieldAt (part (inst insts i) k).shape p).2.2.2 u x) →
      ∀ex∈es,((ev C D fst lst trn P ex : Int) : Fp)=0) : CompactGroupOk insts H es := by
  apply compact_groupOk_of hpos hH hsub
  intro q hq C D P hC hD e he
  have hm := compact_mem.mp (compact_get_mem hq)
  rcases hr : (compactRecs insts).getD q default with ⟨i,rk⟩
  rw [hr] at hm hC
  simp only at hm
  rcases compact_mem_I.mp hm.2 with ⟨t,ht,rfl⟩|⟨k,p,hk,hp,rfl⟩
  · exact hW i hm.1 t ht C D P _ _ _ hC e he
  · exact hQ i hm.1 k p hk hp (compactU insts q) C D P _ _ _ hC e he

theorem compact_cBool {insts : List UpsInst} (hpos : 0<insts.length)
    (hi : ∀ I∈insts,InstOk I) {H : Nat} (hH : compactR insts+1≤H) :
    CompactGroupOk insts H UpsV3.cBool := by
  apply compact_current_group hpos hH (fun e he=>by simp [compactConstraints,he])
  · intro i hi' t ht C D P fst lst trn hC
    exact cBool_w (hi _ (inst_mem hi')) ht hC
  · intro i hi' k p hk hp u C D P fst lst trn hC
    exact cBool_q ((hi _ (inst_mem hi')).bits k hk) hC

theorem compact_cPlan {insts : List UpsInst} (hpos : 0<insts.length)
    (hi : ∀ I∈insts,InstOk I)
    (hp : ∀I∈insts,∀k,k<nQ I → PartOk I k (part I k))
    {H : Nat} (hH : compactR insts+1≤H) : CompactGroupOk insts H UpsV3.cPlan := by
  apply compact_current_group hpos hH (fun e he=>by simp [compactConstraints,he])
  · intro i hi' t ht C D P fst lst trn hC
    exact plan_w hC
  · intro i hi' k p hk hpp u C D P fst lst trn hC
    by_cases h0 : p=0
    · subst p
      exact plan_q0 (hi _ (inst_mem hi')) (hp _ (inst_mem hi') k hk) hC
    · exact plan_qn h0 hC
end ZkFormal.NearV3.Render.UpsRelay
