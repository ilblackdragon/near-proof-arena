import ZkFormal.NearV3.Assembly.CompactUnaryDigestTargets
import ZkFormal.NearV3.Assembly.CompactBranchValueTargets
import ZkFormal.NearV3.Assembly.CompactSplitValueTargets

namespace ZkFormal.NearV3.Assembly.CompactPhysicalDigests
open Render Render.UpsGen ZkFormal.Near

/-- Exactly the parts whose sole demand is the fresh value digest. -/
theorem fresh_only_target (I : UpsInst) (k : Nat) (hf : FieldsOk (part I k))
    (hp : PartOk I k (part I k)) (hw : WindowOk I (part I k))
    (h : (part I k).kind=2∨(part I k).kind=3∨(part I k).kind=4∨(part I k).kind=8∨
      ((part I k).kind=10 ∧ I.ci=8)) :
    (List.range (part I k).q.length).flatMap (nodeDigestMsgs I k)=
      [digestWindow I k (if (part I k).ty=0 then 9+(part I k).qhk else 5) 0 (L I)] := by
  rcases h with h|h|h|h|⟨h,hc⟩
  · rw [fresh_leaf_target I k hf hp (Or.inl h),hp.tyLeaf (by omega),if_pos rfl]
  · rw [branch_value_target I k hf hp (Or.inl h),hp.tyBV (Or.inl h),if_neg (by decide)]
  · rw [branch_value_target I k hf hp (Or.inr h),hp.tyBV (Or.inr h),if_neg (by decide)]
  · rw [fresh_leaf_target I k hf hp (Or.inr h),hp.tyLeaf (by omega),if_pos rfl]
  · have ht:(part I k).ty=3:=(hp.tySpb h).mpr (by omega)
    rw [split_value_copied_targets I k hf hp hw h hc,ht,if_neg (by decide)]

end ZkFormal.NearV3.Assembly.CompactPhysicalDigests
