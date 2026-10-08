import ZkFormal.NearV3.Assembly.RcptStateReceiptEnd
import ZkFormal.NearV3.Assembly.Compute
import ZkFormal.NearV3.Rcpt.Candidates.PreparedSourceCount

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 Sched

/-- The source-plan correspondence is an exact ordinary length equality;
receipt count is derived from actual execution, including system receipts. -/
theorem native_plannedRows_capacity {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (lists : List (List Input))
    (hsource : lists.length=p.lists.length)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true)
    {ctx : ApplyCtx} {t : PTrie} {out : MainOut}
    (hrun : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (hgas : ctx.gasLimit≤maxGasLimitD0) :
    (plannedRows lists).length≤2147802 ∧ (plannedRows lists).length<2^22 := by
  have hs := Rcpt.Candidates.prepD0_source_count hp
  have hn := applyNewChunk_receipt_bound hrun hgas
  have hr := plannedRows_bound lists hw
  have hc : (lists.flatten.map Input.receipt).length=(lists.map List.length).sum := by rw [List.length_map,List.length_flatten]
  rw [hc] at hn
  rw [hsource] at hr
  constructor <;> omega

theorem native_receipt_list_count {ctx : ApplyCtx} {t : PTrie} {out : MainOut}
    (lists : List (List Input))
    (hrun : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (hgas : ctx.gasLimit≤maxGasLimitD0) : ∀xs∈lists,xs.length<2^16 := by
  have hn := applyNewChunk_receipt_bound hrun hgas
  intro xs hx
  have hs : xs.length≤lists.flatten.length := by
    have hh : xs.Sublist lists.flatten := List.sublist_flatten_of_mem hx
    exact hh.length_le
  simp only [List.length_map] at hn
  omega

end ZkFormal.NearV3.Assembly.RcptSkeleton
