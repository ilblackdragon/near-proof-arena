import ZkFormal.NearV3.Rcpt.Candidates.NativeReceiptMemLedger
namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Near RcptV3
open Rcpt.Candidates.NodePostUpdate
/-- Original account IDs and timestamps are canonically bounded using actual
native account allocation and the accepted execution's receipt bound. -/
theorem native_receipt_mem_bounds (ctx : ApplyCtx) (lists : List (List Input))
    (original replay : PTrie) (as : List AcctV)
    (ha:nativeAccountViews original replay (lists.flatten.map Input.receipt)=some as)
    (hn:(NearSpecV3.valsOf original).length<Algebra.P)
    {t : PTrie} {out : MainOut}
    (hrun:applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (hgas:ctx.gasLimit≤maxGasLimitD0)
    (p : ReceiptPlan) (row : Coord) (hm:PlannedRow.receipt p row∈plannedRows lists) :
    let slot:=accountSlot original ((lists.flatten.map Input.receipt).map (fun r=>accountKeyPath r.receiverId)) p.receiptIndex
    valueIndex original (accountKeyPath p.input.receipt.receiverId)=some slot ∧
    slot<Algebra.P ∧ p.receiptIndex<Algebra.P ∧ depositPlanPrevious lists p<Algebra.P := by
  have hi:=planned_receipt_native_index lists p row hm
  obtain ⟨vid,hv⟩:=nativeAccountViews_keys_defined ha _
    (List.mem_map.mpr ⟨p.input.receipt,List.mem_of_getElem? hi,rfl⟩)
  have hs:accountSlot original ((lists.flatten.map Input.receipt).map (fun r=>accountKeyPath r.receiverId)) p.receiptIndex=vid:=by
    simp only [accountSlot,List.getD_eq_getElem?_getD,List.getElem?_map,hi,Option.map_some,Option.getD_some,hv]
  have hb:=planned_receipt_native_bound ctx lists hrun hgas p row hm
  have hp:p.receiptIndex<Algebra.P:=by unfold Algebra.P;omega
  exact ⟨hs ▸ hv,hs ▸ Nat.lt_trans (valueIndex_bound hv) hn,hp,
    Nat.lt_of_le_of_lt (depositPlanPrevious_bound lists p) hp⟩
end ZkFormal.NearV3.Assembly.RcptSkeleton
