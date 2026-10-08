import ZkFormal.NearV3.Assembly.RcptGasTokenLocal

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3

theorem planned_receipt_token_bound (ctx : ApplyCtx) (lists : List (List Input))
    (p : ReceiptPlan) (row : Coord) (hm : PlannedRow.receipt p row∈plannedRows lists)
    {t : PTrie} {out : MainOut}
    (hrun : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out) :
    (receiptPlanToken ctx lists p).before+(receiptPlanToken ctx lists p).burnt<256^16 := by
  have hr : (lists.flatten.map Input.receipt)[p.receiptIndex]?=some p.input.receipt := by
    rw [←plannedSegments_rows] at hm
    obtain ⟨seg,hseg,hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨r,_,he⟩ := List.mem_map.mp hm
    cases seg with
    | header => cases he
    | receipt p' s => cases he;exact plannedSegment_receipt_input lists p s hseg
  have hh := (applyNewChunk_token_ledger prims ctx t _ out hrun).2.2
  apply (hh _ (List.mem_of_getElem? (tokenLedger_get ctx _ 0 _ _ hr))).2

end ZkFormal.NearV3.Assembly.RcptSkeleton
