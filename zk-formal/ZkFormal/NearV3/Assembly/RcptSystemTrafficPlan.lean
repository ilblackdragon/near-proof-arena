import ZkFormal.NearV3.Assembly.RcptSystemTraffic

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def systemRowMessages (p : ReceiptPlan) (row : Coord) (sd : Bool) : List Msg :=
  if row.state==(if sd then sV else sS) && systemLookup p.input.receipt row.index then
    [[p.receiptIndex,row.index,(p.input.receipt.receiverId.getD row.index 0).toNat]] else []

def systemPlannedMessages (sd : Bool) : PlannedRow→List Msg
  | .header _ _=>[]
  | .receipt p row=>systemRowMessages p row sd

theorem system_segment_messages (p : ReceiptPlan) (s len : Nat) (sd : Bool) :
    (segment s len).flatMap (fun row=>systemRowMessages p row sd)=
      if s=(if sd then sV else sS) then systemMessages p.input.receipt p.receiptIndex len else [] := by
  rw [segment,List.flatMap_map]
  by_cases hs : s=(if sd then sV else sS)
  · simp only [Function.comp_def,systemRowMessages,hs,beq_self_eq_true,Bool.true_and,ite_true]
    exact RcptV3Proof.gated_list _ _ _
  · simp [systemRowMessages,hs]

theorem system_receipt_messages (p : ReceiptPlan) (sd : Bool) :
    (plannedReceiptRows p).flatMap (systemPlannedMessages sd)=
      systemMessages p.input.receipt p.receiptIndex
        (if sd then p.input.receipt.receiverId.length else p.input.receipt.signerId.length) := by
  simp only [plannedReceiptRows,List.flatMap_map,Function.comp_def,systemPlannedMessages,
    receiptRows,List.flatMap_assoc,system_segment_messages]
  cases hf : p.input.refund <;> cases sd <;>
    simp [fields,hf,fieldLen,sP,sPL,sV,sVL,sS,sSL,sRID,sT0,sKT,sPK,sGP,sTL,sDEP,sXP0,
      sXRI,sXG,sXST,sXL0,sXLH,sXRH,sXRF,sXRZ,sCL]

theorem system_entity_balance (p : EntityPlan) :
    p.rows.flatMap (systemPlannedMessages true)=p.rows.flatMap (systemPlannedMessages false) := by
  cases p with
  | header p => simp [EntityPlan.rows,List.flatMap_map,systemPlannedMessages]
  | receipt p =>
    rw [EntityPlan.rows,system_receipt_messages,system_receipt_messages]
    exact systemMessages_balance p.input.receipt p.receiptIndex

theorem system_planned_balance (lists : List (List Input)) :
    (plannedRows lists).flatMap (systemPlannedMessages true)=
      (plannedRows lists).flatMap (systemPlannedMessages false) := by
  rw [←entityPlans_rows,List.flatMap_assoc,List.flatMap_assoc]
  have hh : (fun p : EntityPlan=>p.rows.flatMap (systemPlannedMessages true))=
      (fun p : EntityPlan=>p.rows.flatMap (systemPlannedMessages false)) := funext system_entity_balance
  rw [hh]

end ZkFormal.NearV3.Assembly.RcptSkeleton
