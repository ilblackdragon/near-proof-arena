import ZkFormal.NearV3.Assembly.RcptNativeFlags

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem planned_receipt_input_mem (lists : List (List Input)) (p : ReceiptPlan) (row : Coord)
    (hp : PlannedRow.receipt p row∈plannedRows lists) : p.input∈lists.flatten := by
  rw [←plannedSegments_rows] at hp
  obtain ⟨seg,hs,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨a,_,he⟩ := List.mem_map.mp hp
  cases seg with
  | header lp => cases he
  | receipt rp s =>
    cases he
    obtain ⟨lp,hl,hs⟩ := List.mem_flatMap.mp hs
    simp only [listSegments,List.mem_cons] at hs
    rcases hs with he|hs
    · cases he
    · obtain ⟨rp,hr,hs⟩ := List.mem_flatMap.mp hs
      obtain ⟨state,_,he⟩ := List.mem_map.mp hs
      cases he
      exact List.mem_of_getElem? (global_plan_receipt lists lp hl p hr)

theorem nativePriceConstants_ge (ctx : ApplyCtx) (constants : ReceiptPlan→Nat→Fp)
    (p : ReceiptPlan) :
    booleanConstants (nativePriceConstants ctx constants) p ge=
      bitCell (decide (ctx.gasPrice≤p.input.receipt.gasPrice)) := by
  unfold booleanConstants nativePriceConstants
  rw [if_pos rfl,boolInput_preserves _ _ (bitCell_boolean _)]

theorem booleanReceiptTrace_nativeRefund (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hflags : ∀xs∈lists,∀x∈xs,x.refund=nativeRefund ctx x.receipt)
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) :
    refundSurplusConstraint.eval
      (booleanReceiptTrace own ctx lists log (nativePriceConstants ctx constants) pub digests fallback headerFallback)
      0 pos pub=0 := by
  simp only [refundSurplusConstraint,eval_mul,eval_c,eval_not]
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    rw [booleanReceiptTrace_padding own ctx lists log pos _ pub digests fallback headerFallback ha hr]
    grind only
  | some a =>
    rw [booleanReceiptTrace_planned_cell own ctx lists log pos _ pub digests fallback headerFallback a ha hr (by decide),
      booleanReceiptTrace_planned_cell own ctx lists log pos _ pub digests fallback headerFallback a ha ge (by decide)]
    cases a with
    | header p row =>
      have hz : plannedCell (booleanConstants (nativePriceConstants ctx constants))
          (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux fallback))
          (headerStreamAux own (headerBurn ctx (lists.flatten.map Input.receipt))
            (emissionHeaderFallback (booleanHeaderAux headerFallback))) (.header p row) hr=0 := rfl
      rw [hz]
      grind only
    | receipt p row =>
      have hh : p.input.refund=nativeRefund ctx p.input.receipt := by
        obtain ⟨xs,hxs,hx⟩ := List.mem_flatten.mp (planned_receipt_input_mem lists p row (List.mem_of_getElem? ha))
        exact hflags xs hxs p.input hx
      change bitCell p.input.refund * (1-booleanConstants (nativePriceConstants ctx constants) p ge)=0
      rw [nativePriceConstants_ge]
      by_cases hf : p.input.refund=true
      · have hg := nativeRefund_price ctx p.input.receipt (hh.symm.trans hf)
        simp only [bitCell,hf,hg,decide_true,↓reduceIte]
        grind only
      · simp only [bitCell,hf,↓reduceIte]
        grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
