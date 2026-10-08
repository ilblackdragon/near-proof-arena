import ZkFormal.NearV3.Assembly.RcptBooleanCells

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem planned_receipt_wf (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (p : ReceiptPlan) (row : Coord)
    (hp : PlannedRow.receipt p row∈plannedRows lists) : p.input.receipt.wf=true := by
  rw [←plannedSegments_rows] at hp
  obtain ⟨seg,hs,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨a,_,he⟩ := List.mem_map.mp hp
  cases seg with
  | header lp => cases he
  | receipt rp s =>
    cases he
    have hm := List.mem_of_getElem? (plannedSegment_receipt_input lists p s hs)
    obtain ⟨x,hx,he⟩ := List.mem_map.mp hm
    obtain ⟨xs,hxs,hx⟩ := List.mem_flatten.mp hx
    simpa only [he] using hw xs hxs x hx

def booleanReceiptTrace (own : Nat) (ctx : ApplyCtx) (lists : List (List Input)) (log : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp) : Trace Fp :=
  emittedReceiptTrace own ctx lists log (booleanConstants constants) pub digests
    (booleanReceiptAux fallback) (booleanHeaderAux headerFallback)

set_option maxRecDepth 4096 in
theorem boolCols_noEmission : ∀col∈boolCols,emissionColumn col=false := by decide

theorem booleanReceiptTrace_cells (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (col : Nat) (hc : col∈boolCols) :
    BooleanValue ((booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos col) := by
  unfold booleanReceiptTrace emittedReceiptTrace
  rw [emissionPatch_other _ _ _ _ _ _ (boolCols_noEmission col hc)]
  unfold emittedReceiptBase nativeReceiptTrace
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    rw [plannedTrace_padding lists log pos _ _ _ (List.getElem?_eq_none_iff.mp ha) col]
    exact Or.inl rfl
  | some a =>
    rw [plannedTrace_cell lists log pos _ _ _ a ha col]
    cases a with
    | header p row =>
      apply headerCell_boolean _ _ _ _ _ hc
      intro p row col hc
      apply headerStreamAux_boolean
      · intro p row col hc
        unfold emissionHeaderFallback
        split
        · exact Or.inl rfl
        · exact boolInput_boolean col _ hc
      · exact hc
    | receipt p row =>
      apply receiptCell_boolean
      · intro p col hc;exact boolInput_boolean col _ hc
      · intro p row col hc
        apply streamAux_boolean
        · intro p row col hc
          apply tokenAux_boolean
          · intro p row col hc;exact boolInput_boolean col _ hc
          · exact hc
        · exact hc
      · exact planned_receipt_wf lists hw p row (List.mem_of_getElem? ha)
      · exact hc

end ZkFormal.NearV3.Assembly.RcptSkeleton
