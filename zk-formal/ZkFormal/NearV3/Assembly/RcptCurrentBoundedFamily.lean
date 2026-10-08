import ZkFormal.NearV3.Assembly.RcptKeyZeroPhysical

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem plannedTrace_current_bounded_family (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (receiptAux : ReceiptPlan→Coord→Nat→Fp)
    (headerAux : ListPlan→Coord→Nat→Fp) (pub : List Fp) (es : List Expr)
    (hfoot : es.all currentExpr=true)
    (hreceipt : ∀p row,p.input∈lists.flatten→p.input.receipt.wf=true→row.length=fieldLen p.input row.state→row.index<fieldLen p.input row.state→
      ∀e∈es,e.eval (receiptPair constants receiptAux p row row) 0 0 pub=0)
    (hheader : ∀p i,∀e∈es,e.eval (⟨fun _=>1,fun _ _ col=>headerCell headerAux p ⟨sCL,i,12⟩ col⟩ : Trace Fp) 0 0 pub=0)
    (hzero : ∀e∈es,e.eval zeroCurrentTrace 0 0 pub=0) :
    ∀e∈es,e.eval (plannedTrace lists log constants receiptAux headerAux) 0 pos pub=0 := by
  intro e he
  have hf := List.all_eq_true.mp hfoot e he
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    rw [currentExpr_eval _ zeroCurrentTrace 0 pos 0 0 pub
      (fun col=>plannedTrace_padding lists log pos constants receiptAux headerAux (List.getElem?_eq_none_iff.mp ha) col) e hf]
    exact hzero e he
  | some a =>
    have hm := List.mem_of_getElem? ha
    rw [←plannedSegments_rows] at hm
    obtain ⟨seg,_,hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨row,hr,hea⟩ := List.mem_map.mp hm
    obtain ⟨hs,hidx,hl⟩ := segment_member hr
    subst a
    cases seg with
    | header p =>
      change row.state=sCL at hs
      change row.length=12 at hl
      cases row with
      | mk state i len =>
        dsimp only at hs hl
        subst state len
        rw [currentExpr_eval _ (⟨fun _=>1,fun _ _ col=>headerCell headerAux p ⟨sCL,i,12⟩ col⟩ : Trace Fp) 0 pos 0 0 pub
          (fun col=>plannedTrace_cell lists log pos constants receiptAux headerAux _ ha col) e hf]
        exact hheader p i e he
    | receipt p s =>
      have hlen : row.length=fieldLen p.input row.state := by
        change row.state=s at hs
        change row.length=fieldLen p.input s at hl
        rw [hs];exact hl
      have hi : row.index<fieldLen p.input row.state := by
        change row.state=s at hs
        rw [hs]
        exact hidx
      rw [currentExpr_eval _ (receiptPair constants receiptAux p row row) 0 pos 0 0 pub
        (fun col=>plannedTrace_cell lists log pos constants receiptAux headerAux _ ha col) e hf]
      exact hreceipt p row (planned_receipt_input_mem lists p row (List.mem_of_getElem? ha)) (planned_receipt_wf lists hw p row (List.mem_of_getElem? ha)) hlen hi e he

end ZkFormal.NearV3.Assembly.RcptSkeleton
