import ZkFormal.NearV3.Assembly.RcptStateReceiptFlags

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def zeroCurrentTrace : Trace Fp := ⟨fun _=>0,fun _ _ _=>0⟩

theorem plannedTrace_current_family (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (receiptAux : ReceiptPlan→Coord→Nat→Fp)
    (headerAux : ListPlan→Coord→Nat→Fp) (pub : List Fp) (es : List Expr)
    (hfoot : es.all currentExpr=true)
    (hreceipt : ∀p row,p.input.receipt.wf=true→row.length=fieldLen p.input row.state→
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
    obtain ⟨hs,_,hl⟩ := segment_member hr
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
      rw [currentExpr_eval _ (receiptPair constants receiptAux p row row) 0 pos 0 0 pub
        (fun col=>plannedTrace_cell lists log pos constants receiptAux headerAux _ ha col) e hf]
      exact hreceipt p row (planned_receipt_wf lists hw p row (List.mem_of_getElem? ha)) hlen e he

theorem booleanReceiptTrace_firstFlags (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp) :
    ∀e∈receiptFirstConstraints,e.eval
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=0 := by
  intro e he
  unfold booleanReceiptTrace emittedReceiptTrace
  rw [emissionPatch_eval _ _ _ _ _ _ (List.all_eq_true.mp receiptFirstConstraints_footprint.2 e he)]
  apply plannedTrace_current_family lists hw log pos _ _ _ pub receiptFirstConstraints receiptFirstConstraints_footprint.1
    (fun p row _ _=>receipt_firstFlags _ _ p row pub) (fun p i=>header_firstFlags _ p i pub) ?_ e he
  intro e he
  simp only [receiptFirstConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl <;> simp only [eval_mul,eval_mul3,eval_c,eval_not,zeroCurrentTrace] <;> grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
