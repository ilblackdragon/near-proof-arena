import ZkFormal.NearV3.Assembly.RcptGasBorrowCurrent

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def gasBorrowTransition : Expr := mul3 (c sGP) (Dsl.not (c fe)) (sub (n c1) (c (xb 8)))

theorem gasBorrow_transition_mem : gasBorrowTransition∈cGas := by simp [gasBorrowTransition,cGas,gp]

theorem gasBorrow_transition_off (tr : Trace Fp) (pos : Nat) (pub : List Fp)
    (hz : tr.cell 0 pos sGP=0 ∨ tr.cell 0 pos fe=1) : gasBorrowTransition.eval tr 0 pos pub=0 := by
  simp only [gasBorrowTransition,eval_mul3,eval_c,eval_not]
  rcases hz with hz|hz <;> rw [hz] <;> grind only

theorem booleanReceiptTrace_gasBorrowTransition (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hcap : (plannedRows lists).length≤2^log) :
    gasBorrowTransition.eval (booleanReceiptTrace own ctx lists log constants pub digests
      (gasBorrowAux ctx fallback) headerFallback) 0 pos pub=0 := by
  let tr := booleanReceiptTrace own ctx lists log constants pub digests
    (gasBorrowAux ctx fallback) headerFallback
  change gasBorrowTransition.eval tr 0 pos pub=0
  have hc := booleanReceiptTrace_control own ctx lists log pos constants pub digests
    (gasBorrowAux ctx fallback) headerFallback
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    apply gasBorrow_transition_off
    exact Or.inl (booleanReceiptTrace_padding own ctx lists log pos constants pub digests
      (gasBorrowAux ctx fallback) headerFallback ha sGP)
  | some a =>
    have hstate := hc sGP (by decide)
    rw [ha] at hstate
    dsimp only at hstate
    by_cases hs : (eraseRow a).state=sGP
    · cases a with
      | header p row =>
        have hh := planned_header_state lists p row (List.mem_of_getElem? ha)
        change row.state=sGP at hs
        rw [hh] at hs
        contradiction
      | receipt p row =>
        change row.state=sGP at hs
        by_cases he : row.index+1=row.length
        · apply gasBorrow_transition_off
          apply Or.inr
          have hf := hc fe (by decide)
          rw [ha] at hf
          simpa only [eraseRow,controlCell,idx,act,fs,fe,Nat.reduceEqDiff,ite_true,ite_false,he] using hf
        · have hi := planned_row_coord_bound lists (.receipt p row) (List.mem_of_getElem? ha)
          change row.index<row.length at hi
          have hl := planned_receipt_field_length lists p row (List.mem_of_getElem? ha)
          rw [hs] at hl
          change row.length=16 at hl
          have hn := planned_receipt_next lists pos p row ha (by omega)
          have hpos : pos+1<2^log := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hn).1 hcap
          have hc1 := booleanReceiptTrace_planned_cell own ctx lists log (pos+1) constants pub digests
            (gasBorrowAux ctx fallback) headerFallback _ hn c1 (by decide)
          have h1 : tr.cell 0 (pos+1) c1=Fp.ofNat (gasBorrow ctx p.input.receipt (row.index+1)) := by
            apply hc1.trans
            cases row with
            | mk state i len =>
              dsimp only at hs
              subst state
              exact gasBorrow_cell ctx constants pub digests (receiptPlanToken ctx lists) fallback p (i+1) len
          have hcur := booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests
            (gasBorrowAux ctx fallback) headerFallback _ ha (xb 8) (by decide)
          have h0 : tr.cell 0 pos (xb 8)=Fp.ofNat (gasBorrow ctx p.input.receipt (row.index+1)) := by
            apply hcur.trans
            cases row with
            | mk state i len =>
              dsimp only at hs
              subst state
              exact gasBorrow_next_bit_cell ctx constants pub digests (receiptPlanToken ctx lists) fallback p i len
          simp only [gasBorrowTransition,eval_mul3,eval_sub,eval_n,eval_c]
          change _ * _ * (tr.cell 0 ((pos+1)%2^log) c1-tr.cell 0 pos (xb 8))=0
          rw [Nat.mod_eq_of_lt hpos,h1,h0]
          grind only
    · apply gasBorrow_transition_off
      exact Or.inl (hstate.trans (by rw [control_state _ (by decide),if_neg (Ne.symm hs)]))

end ZkFormal.NearV3.Assembly.RcptSkeleton
