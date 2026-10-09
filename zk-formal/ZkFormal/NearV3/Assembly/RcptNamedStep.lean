import ZkFormal.NearV3.Assembly.RcptNamedStart

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render ZkFormal.Near.Render.RcptGen ZkFormal.Near.Render.RcptP

def namedStepConstraint : Expr :=
  mul3 (c sV) (Dsl.not (c fe)) (sub (n acc) (.add (c acc) hexN))

theorem namedStep_in_chars : namedStepConstraint∈cChars := by
  simp only [namedStepConstraint,cChars,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  grind only

theorem namedStep_zero (tr : Trace Fp) (pos : Nat) (pub : List Fp)
    (hz : tr.cell 0 pos sV=0 ∨ tr.cell 0 pos fe=1) :
    namedStepConstraint.eval tr 0 pos pub=0 := by
  simp only [namedStepConstraint,eval_mul3,eval_c,eval_not]
  rcases hz with hz|hz <;> rw [hz] <;> grind only

set_option maxRecDepth 4096 in
theorem booleanReceiptTrace_namedStep (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (hcap : (plannedRows lists).length≤2^log) :
    namedStepConstraint.eval
      (booleanReceiptTrace own ctx lists log constants
        pub digests (characterAux (namedAux fallback)) (characterHeaderAux headerFallback)) 0 pos pub=0 := by
  let constants' := constants
  let fallback' := characterAux (namedAux fallback)
  let tr := booleanReceiptTrace own ctx lists log constants' pub digests fallback' (characterHeaderAux headerFallback)
  change namedStepConstraint.eval tr 0 pos pub=0
  have hc := booleanReceiptTrace_control own ctx lists log pos constants' pub digests fallback' (characterHeaderAux headerFallback)
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    apply namedStep_zero
    exact Or.inl (booleanReceiptTrace_padding own ctx lists log pos constants' pub digests fallback' (characterHeaderAux headerFallback) ha sV)
  | some a =>
    have hstate := hc sV (by decide)
    rw [ha] at hstate
    dsimp only at hstate
    by_cases hs : (eraseRow a).state=sV
    · cases a with
      | header p row =>
        have hm := List.mem_of_getElem? ha
        rw [←plannedSegments_rows] at hm
        obtain ⟨seg,_,hm⟩ := List.mem_flatMap.mp hm
        obtain ⟨c,hc,he⟩ := List.mem_map.mp hm
        have hh := (segment_member hc).1
        cases seg <;> cases he
        change row.state=sCL at hh
        simp only [eraseRow] at hs
        rw [hh] at hs
        contradiction
      | receipt p row =>
        change row.state=sV at hs
        by_cases he : row.index+1=row.length
        · apply namedStep_zero
          apply Or.inr
          have hf := hc fe (by decide)
          rw [ha] at hf
          simpa only [eraseRow,controlCell,idx,act,fs,fe,Nat.reduceEqDiff,↓reduceIte,he] using hf
        · have hi := planned_row_coord_bound lists (.receipt p row) (List.mem_of_getElem? ha)
          change row.index<row.length at hi
          have hnext := planned_receipt_next lists pos p row ha (by omega)
          have hpos : pos+1<2^log := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hnext).1 hcap
          have ht : tr.height 0=2^log := rfl
          have hw' := planned_receipt_wf lists hw p row (List.mem_of_getElem? ha)
          have h0 := booleanReceiptTrace_named_cells own ctx lists log pos constants pub digests fallback headerFallback p row ha acc (by decide)
          have h1 := booleanReceiptTrace_named_cells own ctx lists log (pos+1) constants pub digests fallback headerFallback p (advance row) hnext acc (by decide)
          have hnhex := booleanReceiptTrace_named_hex own ctx lists log (pos+1) constants pub digests fallback headerFallback p (advance row) hnext hs hw'
          have hhexN : hexN.eval tr 0 pos pub=Fp.ofNat (b2n (isHexC ((characterData p.input.receipt).recv.getD (row.index+1) 0))) := by
            simp only [hexN,eval_add,eval_n,ht,Nat.mod_eq_of_lt hpos]
            simpa only [hexE,eval_add,eval_c,advance] using hnhex
          simp only [namedStepConstraint,eval_mul3,eval_sub,eval_add,eval_c,eval_n,ht,Nat.mod_eq_of_lt hpos,hhexN]
          rw [h0,h1]
          simp only [namedAux,hs,advance,acc,↓reduceIte]
          have hh := named_score_step p.input.receipt row.index
          grind only

    · apply namedStep_zero
      apply Or.inl
      exact hstate.trans (by rw [control_state _ (by decide),if_neg (Ne.symm hs)])

end ZkFormal.NearV3.Assembly.RcptSkeleton
