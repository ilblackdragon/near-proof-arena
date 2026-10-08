import ZkFormal.NearV3.Assembly.RcptNamedEndComposition

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render ZkFormal.Near.Render.RcptGen ZkFormal.Near.Render.RcptP

def namedFixedConstraints : List Expr :=
  [mul3 (c sV) (Dsl.not (c fe)) (sub (n vc0) (c vc0)),
   mul3 (c sV) (Dsl.not (c fe)) (sub (n vc1) (c vc1)),
   mul3 (c sV) (Dsl.not (c fe)) (sub (n h01) (c h01))]

theorem namedFixed_in_chars : ∀e∈namedFixedConstraints,e∈cChars := by
  intro e he
  simp only [namedFixedConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  simp only [cChars,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  grind only

theorem namedFixed_zero (tr : Trace Fp) (pos : Nat) (pub : List Fp)
    (hz : tr.cell 0 pos sV=0 ∨ tr.cell 0 pos fe=1) :
    ∀e∈namedFixedConstraints,e.eval tr 0 pos pub=0 := by
  intro e he
  simp only [namedFixedConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl <;> simp only [eval_mul3,eval_c,eval_not]
  all_goals rcases hz with hz|hz <;> rw [hz] <;> grind only

set_option maxRecDepth 4096 in
theorem booleanReceiptTrace_namedFixed (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (hcap : (plannedRows lists).length≤2^log) :
    ∀e∈namedFixedConstraints,e.eval
      (booleanReceiptTrace own ctx lists log (nativePriceConstants ctx (systemConstants constants))
        pub digests (namedAux fallback) headerFallback) 0 pos pub=0 := by
  let constants' := nativePriceConstants ctx (systemConstants constants)
  let fallback' := namedAux fallback
  let tr := booleanReceiptTrace own ctx lists log constants' pub digests fallback' headerFallback
  change ∀e∈namedFixedConstraints,e.eval tr 0 pos pub=0
  have hc := booleanReceiptTrace_control own ctx lists log pos constants' pub digests fallback' headerFallback
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    apply namedFixed_zero
    exact Or.inl (booleanReceiptTrace_padding own ctx lists log pos constants' pub digests fallback' headerFallback ha sV)
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
        · apply namedFixed_zero
          apply Or.inr
          have hf := hc fe (by decide)
          rw [ha] at hf
          simpa only [eraseRow,controlCell,idx,act,fs,fe,Nat.reduceEqDiff,↓reduceIte,he] using hf
        · have hi := planned_row_coord_bound lists (.receipt p row) (List.mem_of_getElem? ha)
          change row.index<row.length at hi
          have hnext := planned_receipt_next lists pos p row ha (by omega)
          have hpos : pos+1<2^log := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hnext).1 hcap
          have ht : tr.height 0=2^log := rfl
          have hfixed : ∀col,col∈[vc0,vc1,h01]→tr.cell 0 (pos+1) col=tr.cell 0 pos col := by
            intro col hcol
            have hall : col∈[acc,vc0,vc1,h01,p1,p2,p3,i1,i2,i3] := by
              simp only [List.mem_cons,List.not_mem_nil,or_false] at hcol ⊢
              grind only
            have hem : emissionColumn col=false := by
              simp only [List.mem_cons,List.not_mem_nil,or_false] at hcol
              rcases hcol with rfl|rfl|rfl <;> decide
            have h0 := (booleanReceiptTrace_planned_cell own ctx lists log pos constants' pub digests fallback' headerFallback _ ha col hem).trans
              (namedAux_transport ctx lists constants' pub digests fallback p row col hall)
            have h1 := (booleanReceiptTrace_planned_cell own ctx lists log (pos+1) constants' pub digests fallback' headerFallback _ hnext col hem).trans
              (namedAux_transport ctx lists constants' pub digests fallback p (advance row) col hall)
            rw [h0,h1]
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hcol
            rcases hcol with rfl|rfl|rfl <;>
              simp [namedAux,hs,advance,acc,vc0,vc1,h01]
          intro e he
          simp only [namedFixedConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
          rcases he with rfl|rfl|rfl
          all_goals
            simp only [eval_mul3,eval_sub,eval_n,eval_c,ht,Nat.mod_eq_of_lt hpos]
            first | rw [hfixed vc0 (by decide)] | rw [hfixed vc1 (by decide)] | rw [hfixed h01 (by decide)]
            grind only

    · apply namedFixed_zero
      apply Or.inl
      exact hstate.trans (by rw [control_state _ (by decide),if_neg (Ne.symm hs)])

end ZkFormal.NearV3.Assembly.RcptSkeleton
