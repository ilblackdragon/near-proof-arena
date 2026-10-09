import ZkFormal.NearV3.Assembly.RcptPredecessorStep

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render ZkFormal.Near.Render.RcptGen ZkFormal.Near.Render.RcptP

theorem predecessorStep_zero (tr : Trace Fp) (pos : Nat) (pub : List Fp)
    (hz : tr.cell 0 pos sP=0 ∨ tr.cell 0 pos fe=1) :
    predecessorStepConstraint.eval tr 0 pos pub=0 := by
  simp only [predecessorStepConstraint,eval_mul3,eval_c,eval_not]
  rcases hz with hz|hz <;> rw [hz] <;> grind only

set_option maxRecDepth 4096 in
theorem booleanReceiptTrace_predecessorStep (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (hcap : (plannedRows lists).length≤2^log) :
    predecessorStepConstraint.eval
      (booleanReceiptTrace own ctx lists log (nativePriceConstants ctx (systemConstants constants))
        pub digests (predecessorAux fallback) headerFallback) 0 pos pub=0 := by
  let constants' := nativePriceConstants ctx (systemConstants constants)
  let fallback' := predecessorAux fallback
  let tr := booleanReceiptTrace own ctx lists log constants' pub digests fallback' headerFallback
  change predecessorStepConstraint.eval tr 0 pos pub=0
  have hc := booleanReceiptTrace_control own ctx lists log pos constants' pub digests fallback' headerFallback
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    apply predecessorStep_zero
    exact Or.inl (booleanReceiptTrace_padding own ctx lists log pos constants' pub digests fallback' headerFallback ha sP)
  | some a =>
    have hstate := hc sP (by decide)
    rw [ha] at hstate
    dsimp only at hstate
    by_cases hs : (eraseRow a).state=sP
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
        change row.state=sP at hs
        by_cases he : row.index+1=row.length
        · apply predecessorStep_zero
          apply Or.inr
          have hf := hc fe (by decide)
          rw [ha] at hf
          simpa only [eraseRow,controlCell,idx,act,fs,fe,Nat.reduceEqDiff,↓reduceIte,he] using hf
        · have hi := planned_row_coord_bound lists (.receipt p row) (List.mem_of_getElem? ha)
          change row.index<row.length at hi
          have hnext := planned_receipt_next lists pos p row ha (by omega)
          have hpos : pos+1<2^log := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hnext).1 hcap
          have ht : tr.height 0=2^log := rfl
          have hcurr := booleanReceiptTrace_planned_cell own ctx lists log pos constants' pub digests fallback' headerFallback _ ha acc (by decide)
          have hnacc := booleanReceiptTrace_planned_cell own ctx lists log (pos+1) constants' pub digests fallback' headerFallback _ hnext acc (by decide)
          have hnbyte := booleanReceiptTrace_planned_cell own ctx lists log (pos+1) constants' pub digests fallback' headerFallback _ hnext b (by decide)
          have hnreg := booleanReceiptTrace_planned_cell own ctx lists log (pos+1) constants' pub digests fallback' headerFallback _ hnext (reg 0) (by decide)
          have ha0 := (predecessorAux_cells ctx lists constants pub digests fallback p row hs).1
          have ha1 := (predecessorAux_cells ctx lists constants pub digests fallback p (advance row) hs).1
          have hb1 := predecessor_bytes (booleanConstants constants') pub digests
            (tokenAux (receiptPlanToken ctx lists) (booleanReceiptAux fallback')) p (advance row) hs
          have h0 : tr.cell 0 pos acc=Fp.ofNat (accP (characterData p.input.receipt) row.index) := hcurr.trans ha0
          have h1 : tr.cell 0 (pos+1) acc=Fp.ofNat (accP (characterData p.input.receipt) (row.index+1)) := hnacc.trans ha1
          have hb : tr.cell 0 (pos+1) b=Fp.ofNat ((characterData p.input.receipt).pred.getD (row.index+1) 0) := hnbyte.trans hb1.1
          have hr : tr.cell 0 (pos+1) (reg 0)=Fp.ofNat (sysB (row.index+1)) := hnreg.trans hb1.2
          simp only [predecessorStepConstraint,eval_mul3,eval_sub,eval_add,RcptV3.sq,eval_mul,eval_n,eval_c,
            ht,Nat.mod_eq_of_lt hpos,h0,h1,hb,hr]
          have hh := predecessor_score_step p.input.receipt row.index
          grind only
    · apply predecessorStep_zero
      apply Or.inl
      exact hstate.trans (by rw [control_state _ (by decide),if_neg (Ne.symm hs)])

end ZkFormal.NearV3.Assembly.RcptSkeleton
