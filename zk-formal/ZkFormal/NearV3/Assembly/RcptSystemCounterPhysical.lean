import ZkFormal.NearV3.Assembly.RcptSystemLookupPhysical

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render ZkFormal.Near.Render.RcptGen ZkFormal.Near.Render.RcptP

def systemCounterConstraint : Expr :=
  mul3 (c sS) (Dsl.not (c fe)) (sub (n scnt) (.add (c scnt) (n gS)))

theorem systemCounter_zero (tr : Trace Fp) (pos : Nat) (pub : List Fp)
    (hz : tr.cell 0 pos sS=0 ∨ tr.cell 0 pos fe=1) :
    systemCounterConstraint.eval tr 0 pos pub=0 := by
  simp only [systemCounterConstraint,eval_mul3,eval_c,eval_not]
  rcases hz with hz|hz <;> rw [hz] <;> grind only

set_option maxRecDepth 4096 in
theorem booleanReceiptTrace_systemCounter (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (hcap : (plannedRows lists).length≤2^log) :
    systemCounterConstraint.eval
      (booleanReceiptTrace own ctx lists log (nativePriceConstants ctx (systemConstants (systemIdentityConstants constants)))
        pub digests (systemAux fallback) (systemHeaderAux headerFallback)) 0 pos pub=0 := by
  let constants' := nativePriceConstants ctx (systemConstants (systemIdentityConstants constants))
  let fallback' := systemAux fallback
  let tr := booleanReceiptTrace own ctx lists log constants' pub digests fallback' (systemHeaderAux headerFallback)
  change systemCounterConstraint.eval tr 0 pos pub=0
  have hc := booleanReceiptTrace_control own ctx lists log pos constants' pub digests fallback' (systemHeaderAux headerFallback)
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    apply systemCounter_zero
    exact Or.inl (booleanReceiptTrace_padding own ctx lists log pos constants' pub digests fallback' (systemHeaderAux headerFallback) ha sS)
  | some a =>
    have hstate := hc sS (by decide)
    rw [ha] at hstate
    dsimp only at hstate
    by_cases hs : (eraseRow a).state=sS
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
        change row.state=sS at hs
        by_cases he : row.index+1=row.length
        · apply systemCounter_zero
          apply Or.inr
          have hf := hc fe (by decide)
          rw [ha] at hf
          simpa only [eraseRow,controlCell,idx,act,fs,fe,Nat.reduceEqDiff,↓reduceIte,he] using hf
        · have hi := planned_row_coord_bound lists (.receipt p row) (List.mem_of_getElem? ha)
          change row.index<row.length at hi
          have hnext := planned_receipt_next lists pos p row ha (by omega)
          have hpos : pos+1<2^log := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hnext).1 hcap
          have ht : tr.height 0=2^log := rfl
          have hc0 := booleanReceiptTrace_planned_cell own ctx lists log pos constants' pub digests fallback' (systemHeaderAux headerFallback) _ ha scnt (by decide)
          have hc1 := booleanReceiptTrace_planned_cell own ctx lists log (pos+1) constants' pub digests fallback' (systemHeaderAux headerFallback) _ hnext scnt (by decide)
          have hg1 := booleanReceiptTrace_planned_cell own ctx lists log (pos+1) constants' pub digests fallback' (systemHeaderAux headerFallback) _ hnext gS (by decide)
          have h0 : tr.cell 0 pos scnt=Fp.ofNat (systemLookupCount p.input.receipt row.index) :=
            hc0.trans (systemAux_transport ctx lists constants' pub digests fallback p row scnt (by decide))
          have h1 : tr.cell 0 (pos+1) scnt=Fp.ofNat (systemLookupCount p.input.receipt (row.index+1)) :=
            hc1.trans (systemAux_transport ctx lists constants' pub digests fallback p (advance row) scnt (by decide))
          have hg : tr.cell 0 (pos+1) gS=bitCell (systemLookup p.input.receipt (row.index+1)) := by
            have hh := hg1.trans (systemAux_transport ctx lists constants' pub digests fallback p (advance row) gS (by decide))
            simpa only [systemAux,gV,gS,Nat.reduceEqDiff,↓reduceIte,advance,hs,beq_self_eq_true,Bool.true_and] using hh
          simp only [systemCounterConstraint,eval_mul3,eval_sub,eval_add,eval_n,eval_c,
            ht,Nat.mod_eq_of_lt hpos]
          rw [h0,h1,hg]
          have hh := congrArg Fp.ofNat (systemLookupCount_step p.input.receipt row.index)
          rw [ofNat_add_e,system_bit_nat] at hh
          rw [hh]
          grind only

    · apply systemCounter_zero
      apply Or.inl
      exact hstate.trans (by rw [control_state _ (by decide),if_neg (Ne.symm hs)])

end ZkFormal.NearV3.Assembly.RcptSkeleton
