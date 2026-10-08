import ZkFormal.NearV3.Assembly.RcptGasTokenCurrent

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def gasAccumulatorTransition : Expr := mul3 (c sGP) (Dsl.not (c fe)) (sub (n c4) (c (xb 39)))

theorem gasAccumulator_transition_mem : gasAccumulatorTransition∈cGas := by simp [gasAccumulatorTransition,cGas,gp]

theorem gasAccumulator_transition_off (tr : Trace Fp) (pos : Nat) (pub : List Fp)
    (hz : tr.cell 0 pos sGP=0 ∨ tr.cell 0 pos fe=1) : gasAccumulatorTransition.eval tr 0 pos pub=0 := by
  simp only [gasAccumulatorTransition,eval_mul3,eval_c,eval_not]
  rcases hz with hz|hz <;> rw [hz] <;> grind only

theorem booleanReceiptTrace_gasAccumulatorTransition (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hcap : (plannedRows lists).length≤2^log) :
    gasAccumulatorTransition.eval (booleanReceiptTrace own ctx lists log constants pub digests
      (gasTokenAux (receiptPlanToken ctx lists) fallback) headerFallback) 0 pos pub=0 := by
  let tr := booleanReceiptTrace own ctx lists log constants pub digests
    (gasTokenAux (receiptPlanToken ctx lists) fallback) headerFallback
  change gasAccumulatorTransition.eval tr 0 pos pub=0
  have hc := booleanReceiptTrace_control own ctx lists log pos constants pub digests
    (gasTokenAux (receiptPlanToken ctx lists) fallback) headerFallback
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    apply gasAccumulator_transition_off
    exact Or.inl (booleanReceiptTrace_padding own ctx lists log pos constants pub digests
      (gasTokenAux (receiptPlanToken ctx lists) fallback) headerFallback ha sGP)
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
        · apply gasAccumulator_transition_off
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
            (gasTokenAux (receiptPlanToken ctx lists) fallback) headerFallback _ hn c4 (by decide)
          have h1 : tr.cell 0 (pos+1) c4=Fp.ofNat (gasTokenCarry (receiptPlanToken ctx lists p) (row.index+1)) := by
            apply hc1.trans
            cases row with
            | mk state i len =>
              dsimp only at hs
              subst state
              exact gasToken_carry_cell (receiptPlanToken ctx lists) constants pub digests fallback p (i+1) len
          have hcur := booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests
            (gasTokenAux (receiptPlanToken ctx lists) fallback) headerFallback _ ha (xb 39) (by decide)
          have h0 : tr.cell 0 pos (xb 39)=Fp.ofNat (gasTokenCarry (receiptPlanToken ctx lists p) (row.index+1)) := by
            apply hcur.trans
            cases row with
            | mk state i len =>
              dsimp only at hs
              subst state
              exact gasToken_next_carry_cell (receiptPlanToken ctx lists) constants pub digests fallback p i len
          simp only [gasAccumulatorTransition,eval_mul3,eval_sub,eval_n,eval_c]
          change _ * _ * (tr.cell 0 ((pos+1)%2^log) c4-tr.cell 0 pos (xb 39))=0
          rw [Nat.mod_eq_of_lt hpos,h1,h0]
          grind only
    · apply gasAccumulator_transition_off
      exact Or.inl (hstate.trans (by rw [control_state _ (by decide),if_neg (Ne.symm hs)]))

end ZkFormal.NearV3.Assembly.RcptSkeleton
