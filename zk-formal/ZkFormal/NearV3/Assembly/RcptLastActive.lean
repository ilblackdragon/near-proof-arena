import ZkFormal.NearV3.Assembly.RcptFinalTotals

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- The concrete last-receipt/list gate can only fire on the actual final
active row, including when that row belongs to an empty terminal list. -/
theorem booleanReceiptTrace_lastR_position (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hcap : (plannedRows lists).length<2^log)
    (hl : (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos lastR≠0) :
    ∃a,(plannedRows lists)[pos]?=some a ∧ (plannedRows lists).getLast?=some a := by
  cases ha : (plannedRows lists)[pos]? with
  | none => exact False.elim (hl (booleanReceiptTrace_padding own ctx lists log pos constants pub digests fallback headerFallback ha lastR))
  | some a =>
    refine ⟨a,rfl,?_⟩
    have hb : (plannedRows lists)[pos+1]?=none := by
      cases hb : (plannedRows lists)[pos+1]? with
      | none => rfl
      | some b =>
        have hpos : pos+1<2^log := by have hh := (List.getElem?_eq_some_iff.mp hb).1;omega
        have hc := booleanReceiptTrace_listBoundaries own ctx lists hw log pos constants pub digests fallback headerFallback hcap
          (sub (c lastR) (.mul (c le) (Dsl.not (n act)))) (by simp [listBoundaryConstraints])
        have hact := booleanReceiptTrace_control own ctx lists log (pos+1) constants pub digests fallback headerFallback act (by decide)
        rw [hb] at hact
        have ht : (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).height 0=2^log := rfl
        simp only [eval_sub,eval_c,eval_mul,eval_not,eval_n,ht,Nat.mod_eq_of_lt hpos] at hc
        have hact' : (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 (pos+1) act=1 := hact
        rw [hact'] at hc
        have hh : (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos lastR=0 := by grind only
        exact False.elim (hl hh)
    have hp := (List.getElem?_eq_some_iff.mp ha).1
    have hn := List.getElem?_eq_none_iff.mp hb
    rw [List.getLast?_eq_getElem?,show (plannedRows lists).length-1=pos by omega]
    exact ha

end ZkFormal.NearV3.Assembly.RcptSkeleton
