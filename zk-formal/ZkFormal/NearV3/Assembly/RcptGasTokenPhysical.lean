import ZkFormal.NearV3.Assembly.RcptGasTokenTransition

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem booleanReceiptTrace_gasToken (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    {t : PTrie} {out : MainOut}
    (hrun : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (hcap : (plannedRows lists).length≤2^log) :
    ∀e∈gasAccumulatorConstraints,e.eval (booleanReceiptTrace own ctx lists log constants
      pub digests (gasTokenAux (receiptPlanToken ctx lists) fallback) headerFallback) 0 pos pub=0 := by
  intro e he
  have hh : e∈gasAccumulatorCurrent ∨ e=gasAccumulatorTransition := by
    change e∈[_,_,_,_] at he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    simp only [gasAccumulatorCurrent,gasAccumulatorTransition,gp,List.mem_cons,List.not_mem_nil,or_false] at he ⊢
    grind only
  rcases hh with hh|rfl
  · exact booleanReceiptTrace_gasTokenCurrent own ctx lists hrun log pos constants pub digests fallback headerFallback e hh
  · exact booleanReceiptTrace_gasAccumulatorTransition own ctx lists log pos constants pub digests fallback headerFallback hcap

end ZkFormal.NearV3.Assembly.RcptSkeleton
