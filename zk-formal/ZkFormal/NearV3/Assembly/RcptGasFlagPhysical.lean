import ZkFormal.NearV3.Assembly.RcptGasFlagTransition

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem booleanReceiptTrace_gasFlags (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true)
    (hf : ∀xs∈lists,∀x∈xs,x.refund=nativeRefund ctx x.receipt) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (hc : ctx.gasPrice<256^16)
    (hcap : (plannedRows lists).length≤2^log) :
    ∀e∈gasFlagConstraints,e.eval (booleanReceiptTrace own ctx lists log (gasEffectiveConstants ctx constants)
      pub digests (gasFlagAux ctx (gasBorrowAux ctx fallback)) headerFallback) 0 pos pub=0 := by
  intro e he
  have hh : e∈gasFlagCurrent ∨ e=gasFlagTransition := by
    simp only [gasFlagConstraints,cGas] at he
    change e∈[_,_,_,_] at he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    simp only [gasFlagCurrent,gasFlagTransition,gp,List.mem_cons,List.not_mem_nil,or_false] at he ⊢
    grind only
  rcases hh with hh|rfl
  · exact booleanReceiptTrace_gasFlagCurrent own ctx lists hw hf log pos constants pub digests fallback headerFallback hc e hh
  · exact booleanReceiptTrace_gasFlagTransition own ctx lists log pos (gasEffectiveConstants ctx constants)
      pub digests fallback headerFallback hcap

end ZkFormal.NearV3.Assembly.RcptSkeleton
