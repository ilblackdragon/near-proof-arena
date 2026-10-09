import ZkFormal.NearV3.Assembly.RcptGasBorrowCommute

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem booleanReceiptTrace_gasBorrow (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (hpub : GasPublicBytes ctx pub)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (hc : ctx.gasPrice<256^16)
    (hcap : (plannedRows lists).length≤2^log) :
    ∀e∈gasBorrowConstraints,e.eval (booleanReceiptTrace own ctx lists log (nativePriceConstants ctx constants)
      pub digests (gasBorrowAux ctx fallback) headerFallback) 0 pos pub=0 := by
  intro e he
  have hh : e∈gasBorrowCurrent ∨ e=gasBorrowTransition := by
    simp only [gasBorrowConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
    simp only [gasBorrowCurrent,gasBorrowTransition,gp,List.mem_cons,List.not_mem_nil,or_false] at he ⊢
    grind only
  rcases hh with hh|rfl
  · exact booleanReceiptTrace_gasBorrowCurrent own ctx lists hw log pos constants pub hpub digests fallback headerFallback hc e hh
  · exact booleanReceiptTrace_gasBorrowTransition own ctx lists log pos (nativePriceConstants ctx constants) pub digests fallback headerFallback hcap

end ZkFormal.NearV3.Assembly.RcptSkeleton
