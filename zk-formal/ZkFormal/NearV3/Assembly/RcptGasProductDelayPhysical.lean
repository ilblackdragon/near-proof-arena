import ZkFormal.NearV3.Assembly.RcptGasProductNativeBounds
import ZkFormal.NearV3.Assembly.RcptCandidateGasDelayPhysical

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3

/-- Both corrected multiplication and delay families use the same physical trace.
All numeric product bounds come from native execution, including system branches. -/
theorem booleanReceiptTrace_acceptedGasProductDelay (own : Nat) (ctx : ApplyCtx)
    (lists : List (List Input)) (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true)
    {t : PTrie} {out : MainOut}
    (hrun : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (hp : ctx.gasPrice<256^16)
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (hcap : (plannedRows lists).length≤2^log) :
    ∀e∈gasProductConstraints systemSurplus++candidateGasDelayConstraints,e.eval
      (booleanReceiptTrace own ctx lists log (gasEffectiveConstants ctx constants)
        pub digests (nativeGasProductAux ctx (receiptPlanToken ctx lists) fallback) headerFallback) 0 pos pub=0 := by
  intro e he
  rcases List.mem_append.mp he with he|he
  · exact booleanReceiptTrace_acceptedGasProduct own ctx lists hw hrun hp log pos constants pub digests fallback headerFallback hcap e he
  · rw [nativeGasProduct_delay_outer]
    apply booleanReceiptTrace_candidateGasDelay own ctx lists ?_ hp log pos constants pub digests
      (gasProductAux ctx (gasTokenAux (receiptPlanToken ctx lists) fallback)) headerFallback hcap e he
    intro xs hxs x hx
    have hh := hw xs hxs x hx
    simp only [Receipt.wf,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.1.2

theorem candidate_product_delay_count :
    (gasProductConstraints systemSurplus++candidateGasDelayConstraints).length=26 := rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
