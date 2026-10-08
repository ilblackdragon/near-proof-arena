import ZkFormal.NearV3.Assembly.RcptGasEffectiveLocal

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem gasEffective_zero (tr : Trace Fp) (pos : Nat) (pub : List Fp)
    (hs : tr.cell 0 pos sGP=0) (hr : rowE.eval tr 0 pos pub=0) :
    ∀e∈gasEffectiveConstraints,e.eval tr 0 pos pub=0 := by
  intro e he
  simp only [gasEffectiveConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl
  all_goals simp only [gp,eval_mul,eval_c,hs,hr]
  all_goals grind only

theorem booleanReceiptTrace_gasEffective (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (hpub : GasPublicBytes ctx pub)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) :
    ∀e∈gasEffectiveConstraints,e.eval (booleanReceiptTrace own ctx lists log
      (nativePriceConstants ctx (systemConstants (gasEffectiveConstants ctx constants)))
      pub digests (gasEffectiveAux ctx fallback) headerFallback) 0 pos pub=0 := by
  intro e he
  unfold booleanReceiptTrace emittedReceiptTrace
  rw [emissionPatch_eval _ _ _ _ _ _ (List.all_eq_true.mp gasEffectiveConstraints_footprint.2 e he)]
  apply plannedTrace_current_bounded_family lists hw log pos _ _ _ pub gasEffectiveConstraints gasEffectiveConstraints_footprint.1
    (fun p row _ _ _ hi=>receipt_gasEffective_local ctx constants pub hpub digests (receiptPlanToken ctx lists) fallback p row hi) ?_ ?_ e he
  · intro p i
    apply gasEffective_zero _ _ _ (by rfl)
    simp only [rowE,eval_sub,eval_c]
    change (1:Fp)-1=0
    grind only
  · apply gasEffective_zero _ _ _ (by rfl)
    simp only [rowE,eval_sub,eval_c,zeroCurrentTrace]
    grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
