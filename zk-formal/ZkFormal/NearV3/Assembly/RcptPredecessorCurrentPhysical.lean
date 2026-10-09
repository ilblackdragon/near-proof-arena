import ZkFormal.NearV3.Assembly.RcptPredecessorCurrent

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem predecessorCurrent_zero (tr : Trace Fp) (pos : Nat) (pub : List Fp)
    (hs : tr.cell 0 pos sP=0) (hr : rowE.eval tr 0 pos pub=0) :
    ∀e∈predecessorCurrentConstraints,e.eval tr 0 pos pub=0 := by
  intro e he
  simp only [predecessorCurrentConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl <;>
    simp only [eval_mul3,eval_mul,eval_c,hs,hr] <;> grind only

theorem booleanReceiptTrace_predecessorCurrent (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp) :
    ∀e∈predecessorCurrentConstraints,e.eval
      (booleanReceiptTrace own ctx lists log (nativePriceConstants ctx (systemConstants constants))
        pub digests (predecessorAux fallback) headerFallback) 0 pos pub=0 := by
  intro e he
  unfold booleanReceiptTrace emittedReceiptTrace
  rw [emissionPatch_eval _ _ _ _ _ _ (List.all_eq_true.mp predecessorCurrent_footprint.2 e he)]
  apply plannedTrace_current_family lists hw log pos _ _ _ pub predecessorCurrentConstraints
    predecessorCurrent_footprint.1
    (fun p row hw hlen=>receipt_predecessor_current ctx lists constants pub digests fallback p row hw hlen)
    ?_ ?_ e he
  · intro p i
    apply predecessorCurrent_zero _ _ _ (by rfl)
    simp only [rowE,eval_sub,eval_c]
    change (1:Fp)-1=0
    grind only
  · apply predecessorCurrent_zero _ _ _ (by rfl)
    simp only [rowE,eval_sub,eval_c,zeroCurrentTrace]
    grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
