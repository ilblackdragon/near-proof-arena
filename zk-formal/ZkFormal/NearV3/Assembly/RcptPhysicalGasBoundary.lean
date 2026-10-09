import ZkFormal.NearV3.Assembly.RcptGasTransport

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- GP's final shifted token window is linked to the next physical segment's
native prefix total, not assumed equal to an abstract next-row witness. -/
theorem planned_GP_boundary_gas (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : ReceiptPlan) (q : SegmentPlan)
    (hpq : Neighbors (plannedSegments lists) (.receipt p sGP) q)
    (a b : PlannedRow) (hpa : (SegmentPlan.receipt p sGP).rows.getLast?=some a)
    (hqb : q.rows.head?=some b)
    (ha : (plannedRows lists)[pos]?=some a) (hb : (plannedRows lists)[pos+1]?=some b)
    (hh : pos+1<2^log) :
    ∀e∈gasTokenConstraints,e.eval
      (plannedTrace lists log constants
        (tokenReceiptAux pub digests (receiptPlanToken ctx lists) fallback)
        (headerStreamAux own (headerBurn ctx (lists.flatten.map Input.receipt)) headerFallback)) 0 pos pub=0 := by
  have hae := GP_segment_last p a hpa
  apply gasToken_transport _
    (receiptPair constants (tokenReceiptAux pub digests (receiptPlanToken ctx lists) fallback)
      p ⟨sGP,15,16⟩ (nextGas 15)) 0 pos 0 0 pub
  · intro c
    rw [plannedTrace_cell _ _ _ _ _ _ _ ha c,hae]
    rfl
  · intro j hj
    change (plannedTrace lists log constants _ _).cell 0 ((pos+1)%2^log) (tok j)=_
    rw [Nat.mod_eq_of_lt hh,plannedTrace_cell _ _ _ _ _ _ _ hb (tok j)]
    change nativePlannedCell own ctx lists constants pub digests fallback headerFallback b (tok j)=
      receiptCell constants (tokenReceiptAux pub digests (receiptPlanToken ctx lists) fallback) p (nextGas 15) (tok j)
    rw [GP_boundary_next_tokens own ctx lists constants pub digests fallback headerFallback p q hpq b hqb j hj,
      receipt_token_cell _ _ _ _ _ _ _ _ hj]
    rfl
  · exact receipt_gas_token_constraints constants pub digests (receiptPlanToken ctx lists) fallback p 15 (by decide)

end ZkFormal.NearV3.Assembly.RcptSkeleton
