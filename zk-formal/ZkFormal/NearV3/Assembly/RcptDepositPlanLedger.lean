import ZkFormal.NearV3.Assembly.RcptDepositPhysical

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3

/-- Account selected by the actual globally ordered native ledger. The fallback
is unreachable at an actual planned receipt, as proved below. -/
def depositPlanAccount (steps : List NativeDepositStep) (p : ReceiptPlan) : Account :=
  match steps[p.receiptIndex]? with
  | some s=>s.account
  | none=>⟨0,0,[],0⟩

/-- Last earlier receiver occurrence, using version0 for the initial account.
This supplies a bounded version number; global provider ownership is separate. -/
def latestReceiverVersion (receiver : Bytes) : Nat→List Receipt→Nat
  | _,[]=>0
  | start,r::rs=>
      let later := latestReceiverVersion receiver (start+1) rs
      if later=0 then (if r.receiverId==receiver then start+1 else 0) else later

def depositPlanPrevious (lists : List (List Input)) (p : ReceiptPlan) : Nat :=
  latestReceiverVersion p.input.receipt.receiverId 0 ((lists.flatten.map Input.receipt).take p.receiptIndex)

theorem latestReceiverVersion_bound (receiver : Bytes) (start : Nat) (rs : List Receipt) :
    latestReceiverVersion receiver start rs≤start+rs.length := by
  induction rs generalizing start with
  | nil =>simp [latestReceiverVersion]
  | cons r rs ih =>
    have hh := ih (start+1)
    simp only [latestReceiverVersion,List.length_cons]
    split
    · split <;> omega
    · omega

theorem depositPlanPrevious_bound (lists : List (List Input)) (p : ReceiptPlan) :
    depositPlanPrevious lists p≤p.receiptIndex := by
  have hh := latestReceiverVersion_bound p.input.receipt.receiverId 0 ((lists.flatten.map Input.receipt).take p.receiptIndex)
  simp only [Nat.zero_add,List.length_take] at hh
  exact Nat.le_trans hh (Nat.min_le_left _ _)

theorem planned_receipt_native_index (lists : List (List Input)) (p : ReceiptPlan) (row : Coord)
    (hm : PlannedRow.receipt p row∈plannedRows lists) :
    (lists.flatten.map Input.receipt)[p.receiptIndex]?=some p.input.receipt := by
  rw [←plannedSegments_rows] at hm
  obtain ⟨seg,hseg,hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨r,_,he⟩ := List.mem_map.mp hm
  cases seg with
  | header =>cases he
  | receipt p' s =>cases he;exact plannedSegment_receipt_input lists p s hseg

theorem depositPlanAccount_native (ctx : ApplyCtx) (lists : List (List Input))
    (steps : List NativeDepositStep) (ho : steps.map NativeDepositStep.receipt=lists.flatten.map Input.receipt)
    (hv : ∀s∈steps,s.Valid ctx) (p : ReceiptPlan) (row : Coord)
    (hm : PlannedRow.receipt p row∈plannedRows lists) :
    DepositArithmeticOk (nativeDepositData (depositPlanAccount steps p) p.input.receipt) := by
  have hi := planned_receipt_native_index lists p row hm
  rw [←ho,List.getElem?_map] at hi
  cases hs : steps[p.receiptIndex]? with
  | none =>simp only [hs,Option.map_none] at hi;cases hi
  | some s =>
    simp only [hs,Option.map_some,Option.some.injEq] at hi
    simp only [depositPlanAccount,hs]
    rw [←hi]
    exact NativeDepositStep.arithmetic (hv s (List.mem_of_getElem? hs))

theorem planned_receipt_native_bound (ctx : ApplyCtx) (lists : List (List Input))
    {t : PTrie} {out : MainOut}
    (hrun : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (hgas : ctx.gasLimit≤maxGasLimitD0) (p : ReceiptPlan) (row : Coord)
    (hm : PlannedRow.receipt p row∈plannedRows lists) : p.receiptIndex<4481 := by
  have hi := (List.getElem?_eq_some_iff.mp (planned_receipt_native_index lists p row hm)).1
  have hb := applyNewChunk_receipt_bound hrun hgas
  omega

end ZkFormal.NearV3.Assembly.RcptSkeleton
