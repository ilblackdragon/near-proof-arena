import ZkFormal.NearV3.Rcpt.Candidates.NativeReceiptMemView
namespace ZkFormal.NearV3.Assembly.RcptSkeleton
set_option maxRecDepth 4096
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

theorem receipt_first_position (p : ReceiptPlan) :
    (plannedReceiptRows p)[0]?=some (.receipt p ⟨sPL,0,4⟩) := by
  cases p.input.refund <;> rfl

/-- Shared receipt constants supply original account VID and prior timestamp;
canonical bounds are explicit, avoiding field-cast aliasing. -/
theorem native_receipt_mem_metadata (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (pre post : List PlannedRow)
    (hb:plannedRows lists=pre++plannedReceiptRows p++post)
    (hid:accountId p<Algebra.P) (ht:previous p<Algebra.P) :
    let tr:=RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists log
      (completeReceiptConstants ctx k accountId (depositConstants accounts (depositAgeConstants previous constants))) pub digests
      (completeReceiptAux ctx k lists accountId accessId (depositFinalAux previous accounts fallback)) headerFallback) 0
    let x:=rcptOf tr 0 (inputShape pre.length p.input)
    x.kslot=accountId p ∧ x.tprev=previous p := by
  have ha:=receipt_block_lookup lists p pre post hb 0 _ (receipt_first_position p)
  simp only [Nat.add_zero] at ha
  have hc:=booleanReceiptTrace_planned_cell own ctx lists log pre.length
    (completeReceiptConstants ctx k accountId (depositConstants accounts (depositAgeConstants previous constants))) pub digests
    (completeReceiptAux ctx k lists accountId accessId (depositFinalAux previous accounts fallback)) headerFallback _ ha
  dsimp only [rcptOf,inputShape]
  unfold cv
  rw [RoutingQCandidate.patch_other _ _ _ kslot (by decide),RoutingQCandidate.patch_other _ _ _ tprev (by decide),
    hc kslot (by decide),hc tprev (by decide)]
  change (Fp.ofNat (accountId p)).toNat=accountId p ∧ (Fp.ofNat (previous p)).toNat=previous p
  exact ⟨by rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt hid],by rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt ht]⟩

end ZkFormal.NearV3.Assembly.RcptSkeleton
