import ZkFormal.NearV3.Assembly.RcptDepositPlanLedger

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3

/-- Physical DEP completeness with actual native account reads and actual
receipt indices. This does not yet claim global account/version bus ownership. -/
theorem booleanReceiptTrace_acceptedDeposit {cb : Bytes} {hint : Hint} {prep : Prep}
    (hp : prepD0 cb hint=.ok prep) (own : Nat) (ctx : ApplyCtx)
    (lists : List (List Input)) (hsource : lists.length=prep.lists.length)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true)
    {t : PTrie} {out : MainOut}
    (hrun : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (hgas : ctx.gasLimit≤maxGasLimitD0)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp) :
    ∃mid so steps,schedStep prims ctx t=.ok (mid,so) ∧
      nativeDepositLedger ctx ⟨mid,[],[],0,0⟩ (lists.flatten.map Input.receipt)=some steps ∧
      steps.map NativeDepositStep.receipt=lists.flatten.map Input.receipt ∧
      (∀s∈steps,s.Valid ctx) ∧
      ∀pos,∀e∈depositAgeConstraints,e.eval
        (booleanReceiptTrace own ctx lists 22
          (depositConstants (depositPlanAccount steps) (depositAgeConstants (depositPlanPrevious lists) constants))
          pub digests (depositAgeAux (depositPlanPrevious lists) (depositAux (depositPlanAccount steps) fallback))
          (depositHeaderAux headerFallback)) 0 pos pub=0 := by
  obtain ⟨mid,so,steps,hmid,hl,ho,hv⟩ := applyNewChunk_deposit_ledger prims ctx t _ out hrun
  refine ⟨mid,so,steps,hmid,hl,ho,hv,?_⟩
  intro pos
  exact booleanReceiptTrace_candidateDeposit own ctx lists (depositPlanPrevious lists) (depositPlanAccount steps)
    (depositPlanAccount_native ctx lists steps ho hv)
    (planned_receipt_native_bound ctx lists hrun hgas)
    (fun p _ _=>depositPlanPrevious_bound lists p)
    22 pos constants pub digests fallback headerFallback
    (Nat.le_of_lt (native_plannedRows_capacity hp lists hsource hw hrun hgas).2)

end ZkFormal.NearV3.Assembly.RcptSkeleton
