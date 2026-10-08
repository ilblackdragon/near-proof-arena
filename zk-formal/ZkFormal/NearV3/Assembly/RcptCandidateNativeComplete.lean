import ZkFormal.NearV3.Assembly.RcptDepositGlobalCommute

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 Sched RoutingBoundedLayout

/-- All 881 candidate receipt equations hold on ONE physical log22 trace, with
DEP accounts read from the actual native ledger. Digest/global ownership and
candidate table installation remain separate obligations. -/
theorem booleanReceiptTrace_native_candidate_complete {cb bs : Bytes} {hint : Hint} {p : Prep} {k : WalkD0} {w : StateWitness}
    (hp : prepD0 cb hint=.ok p) (hk : walkD0 cb=.ok k) (hd : decodeStateWitness bs=.ok w) (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hsource : lists.length=p.lists.length)
    (hls : lists.flatten.map Input.receipt=appliedReceipts k w)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hne : lists≠[])
    (hn : ∀xs∈lists,∀x∈xs,AccountId.isNamed x.receipt.receiverId=true)
    (hflags : ∀xs∈lists,∀x∈xs,x.refund=nativeRefund ctx x.receipt)
    {t : PTrie} {out : MainOut}
    (hrun : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (hgas : ctx.gasLimit≤maxGasLimitD0)
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hgp : GasPublicBytes ctx pub) (hprice : ctx.gasPrice<256^16)
    (hpub : FinalPublicBytes lists out pub)
    (hown : ∀j,j<8→pub.getD (PH_OWN+j) 0=Fp.ofNat (((u64 own).getD j 0).toNat)) :
    ∃mid so steps,schedStep prims ctx t=.ok (mid,so) ∧
      nativeDepositLedger ctx ⟨mid,[],[],0,0⟩ (lists.flatten.map Input.receipt)=some steps ∧
      steps.map NativeDepositStep.receipt=lists.flatten.map Input.receipt ∧
      (∀s∈steps,s.Valid ctx) ∧
      ∀pos,pos<2^22→∀e∈cRegs++cEmit++cStates++cEnd++cChars++cSys++cRoute++cKey++systemGasConstraints++depositAgeConstraints,
        e.eval (booleanReceiptTrace own ctx lists 22
          (completeReceiptConstants ctx k accountId
            (depositConstants (depositPlanAccount steps) (depositAgeConstants (depositPlanPrevious lists) constants)))
          pub digests
          (completeReceiptAux ctx k lists accountId accessId
            (depositFinalAux (depositPlanPrevious lists) (depositPlanAccount steps) fallback))
          (completeReceiptHeaders (depositHeaderAux headerFallback))) 0 pos pub=0 := by
  obtain ⟨mid,so,steps,hmid,hl,ho,hv⟩ := applyNewChunk_deposit_ledger prims ctx t _ out hrun
  refine ⟨mid,so,steps,hmid,hl,ho,hv,?_⟩
  intro pos hpos e he
  rcases List.mem_append.mp he with he|he
  · exact booleanReceiptTrace_native_candidateGas_complete hp hk hd own ctx lists hsource hls hw hne hn hflags hrun hgas
      accountId accessId
      (depositConstants (depositPlanAccount steps) (depositAgeConstants (depositPlanPrevious lists) constants))
      pub digests (depositFinalAux (depositPlanPrevious lists) (depositPlanAccount steps) fallback)
      (depositHeaderAux headerFallback) hgp hprice hpub hown pos hpos e he
  · have hh := booleanReceiptTrace_candidateDeposit own ctx lists (depositPlanPrevious lists) (depositPlanAccount steps)
      (depositPlanAccount_native ctx lists steps ho hv)
      (planned_receipt_native_bound ctx lists hrun hgas)
      (fun rp _ _=>depositPlanPrevious_bound lists rp)
      22 pos (completeReceiptConstants ctx k accountId constants) pub digests
      (completeReceiptAux ctx k lists accountId accessId fallback)
      (completeReceiptHeaders headerFallback)
      (Nat.le_of_lt (native_plannedRows_capacity hp lists hsource hw hrun hgas).2) e he
    change e.eval (booleanReceiptTrace own ctx lists 22
      (depositConstants (depositPlanAccount steps) (depositAgeConstants (depositPlanPrevious lists)
        (completeReceiptConstants ctx k accountId constants))) pub digests
      (depositFinalAux (depositPlanPrevious lists) (depositPlanAccount steps)
        (completeReceiptAux ctx k lists accountId accessId fallback))
      (depositHeaderAux (completeReceiptHeaders headerFallback))) 0 pos pub=0 at hh
    simpa only [depositFinal_complete_constants,depositFinal_complete_aux,depositFinal_complete_headers] using hh

set_option maxRecDepth 4096 in
theorem native_candidate_complete_count :
    (cRegs++cEmit++cStates++cEnd++cChars++cSys++cRoute++cKey++systemGasConstraints++depositAgeConstraints).length=881 := by decide

end ZkFormal.NearV3.Assembly.RcptSkeleton
