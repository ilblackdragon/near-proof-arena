import ZkFormal.NearV3.Assembly.RcptCandidateRoutingNative

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 Sched RoutingBoundedLayout

theorem booleanReceiptTrace_native_repaired_tableLocal {cb bs : Bytes} {hint : Hint} {p : Prep} {k : WalkD0} {w : StateWitness}
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
      TableLocal ReceiptCandidateRouting.candidateTable
        (RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists 22
          (completeReceiptConstants ctx k accountId
            (depositConstants (depositPlanAccount steps) (depositAgeConstants (depositPlanPrevious lists) constants)))
          pub digests
          (completeReceiptAux ctx k lists accountId accessId
            (depositFinalAux (depositPlanPrevious lists) (depositPlanAccount steps) fallback))
          (completeReceiptHeaders (depositHeaderAux headerFallback))) 0) 0 pub := by
  obtain ⟨mid,so,steps,hmid,hl,ho,hv,hlocal⟩ := booleanReceiptTrace_native_candidate_tableLocal
    hp hk hd own ctx lists hsource hls hw hne hn hflags hrun hgas
    accountId accessId constants pub digests fallback headerFallback hgp hprice hpub hown
  refine ⟨mid,so,steps,hmid,hl,ho,hv,?_⟩
  apply ReceiptCandidateRouting.patch_local_of_q_bound hlocal
  intro pos _ hs
  exact booleanReceiptTrace_native_q_bound hp hk hd own ctx lists hls accountId _ pub digests _ _ 22 pos hs

set_option maxRecDepth 4096 in
theorem repaired_candidate_shape :
    ReceiptCandidateRouting.candidateTable.width=RcptV3.table.width ∧
    ReceiptCandidateRouting.candidateTable.maxLog=22 ∧
    ReceiptCandidateRouting.candidateTable.constraints.length=882 ∧
    ReceiptCandidateRouting.candidateTable.interactions=RcptV3.interactions := by decide

theorem repaired_candidate_busCount (tr : Trace Fp) (pub : List Fp)
    (bus : Nat) (sd : Bool) (msg : List Fp) :
    tableBusCount ReceiptCandidateRouting.candidateTable.interactions
      (RoutingQCandidate.patchTrace tr 0) 0 pub bus sd msg=
    tableBusCount receiptArithmeticCandidate.interactions tr 0 pub bus sd msg :=
  RoutingQCandidate.patch_busCount tr 0 pub bus sd msg

end ZkFormal.NearV3.Assembly.RcptSkeleton
