import ZkFormal.NearV3.Candidates.ReceiptSourceInputs
import ZkFormal.NearV3.Assembly.RcptSystemCertificate
import ZkFormal.NearV3.Assembly.RcptDepositGlobalCommute
import ZkFormal.NearV3.Assembly.RoutingQTrace
namespace ZkFormal.NearV3.Candidates.NativeReceiptSignerBalance
open NearSpec NearSpecV3 ZkFormal.Near Assembly RcptSkeleton ZkFormal.Air ZkFormal.Algebra RcptV3

theorem complete {cb : Bytes} {hint : Hint} {p : Prep} (hp:prepD0 cb hint=.ok p)
    (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (hsource:lists.length=p.lists.length) (hw:∀xs∈lists,∀x∈xs,x.receipt.wf=true)
    {t : PTrie} {out : MainOut}
    (hrun:applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (hgas:ctx.gasLimit≤maxGasLimitD0)
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp) :
    let tr:=RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists 22
      (completeReceiptConstants ctx k accountId constants) pub digests
      (completeReceiptAux ctx k lists accountId accessId fallback)
      (completeReceiptHeaders headerFallback)) 0
    ∀msg,tableBusCount RcptV3.interactions tr 0 pub B_SREC true msg=
      tableBusCount RcptV3.interactions tr 0 pub B_SREC false msg := by
  have hh:=booleanReceiptTrace_native_systemBalance hp own ctx lists hsource hw hrun hgas
    (keyConstants accountId (nativeRoutingConstants k (gasEffectiveConstants ctx constants))) pub digests
    (routingAux (nativeRoutingInterval k) (keyAux accountId accessId (gasBorrowAux ctx
      (gasEffectiveAux ctx (candidateGasDelayAux ctx (gasFlagAux ctx
        (gasTokenAux (receiptPlanToken ctx lists) (gasProductAux ctx fallback))))))))
    (routingHeaderAux (keyHeaderAux headerFallback))
  dsimp only
  intro msg
  change tableBusCount RoutingQCandidate.candidateTable.interactions _ 0 pub B_SREC true msg=
    tableBusCount RoutingQCandidate.candidateTable.interactions _ 0 pub B_SREC false msg
  rw [RoutingQCandidate.patch_busCount,RoutingQCandidate.patch_busCount,tableBusCount_eq,tableBusCount_eq]
  exact congrArg (fun xs=>xs.count msg) hh

theorem accepted {cb wb raw : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    {w : StateWitness} {m : MainExecutionV3}
    (hp:prepD0 cb hint=.ok p) (hk:walkD0 cb=.ok k) (hw:decodeW wb=.ok w)
    (hr:decodeStateWitness raw=.ok w) (hc:checkD0a B0 cb wb=.ok ()) (hm:m.NativeValid k w)
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp) :
    let lists:=sourceInputLists (m.ctx k) p.lists w.entries
    let tr:=RoutingQCandidate.patchTrace (booleanReceiptTrace k.H.shardId (m.ctx k) lists 22
      (completeReceiptConstants (m.ctx k) k accountId constants) pub digests
      (completeReceiptAux (m.ctx k) k lists accountId accessId fallback)
      (completeReceiptHeaders headerFallback)) 0
    ∀msg,tableBusCount RcptV3.interactions tr 0 pub B_SREC true msg=
      tableBusCount RcptV3.interactions tr 0 pub B_SREC false msg := by
  have hrel:RelD0a B0 cb wb:=(relD0a_iff B0 cb wb).mpr hc
  obtain ⟨hcount,hreceipts,hwf,_,_,_⟩:=ReceiptSourceInputs.admitted (m.ctx k) hrel hp hk hw hr
  exact complete hp k.H.shardId (m.ctx k) k _ hcount hwf
    (by rw [hreceipts];exact hm.run) (ReceiptSourceInputs.gas hrel hp hk hm).1
    accountId accessId constants pub digests fallback headerFallback

end ZkFormal.NearV3.Candidates.NativeReceiptSignerBalance
