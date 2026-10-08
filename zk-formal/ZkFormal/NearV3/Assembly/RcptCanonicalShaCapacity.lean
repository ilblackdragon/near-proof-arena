import ZkFormal.NearV3.Assembly.RcptCanonicalShaLengths
import ZkFormal.NearV3.Assembly.RcptShaLengthCapacity
import ZkFormal.NearV3.Assembly.RcptCanonicalCounts

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof Rcpt.Candidates

/-- The actual honest physical receipt view fits the allocated SHA-family budget.
Native execution/preparation supply both counts; serialization supplies byte costs.
No independent extracted receipt-Wf or receipt SHA-row bound is assumed. -/
theorem canonical_native_sha_capacity (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat) (log : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true)
    (hflag : ∀xs∈lists,∀x∈xs,x.refund=nativeRefund ctx x.receipt)
    (hh : 2^log<Algebra.P)
    (hL : TableLocal ReceiptCandidateRouting.candidateTable (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub (nativeDigests ctx digests)
        (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback) 0) 0 pub)
    (bs : List ListBlock) (e : Nat)
    (hc : ListChain (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub (nativeDigests ctx digests)
        (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback) 0) 0 0 bs e)
    {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (hsource : lists.length=p.lists.length)
    {t : PTrie} {out : MainOut}
    (hrun : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (hgas : ctx.gasLimit≤maxGasLimitD0)
    (as : List AcctV) (ha : as=[] ∨ AcctWf as) (hac : as.length≤8192) :
    let tr:=RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub (nativeDigests ctx digests)
        (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback) 0
    let ls:=bs.map (ListBlock.view tr 0)
    ((receiptShaJobs pub ls as).map (fun m=>Render.rowsOf m.bytes.length)).sum≤1373299 := by
  have hl := canonical_native_sha_lengths own ctx k lists accountId accessId log constants pub digests
    fallback headerFallback hw hflag hh hL bs e hc
  have hn := canonical_native_count_bounds own ctx lists log constants pub (nativeDigests ctx digests)
    (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback hw hp hsource
    hrun hgas hh hL bs e hc
  exact receipt_jobs_capacity_lengths pub _ as hl ha hac hn.2 hn.1

end ZkFormal.NearV3.Assembly.RcptSkeleton
