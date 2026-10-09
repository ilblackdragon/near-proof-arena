import ZkFormal.NearV3.Assembly.RcptCanonicalShaBytes
import ZkFormal.NearV3.Assembly.RcptCanonicalRcJobs
import ZkFormal.NearV3.Assembly.RcptMerkleShaBytes

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof Rcpt.Candidates

private theorem zip_mem {α : Type} (xs : List α) (p : α×Nat) (hp : p∈xs.zipIdx) : p.1∈xs := by
  have hh : p.1∈xs.zipIdx.map Prod.fst := List.mem_map.mpr ⟨p,hp,rfl⟩
  simpa only [List.zipIdx_map_fst] using hh

theorem receipt_jobs_bytes (pub : List Fp) (ls : RcptV3Vs) (as : List AcctV)
    (hc : ∀bytes∈rcShaPayloads pub ls,∀b∈bytes,b<256)
    (hr : ∀x∈flatR ls,∀bytes∈receiptShaPayloads pub x,∀b∈bytes,b<256)
    (ha : ∀m∈accountShaJobs as,∀b∈m.bytes,b<256) :
    ∀m∈receiptShaJobs pub ls as,∀b∈m.bytes,b<256 := by
  intro m hm b hb
  simp only [receiptShaJobs,List.mem_append] at hm
  rcases hm with ((hc'|hr')|ha')|hm'
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hc'
    exact hc p.1 (zip_mem _ p hp) b hb
  · obtain ⟨p,hp,hm⟩ := List.mem_flatMap.mp hr'
    apply hr p.1 (zip_mem _ p hp) m.bytes ?_ b hb
    rw [←receiptJobsAt_payloads pub p.2 p.1]
    exact List.mem_map.mpr ⟨m,hm,rfl⟩
  · exact ha m ha' b hb
  · exact merkle_sha_job_bytes _ m hm' b hb

theorem canonical_native_sha_job_bytes (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat) (log : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true)
    (hflag : ∀xs∈lists,∀x∈xs,x.refund=nativeRefund ctx x.receipt)
    (hheight : HeightPublicBytes ctx pub) (hh : 2^log<Algebra.P)
    (hL : TableLocal ReceiptCandidateRouting.candidateTable (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub (nativeDigests ctx digests)
        (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback) 0) 0 pub)
    (bs : List ListBlock) (e : Nat)
    (hc : ListChain (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub (nativeDigests ctx digests)
        (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback) 0) 0 0 bs e)
    (hown : ∀i,i<8→pub.getD (PH_OWN+i) 0=Fp.ofNat (((u64 own).getD i 0).toNat))
    (as : List AcctV) (ha : ∀m∈accountShaJobs as,∀b∈m.bytes,b<256) :
    let tr:=RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub (nativeDigests ctx digests)
        (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback) 0
    let ls:=bs.map (ListBlock.view tr 0)
    ∀m∈receiptShaJobs pub ls as,∀b∈m.bytes,b<256 := by
  apply receipt_jobs_bytes pub _ as
  · exact canonical_rc_sha_bytes own ctx lists log constants pub (nativeDigests ctx digests)
      (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback hw hh hown hL bs e hc
  · exact canonical_native_sha_bytes own ctx k lists accountId accessId log constants pub digests
      fallback headerFallback hw hflag hheight hh hL bs e hc
  · exact ha

end ZkFormal.NearV3.Assembly.RcptSkeleton
