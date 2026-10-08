import ZkFormal.NearV3.Rcpt.Candidates.ShaAllocationTraffic
import ZkFormal.NearV3.Rcpt.Candidates.AccountEmptyTraffic
import ZkFormal.NearV3.Assembly.RcptCandidateRepairedTraffic
namespace ZkFormal.NearV3.Candidates.ReceiptPhysicalShaBytes
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Rcpt.Candidates

/-- The public refund body remains a distinct byte consumer, rather than being
silently added as a SHA preimage or dropped from receipt sends. -/
theorem logical (pub : List Fp) (ls : RcptV3Vs) (as : List AcctV) (msg : List Fp) :
    cnt (Sha.Gen.expectedBytes (jobsToSha (receiptShaJobs pub ls as))) msg+
      cnt (refundFragments (flatR ls)) msg=
    cnt (rcptSends3 pub ls B_BYTES) msg+cnt (acctV3Sends as B_BYTES) msg+
      cnt (jobBytes (merkleShaJobs ((flatR ls).map (fun x=>x.leaf)))) msg := by
  have h:=(receipt_core_bytes pub ls).map Msg.toFp
  have hc:=h.count_eq msg
  rw [jobsToSha_bytes]
  have he : jobBytes (receiptShaJobs pub ls as)=
      jobBytes (receiptCoreJobs pub ls)++acctV3Sends as B_BYTES++
      jobBytes (merkleShaJobs ((flatR ls).map (fun x=>x.leaf))) := by
    rw [←accountJobs_bytes]
    simp only [receiptShaJobs,receiptCoreJobs,jobBytes,List.flatMap_append,List.append_assoc]
  rw [he]
  simp only [cnt,List.map_append,List.count_append] at hc ⊢
  omega

/-- Actual repaired receipt and account byte producers discharge the matching
SHA jobs, while the public refund body and Merkle producer remain explicit. -/
theorem physical {pub : List Fp} {ls : RcptV3Vs} {as : List AcctV}
    {trR trA : Trace Fp} {tR tA : Nat}
    (hR : TableTraffic Assembly.ReceiptCandidateRouting.candidateTable.interactions trR tR pub
      (rcptTraffic3 pub ls))
    (hA : ∀msg,tableBusCount AccountEmpty.table.interactions trA tA pub B_BYTES true msg=
      cnt (acctV3Sends as B_BYTES) msg) (msg : List Fp) :
    cnt (Sha.Gen.expectedBytes (jobsToSha (receiptShaJobs pub ls as))) msg+
      cnt (refundFragments (flatR ls)) msg=
    tableBusCount Assembly.ReceiptCandidateRouting.candidateTable.interactions trR tR pub B_BYTES true msg+
      tableBusCount AccountEmpty.table.interactions trA tA pub B_BYTES true msg+
      cnt (jobBytes (merkleShaJobs ((flatR ls).map (fun x=>x.leaf)))) msg := by
  rw [(hR B_BYTES msg).1,hA]
  exact logical pub ls as msg
end ZkFormal.NearV3.Candidates.ReceiptPhysicalShaBytes
