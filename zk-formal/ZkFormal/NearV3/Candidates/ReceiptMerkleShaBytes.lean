import ZkFormal.NearV3.Candidates.ReceiptPhysicalShaBytes
import ZkFormal.NearV3.Candidates.MerkleRender.Bytes
namespace ZkFormal.NearV3.Candidates.ReceiptMerkleShaBytes
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Rcpt.Candidates

/-- Actual native outcome-Merkle cells discharge the remaining receipt-batch
Merkle byte producer, including the empty-outcome case. Receipt leaves must be
bound to these same outcomes; public refund-body traffic is retained. -/
theorem physical {pub : List Fp} {ls : RcptV3Vs} {as : List AcctV}
    {trR trA : Trace Fp} {tR tA : Nat} (os : List NearSpec.Outcome)
    (hn : os.length≤4481)
    (hleaves : (flatR ls).map (fun x=>x.leaf)=MerkleRender.outcomePreimages os)
    (hR : TableTraffic Assembly.ReceiptCandidateRouting.candidateTable.interactions trR tR pub
      (rcptTraffic3 pub ls))
    (hA : ∀msg,tableBusCount AccountEmpty.table.interactions trA tA pub B_BYTES true msg=
      cnt (acctV3Sends as B_BYTES) msg) (msg : List Fp) :
    cnt (Sha.Gen.expectedBytes (jobsToSha (receiptShaJobs pub ls as))) msg+
      cnt (refundFragments (flatR ls)) msg=
    tableBusCount Assembly.ReceiptCandidateRouting.candidateTable.interactions trR tR pub B_BYTES true msg+
      tableBusCount AccountEmpty.table.interactions trA tA pub B_BYTES true msg+
      tableBusCount MerkleEmpty.table.interactions (MerkleRender.outcomeTrace os pub)
        T_MRK pub B_BYTES true msg := by
  have hm:=MerkleRender.outcome_bytes os pub hn msg
  rw [←hleaves] at hm
  rw [hm]
  exact ReceiptPhysicalShaBytes.physical hR hA msg
end ZkFormal.NearV3.Candidates.ReceiptMerkleShaBytes
