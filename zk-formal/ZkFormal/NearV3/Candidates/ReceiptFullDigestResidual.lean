import ZkFormal.NearV3.Candidates.ReceiptMerkleDigestBalance
namespace ZkFormal.NearV3.Candidates.ReceiptFullDigestResidual
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Rcpt.Candidates

/-- Preserve one indexed RC job per source occurrence. Deduplication flags must
be reconciled with the source digest consumers separately. -/
def rcJobs (pub : List Fp) (ls : RcptV3Vs) : List Render.Msg :=
  (rcShaPayloads pub ls).zipIdx.map (fun p=>⟨msgId K_RC p.2,p.1⟩)

/-- Exact remaining DIGEST obligations of the full receipt SHA batch after
physical receipt and Merkle consumers; RC/account obligations are not dropped. -/
theorem physical (pub : List Fp) (ls : RcptV3Vs) (os : List NearSpec.Outcome)
    (hn : os.length≤4481)
    (hleaf : (flatR ls).map (fun x=>x.leaf)=MerkleRender.outcomePreimages os)
    (hout : ∀i<32,pub.getD (PH_OUT+i) 0=Fp.ofNat (((NearSpec.outcomeRoot os).getD i 0).toNat))
    (hl : ∀x∈flatR ls,x.rid.length=32)
    (hp : ∀x∈flatR ls,x.peoh=(NearSpec.sha256 (x.peo.map UInt8.ofNat)).map UInt8.toNat)
    (hr : ∀x∈flatR ls,x.hr=true→x.rfid=(NearSpec.sha256
      ((x.rid++pubBytes pub PH_HEIGHT 8++List.replicate 8 0).map UInt8.ofNat)).map UInt8.toNat)
    (tr : Trace Fp) (t : Nat)
    (ht : TableTraffic Assembly.ReceiptCandidateRouting.candidateTable.interactions tr t pub (rcptTraffic3 pub ls))
    (as : List AcctV) (msg : List Fp) :
    cnt (Sha.Gen.expectedDigests (jobsToSha (receiptShaJobs pub ls as))) msg=
      tableBusCount Assembly.ReceiptCandidateRouting.candidateTable.interactions tr t pub B_DIGEST false msg+
      tableBusCount MerkleEmpty.table.interactions (MerkleRender.outcomeTrace os pub) T_MRK pub B_DIGEST false msg+
      cnt (Sha.Gen.expectedDigests (jobsToSha (rcJobs pub ls++accountShaJobs as))) msg := by
  have hm:=ReceiptMerkleDigestBalance.physical pub ls os hn hleaf hout hl hp hr tr t ht msg
  rw [ReceiptDigestPartition.jobs_digests] at hm
  rw [ReceiptDigestPartition.jobs_digests,ReceiptDigestPartition.jobs_digests]
  simp only [receiptShaJobs,rcJobs,ReceiptDigestPartition.jobs,List.map_append,cnt,List.count_append] at hm ⊢
  rw [hleaf]
  omega

end ZkFormal.NearV3.Candidates.ReceiptFullDigestResidual
