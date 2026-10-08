import ZkFormal.NearV3.Candidates.ReceiptDigestPartition
import ZkFormal.NearV3.Candidates.MerkleRender.RootPin
namespace ZkFormal.NearV3.Candidates.ReceiptMerkleDigestBalance
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Rcpt.Candidates

theorem leaf_jobs (ls : RcptV3Vs) : ReceiptDigestPartition.leafDigests ls=
    (MerkleRender.leafShaJobs ((flatR ls).map (fun x=>x.leaf))).map Render.digestMsg := by
  simp only [ReceiptDigestPartition.leafDigests,MerkleRender.leafShaJobs,List.zipIdx_map,List.map_map]
  rw [List.map_eq_flatMap]
  rfl

/-- Per-receipt and internal-Merkle SHA outputs are consumed by the actual
receipt and native Merkle tables. RC and account SHA families are separate. -/
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
    (msg : List Fp) :
    cnt (Sha.Gen.expectedDigests (jobsToSha
      (ReceiptDigestPartition.jobs pub ls++merkleShaJobs (MerkleRender.outcomePreimages os)))) msg=
      tableBusCount Assembly.ReceiptCandidateRouting.candidateTable.interactions tr t pub B_DIGEST false msg+
      tableBusCount MerkleEmpty.table.interactions (MerkleRender.outcomeTrace os pub) T_MRK pub B_DIGEST false msg := by
  have hc:=ReceiptDigestPartition.physical pub ls hl hp hr tr t ht msg
  have hm:=MerkleRender.outcome_digest_pinned os pub hn hout msg
  rw [ReceiptDigestPartition.leafDigests] at hc
  have he:=leaf_jobs ls
  rw [hleaf] at he
  rw [ReceiptDigestPartition.leafDigests] at he
  rw [he] at hc
  rw [ReceiptDigestPartition.jobs_digests] at hc ⊢
  simp only [cnt,List.map_append,List.count_append] at hc hm ⊢
  omega

end ZkFormal.NearV3.Candidates.ReceiptMerkleDigestBalance
