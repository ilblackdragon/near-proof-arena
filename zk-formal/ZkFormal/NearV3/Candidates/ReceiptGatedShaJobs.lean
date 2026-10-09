import ZkFormal.NearV3.Candidates.ReceiptFullDigestResidual

namespace ZkFormal.NearV3.Candidates.ReceiptGatedShaJobs
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Rcpt.Candidates

/-- Hash every source occurrence; duplicate flags suppress only DIGEST output. -/
def rcJobs (pub : List Fp) (ls : RcptV3Vs) (duplicate : Nat→Bool) : List Sha.Gen.Msg :=
  (rcShaPayloads pub ls).zipIdx.map (fun p=>⟨msgId K_RC p.2,p.1,!(duplicate p.2)⟩)

def jobs (pub : List Fp) (ls : RcptV3Vs) (as : List AcctV) (duplicate : Nat→Bool) : List Sha.Gen.Msg :=
  rcJobs pub ls duplicate++jobsToSha (ReceiptDigestPartition.jobs pub ls++accountShaJobs as++
    merkleShaJobs ((flatR ls).map (fun x=>x.leaf)))

theorem bytes_unchanged (pub : List Fp) (ls : RcptV3Vs) (as : List AcctV) (duplicate : Nat→Bool) :
    Sha.Gen.expectedBytes (jobs pub ls as duplicate)=
      Sha.Gen.expectedBytes (jobsToSha (receiptShaJobs pub ls as)) := by
  simp only [jobs,rcJobs,receiptShaJobs,ReceiptDigestPartition.jobs,jobsToSha,
    Sha.Gen.expectedBytes,List.map_append,List.flatMap_append,List.flatMap_map,List.append_assoc]

theorem rows_unchanged (pub : List Fp) (ls : RcptV3Vs) (as : List AcctV) (duplicate : Nat→Bool) :
    (Sha.Gen.honestRows (jobs pub ls as duplicate)).length=
      (Sha.Gen.honestRows (jobsToSha (receiptShaJobs pub ls as))).length := by
  rw [←Assembly.upsertShaWeights_sum,←Assembly.upsertShaWeights_sum]
  simp only [Assembly.upsertShaWeights,jobs,rcJobs,receiptShaJobs,ReceiptDigestPartition.jobs,
    jobsToSha,List.map_append,List.map_map,Function.comp_def,Render.msgRows_length,List.append_assoc]

theorem capacity (pub : List Fp) (ls : RcptV3Vs) (as : List AcctV) (duplicate : Nat→Bool)
    (hr : (Sha.Gen.honestRows (jobsToSha (receiptShaJobs pub ls as))).length≤1373299) :
    (Sha.Gen.honestRows (jobs pub ls as duplicate)).length≤1373299 := by
  rw [rows_unchanged]
  exact hr

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
    (as : List AcctV) (duplicate : Nat→Bool) (msg : List Fp) :
    cnt (Sha.Gen.expectedDigests (jobs pub ls as duplicate)) msg=
      tableBusCount Assembly.ReceiptCandidateRouting.candidateTable.interactions tr t pub B_DIGEST false msg+
      tableBusCount MerkleEmpty.table.interactions (MerkleRender.outcomeTrace os pub) T_MRK pub B_DIGEST false msg+
      cnt (Sha.Gen.expectedDigests (rcJobs pub ls duplicate++jobsToSha (accountShaJobs as))) msg := by
  have hm:=ReceiptMerkleDigestBalance.physical pub ls os hn hleaf hout hl hp hr tr t ht msg
  simp only [jobs,jobsToSha,List.map_append,Sha.Gen.expectedDigests,List.filter_append,
    List.map_append,cnt,List.count_append] at hm ⊢
  rw [hleaf]
  omega

end ZkFormal.NearV3.Candidates.ReceiptGatedShaJobs
