import ZkFormal.NearV3.Candidates.ReceiptGatedShaJobs

namespace ZkFormal.NearV3.Candidates.ReceiptGatedShaBytes
open ZkFormal.Algebra ZkFormal.Near Rcpt.Candidates

theorem payloads (pub : List Fp) (ls : RcptV3Vs) (as : List AcctV) (duplicate : Nat→Bool) :
    (ReceiptGatedShaJobs.jobs pub ls as duplicate).map (·.bytes)=
      (receiptShaJobs pub ls as).map Render.Msg.bytes := by
  simp only [ReceiptGatedShaJobs.jobs,ReceiptGatedShaJobs.rcJobs,receiptShaJobs,
    ReceiptDigestPartition.jobs,jobsToSha,List.map_append,List.map_map,Function.comp_def,List.append_assoc]

theorem bytes (pub : List Fp) (ls : RcptV3Vs) (as : List AcctV) (duplicate : Nat→Bool)
    (h : ∀m∈receiptShaJobs pub ls as,∀b∈m.bytes,b<256) :
    ∀m∈ReceiptGatedShaJobs.jobs pub ls as duplicate,∀b∈m.bytes,b<256 := by
  intro m hm b hb
  have hh : m.bytes∈(ReceiptGatedShaJobs.jobs pub ls as duplicate).map (·.bytes) :=
    List.mem_map.mpr ⟨m,hm,rfl⟩
  rw [payloads] at hh
  obtain ⟨n,hn,he⟩:=List.mem_map.mp hh
  exact h n hn b (he.symm ▸ hb)

end ZkFormal.NearV3.Candidates.ReceiptGatedShaBytes
