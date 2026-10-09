import ZkFormal.NearV3.Rcpt.Candidates.NativeShaTraffic
import ZkFormal.NearV3.Rcpt.Candidates.DedupTrafficTrace
import ZkFormal.NearV3.Rcpt.Link.SourcePayload

namespace ZkFormal.NearV3.Rcpt.Candidates
open ZkFormal.Near

/-- Exact nonduplicate source preimages; duplicate occurrences supply no hash job. -/
def sourceViewJobs (bs : List SrcpB) : List Render.Msg :=
  (bs.filter (fun B => !B.dup)).flatMap (fun B =>
    (sourcePayloads B).map (fun p => ⟨msgId K_SRC p.1,p.2⟩))

theorem source_block_job_bytes (B : SrcpB) (repeated : Bool) :
    DedupRender.blockMsgs B repeated B_BYTES true=
      if B.dup then [] else jobBytes ((sourcePayloads B).map (fun p => ⟨msgId K_SRC p.1,p.2⟩)) := by
  cases h : B.dup <;> simp [DedupRender.blockMsgs,DedupRender.rootMsgs,h,jobBytes,
    sourcePayloads,srcpLeafMsgs,srcpItemMsgs,B_BYTES,B_DIGEST,B_RCL,B_SRC,List.flatMap_map]

theorem source_jobs_bytes (bs : List SrcpB) (repeated : Nat→Bool) :
    DedupRender.sourceMsgs bs repeated B_BYTES true=jobBytes (sourceViewJobs bs) := by
  simp only [DedupRender.sourceMsgs,source_block_job_bytes]
  rw [←flatMap_eq_range bs (fun B => if B.dup then [] else
    jobBytes ((sourcePayloads B).map (fun p => ⟨msgId K_SRC p.1,p.2⟩)))]
  induction bs with
  | nil => simp [sourceViewJobs,jobBytes]
  | cons B bs ih =>
    cases h : B.dup <;>
      simp_all [sourceViewJobs,jobBytes,List.flatMap_assoc]

end ZkFormal.NearV3.Rcpt.Candidates
