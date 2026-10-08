import ZkFormal.NearV3.Assembly.SchedulerDigestPlan

namespace ZkFormal.NearV3.Assembly
open NearSpec ZkFormal.Near UpsRows Render.UpsGen

private theorem from_ids (tau start : Nat) (xs : List Bytes) :
    (upsertShaFrom tau start xs).map (·.id)=
      (List.range xs.length).map (fun i=>upsertJobId tau (start+i)) := by
  induction xs generalizing start with
  | nil=>rfl
  | cons x xs ih=>
    simp only [upsertShaFrom,List.map_cons,upsertShaJob,ih,List.length_cons,
      List.range_succ_eq_map,List.map_cons,List.map_map,Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro i hi
    congr 1
    omega

/-- All concrete jobs retain their actual transition and output-part indices. -/
theorem upsert_jobs_indexed (tau : Nat) (value : Bytes) (run : TreeRun) :
    (upsertShaJobs tau value run).map (·.id)=
      (List.range (run.parts.length+1)).map (upsertJobId tau) := by
  unfold upsertShaJobs
  rw [from_ids]
  simp only [List.length_cons,List.length_map,Nat.zero_add]

/-- Actual execution's canonical dependency uses match precisely the same
batch's SHA message IDs. Physical branch order and window hashes are separate
remaining linkage obligations; no hash equality is assumed here. -/
theorem traceUpsert_digest_job_ids {root : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root key value=some run) (tau : Nat) :
    ((planDigestUses run.terminal 0 (run.parts.map TreePart.kind)++[run.parts.length]).map
      (upsertJobId tau))=(upsertShaJobs tau value run).map (·.id) := by
  rw [traceUpsert_digest_uses hr,upsert_jobs_indexed]

end ZkFormal.NearV3.Assembly
