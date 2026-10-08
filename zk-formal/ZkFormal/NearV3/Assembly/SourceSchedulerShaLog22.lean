import ZkFormal.NearV3.Assembly.SourceUpsertShaLog22
import ZkFormal.NearV3.Assembly.SchedulerSanityJobs

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 ZkFormal.Sha.Gen
open Rcpt.Candidates Rcpt.Candidates.DedupCompile

/-- Uses the existing active log22 SHA cap: three whole-message source bins and
one combined upsert/sanity bin. This establishes placement, not physical routing or ownership. -/
theorem checkD0a_source_scheduler_log22 {cb wb raw : Bytes} {codes : List Bytes}
    {k : WalkD0} {w : StateWitness} {hint : Hint} {p : Prep}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w)
    (hc : checkD0a B0 cb wb=.ok ()) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hr : decodeStateWitness raw=.ok w) :
    ∃ us : List SchedulerUpsertWitness,
      1≤us.length ∧ us.length≤32 ∧ (∀u∈us,u.Valid∧u.pre.wf=true) ∧
      let bins := sourceShaBins (sourceWeights p.lists w.entries) ++
        [upsertShaWeights (schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us)]
      bins.length=4 ∧
      bins.flatten=sourceWeights p.lists w.entries ++ upsertShaWeights (schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us) ∧
      (∀ bin∈bins,bin.sum≤2^22) := by
  have hrel := (relD0a_iff B0 cb wb).mpr hc
  obtain ⟨_,_,hs⟩ := relD0a_inputs hrel hp hf hr
  obtain ⟨he,hm⟩ := sourceWeights_exact hr p.lists hs
  have hb := (relD0a_work_bounds hrel hp hf hr).2.1
  obtain ⟨us,hpos,hlen,hvalid,hrows⟩ := checkD0a_scheduler_sha_rows hk hw hc
  refine ⟨us,hpos,hlen,hvalid,by simp [sourceShaBins],?_,?_⟩
  · simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,
      sourceShaBins_reconstruct]
  · intro bin hbin
    rcases List.mem_append.mp hbin with hbin|hbin
    · exact sourceShaBins_fit _ hm (by omega) bin hbin
    · simp only [List.mem_singleton] at hbin
      subst bin
      rw [upsertShaWeights_sum]
      omega

end ZkFormal.NearV3.Assembly
