import ZkFormal.NearV3.Assembly.SourceShaMessages

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 ZkFormal.Sha.Gen

/-- Four concrete message lists for one proof's source and scheduler hashing.
The three source lists have log22 capacity; the scheduler list has log21 capacity.
Final table installation and cross-table bus ownership are separate obligations. -/
theorem checkD0a_source_scheduler_messages {cb wb raw : Bytes} {codes : List Bytes}
    {k : WalkD0} {w : StateWitness} {hint : Hint} {p : Prep}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w)
    (hc : checkD0a B0 cb wb=.ok ()) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hr : decodeStateWitness raw=.ok w) :
    ∃us : List SchedulerUpsertWitness,
      1≤us.length ∧ us.length≤32 ∧ (∀u∈us,u.Valid∧u.pre.wf=true) ∧
      let bins := sourceShaMessageBins (sourceShaMessages p.lists w.entries) ++
        [schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us]
      bins.length=4 ∧
      bins.flatten=sourceShaMessages p.lists w.entries ++
        (schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us) ∧
      (∀ bin∈bins,(honestRows bin).length≤2^22) ∧
      (honestRows (schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us)).length≤2^21 := by
  obtain ⟨us,hpos,hlen,hvalid,hrows⟩ := checkD0a_scheduler_sha_rows hk hw hc
  obtain ⟨hcount,hrecon,hfit⟩ := checkD0a_source_sha_messages hc hp hf hr
  refine ⟨us,hpos,hlen,hvalid,?_,?_,?_,by omega⟩
  · simp only [List.length_append,List.length_cons,List.length_nil,hcount]
  · simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,hrecon]
  · intro bin hb
    rcases List.mem_append.mp hb with hb|hb
    · exact hfit bin hb
    · simp only [List.mem_singleton] at hb
      subst bin
      omega

end ZkFormal.NearV3.Assembly
