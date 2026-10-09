import ZkFormal.NearV3.Assembly.SourceShaBytes

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 ZkFormal.Sha.Gen

theorem schedulerSanityJobs_bytes (tau : Nat) (us : List SchedulerUpsertWitness) :
    ∀M∈schedulerSanityJobs tau us,∀b∈M.bytes,b<256 := by
  induction us generalizing tau with
  | nil => simp [schedulerSanityJobs]
  | cons u us ih =>
    intro M hm b hb
    simp only [schedulerSanityJobs,List.mem_cons] at hm
    rcases hm with rfl|hm
    · obtain ⟨x,_,rfl⟩ := List.mem_map.mp hb
      exact x.toNat_lt
    · exact ih (tau+1) M hm b hb

/-- Every allocated source/scheduler partition satisfies the unchanged SHA honest
renderer's full input contract: byte ranges, message lengths, and physical rows. -/
theorem checkD0a_source_scheduler_sha_ok {cb wb raw : Bytes} {codes : List Bytes}
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
      (∀ bin∈bins,ZkFormal.Sha.MsgsOk bin) := by
  obtain ⟨us,hpos,hlen,hvalid,hcount,hrecon,hfit,_⟩ :=
    checkD0a_source_scheduler_messages hk hw hc hp hf hr
  refine ⟨us,hpos,hlen,hvalid,hcount,hrecon,?_⟩
  intro bin hbin
  have hrows := hfit bin hbin
  refine ⟨?_,fun M hm => sha_message_len_of_rows hrows hm,hrows⟩
  intro M hm b hb
  have hM := List.mem_flatten.mpr ⟨bin,hbin,hm⟩
  rw [hrecon] at hM
  rcases List.mem_append.mp hM with hM|hM
  · exact sourceShaMessages_bytes _ _ M hM b hb
  · rcases List.mem_append.mp hM with hM|hM
    · exact schedulerShaJobs_bytes 0 us M hM b hb
    · exact schedulerSanityJobs_bytes 0 us M hM b hb

end ZkFormal.NearV3.Assembly
