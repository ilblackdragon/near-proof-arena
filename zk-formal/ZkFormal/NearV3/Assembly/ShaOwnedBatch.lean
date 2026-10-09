import ZkFormal.NearV3.Assembly.SourceShaOwnership
import ZkFormal.NearV3.Assembly.SchedulerShaOwnership
import ZkFormal.NearV3.Assembly.SourceSchedulerShaOk

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 ZkFormal.Sha.Gen

private theorem row_arithmetic (r b c : Nat) (hr : 64*r≤17*b+1288*c)
    (hb : b≤5277984) (hc : c≤12928) : r≤1662140 := by omega

/-- A shared witness list carries both the row budget and the ID allocation. -/
theorem schedulerBatch_rows (us : List SchedulerUpsertWitness) (hlen : us.length≤32)
    (hv : ∀u∈us,u.Valid) (hp : ∀u∈us,u.run.parts.length≤403)
    (hnodes : (us.map (fun u=>outputByteCharge u.run)).sum≤2131072)
    (hvalues : (us.map (fun u=>u.value.length)).sum≤3146912) :
    (honestRows (schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us)).length≤1663260 := by
  have hc := schedulerShaJobs_count 0 us hp
  have hcount : (schedulerShaJobs 0 us).length≤12928 := by omega
  have hb : ((schedulerShaJobs 0 us).map (fun M=>M.bytes.length)).sum≤5277984 := by
    rw [schedulerShaJobs_byte_count];omega
  have hr := row_arithmetic _ _ _ (sha_rows_cost (schedulerShaJobs 0 us)) hb hcount
  have hs := schedulerSanityJobs_rows 0 us hv
  simp only [honestRows,List.flatMap_append,List.length_append] at *
  omega

/-- Joint allocation evidence: actual native runs, exact message coverage, active
SHA capacity, and canonical disjoint kind IDs all hold on the SAME witness list. -/
theorem checkD0a_owned_sha_bins {cb wb raw : Bytes} {codes : List Bytes}
    {k : WalkD0} {w : StateWitness} {hint : Hint} {p : Prep}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w)
    (hc : checkD0a B0 cb wb=.ok ()) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hr : decodeStateWitness raw=.ok w) :
    ∃us : List SchedulerUpsertWitness,
      1≤us.length ∧ us.length≤32 ∧ (∀u∈us,u.Valid∧u.pre.wf=true) ∧
      let messages := sourceShaMessages p.lists w.entries ++
        (schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us)
      let bins := sourceShaMessageBins (sourceShaMessages p.lists w.entries) ++
        [schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us]
      bins.length=4 ∧ bins.flatten=messages ∧
      (∀bin∈bins,ZkFormal.Sha.MsgsOk bin) ∧
      (∀M∈messages,M.id<ZkFormal.Algebra.P ∧ (M.id%16=11 ∨ M.id%16=12 ∨ M.id%16=13)) := by
  obtain ⟨us,hpos,hlen,hvalid,_,hnodes,hvalues⟩ := checkD0a_upsert_all_bounds hk hw hc
  have hparts := fun u hu=>(hvalid u hu).2.2.1
  have hrows := schedulerBatch_rows us hlen (fun u hu=>(hvalid u hu).1) hparts hnodes hvalues
  obtain ⟨hcount,hrecon,hfit⟩ := checkD0a_source_sha_messages hc hp hf hr
  have hbsource := sourceShaMessages_bytes p.lists w.entries
  have hbscheduler : ∀M∈schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us,∀b∈M.bytes,b<256 := by
    intro M hm b hb
    rcases List.mem_append.mp hm with hm|hm
    · exact schedulerShaJobs_bytes 0 us M hm b hb
    · exact schedulerSanityJobs_bytes 0 us M hm b hb
  refine ⟨us,hpos,hlen,fun u hu=>⟨(hvalid u hu).1,(hvalid u hu).2.1⟩,?_,?_,?_,?_⟩
  · simp only [List.length_append,List.length_cons,List.length_nil,hcount]
  · simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,hrecon]
  · intro bin hbin
    rcases List.mem_append.mp hbin with hbin|hbin
    · have hh := hfit bin hbin
      refine ⟨?_,fun M hm=>sha_message_len_of_rows hh hm,hh⟩
      intro M hm
      have hx := List.mem_flatten.mpr ⟨bin,hbin,hm⟩
      rw [hrecon] at hx
      exact hbsource M hx
    · simp only [List.mem_singleton] at hbin
      subst bin
      have hh : (honestRows (schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us)).length≤2^22 := by omega
      exact ⟨hbscheduler,fun M hm=>sha_message_len_of_rows hh hm,hh⟩
  · intro M hm
    rcases List.mem_append.mp hm with hm|hm
    · obtain ⟨hbound,hkind⟩ := checkD0a_source_message_ids hc hp hf hr hm
      exact ⟨hbound,Or.inr (Or.inr hkind)⟩
    · rcases List.mem_append.mp hm with hm|hm
      · obtain ⟨hbound,hkind⟩ := schedulerShaJobs_ids 0 us (by omega) hparts M hm
        exact ⟨hbound,Or.inr (Or.inl hkind)⟩
      · obtain ⟨hbound,hkind⟩ := schedulerSanityJobs_ids 0 us (by omega) M hm
        exact ⟨hbound,Or.inl hkind⟩

/-- Exactly the existing trie SHA glue's other-kind ownership condition. -/
theorem shaBatch_other_ids {messages : List ZkFormal.Sha.Gen.Msg}
    (hids : ∀M∈messages,M.id<ZkFormal.Algebra.P ∧
      (M.id%16=11 ∨ M.id%16=12 ∨ M.id%16=13)) :
    ∀m∈expectedBytes messages,∀a,m.head?=some a →
      a<ZkFormal.Algebra.P ∧ a%16≠ZkFormal.Near.K_NPRE ∧
      a%16≠ZkFormal.Near.K_NPOST ∧ a%16≠ZkFormal.Near.K_VPRE := by
  intro m hm a ha
  obtain ⟨M,hM,hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨pos,_,rfl⟩ := List.mem_map.mp hm
  simp only [List.head?_cons,Option.some.injEq] at ha
  subst a
  obtain ⟨hb,hk⟩ := hids M hM
  refine ⟨hb,?_,?_,?_⟩ <;>
    simp only [ZkFormal.Near.K_NPRE,ZkFormal.Near.K_NPOST,ZkFormal.Near.K_VPRE] <;> omega

end ZkFormal.NearV3.Assembly
