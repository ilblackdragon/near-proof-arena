import ZkFormal.NearV3.Assembly.QueueSeed
import ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Qv Qv.Candidates.CombinedWalkGen

theorem mainPlan_slot {pre : PTrie} {v : MainValues} {K : Nat} {resolve : Resolve}
    {w : Walk} (h : w ∈ mainPlan pre v K resolve) :
    w.tau=0 ∧ (mainRequests pre v)[w.slot]?=some (w.request v.shards) ∧
      (w.vid,w.users)=resolve w.tau w.slot := by
  simp only [mainPlan,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with (rfl | rfl | rfl) | h
  · simp [mainWalk,mainRequests,Walk.request,Kind.bytes,keyDelayedIdx]
  · simp [mainWalk,mainRequests,Walk.request,Kind.bytes,keyBufferedIdx]
  · simp [mainWalk,mainRequests,Walk.request,Kind.bytes,keyYieldIdx]
  · obtain ⟨⟨s,i⟩,hi,rfl⟩ := List.mem_map.mp h
    have hs := List.mk_mem_zipIdx_iff_getElem?.mp hi
    simp [mainWalk,mainRequests,Walk.request,Kind.bytes,keyGroupsData,
      Nat.add_comm,hs]

theorem plan_slot {pre : PTrie} {v : MainValues} {pres : List PTrie} {resolve : Resolve}
    {w : Walk} (h : w ∈ plan pre v pres resolve) :
    ∃ t rs, (queueInputs pre v pres)[w.tau]?=some (t,rs) ∧
      rs[w.slot]?=some (w.request v.shards) ∧ (w.vid,w.users)=resolve w.tau w.slot := by
  simp only [plan,List.mem_append] at h
  rcases h with h | h
  · obtain ⟨ht,hs,hr⟩ := mainPlan_slot h
    exact ⟨pre,mainRequests pre v,by simp [queueInputs,ht],hs,hr⟩
  · obtain ⟨⟨t,i⟩,hi,rfl⟩ := List.mem_map.mp h
    have ht := List.mk_mem_zipIdx_iff_getElem?.mp hi
    refine ⟨t,[missingRequest t],?_,?_,?_⟩
    · simp [queueInputs,ht]
    · simp [Walk.request,Kind.bytes,missingRequest,keyDelayedIdx]
    · rfl

/-- Every present generated walk resolves to the one selected native provider. -/
theorem plan_provider {pre : PTrie} {v : MainValues} {pres : List PTrie}
    (hh : ∀ x ∈ queueInputs pre v pres, ∀ r ∈ x.2, r.Holds x.1)
    {w : Walk} (hw : w ∈ plan pre v pres (queueForestResolve (queueInputs pre v pres) 0))
    {b : Bytes} (hb : w.value=some b) :
    ∃ p ∈ queueForestProviders 0 0 (queueInputs pre v pres),
      p.tau=w.tau ∧ p.bytes=b ∧ (w.vid,w.users)=(p.vid,p.users) := by
  obtain ⟨t,rs,ht,hs,hr⟩ := plan_slot hw
  have hh' := (hh (t,rs) (List.mem_of_getElem? ht) _ (List.mem_of_getElem? hs)).1
  change t.find (w.request v.shards).key=some w.value at hh'
  rw [hb] at hh'
  obtain ⟨p,hp,hpt,hpb,hpr⟩ := queueForestResolve_present (queueInputs pre v pres) 0 0 ht hs hh'
  exact ⟨p,hp,by simpa using hpt,hpb,hr.trans hpr⟩

end ZkFormal.NearV3.Assembly
