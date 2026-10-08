import ZkFormal.NearV3.Rcpt.Candidates.NativeExecutionRebased

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 Assembly Render.UpsGen

/-- The missing transition's scheduler output is its actual native poststate. -/
theorem missing_exact_upsert {ctx : ApplyCtx} {pre post : PTrie}
    (h : applyMissingChunk prims ctx pre=.ok post) :
    ∃u : SchedulerUpsertWitness,u.ctx=ctx ∧ u.pre=pre ∧ u.run.output=post ∧ u.Valid := by
  unfold applyMissingChunk at h
  obtain ⟨_,_,h⟩:=ReexecV3D0.bind_ok' h
  obtain ⟨⟨mid,so⟩,hs,h⟩:=ReexecV3D0.bind_ok' h
  cases h
  obtain ⟨_,_,_,_,_,_,_,hu⟩:=schedStep_complete hs
  obtain ⟨u,_,hc,hp,hv,ho,hw⟩:=chosen_rebased_witness hs (.nil pre) (by simp) hu
  exact ⟨u,hc,hp,ho,hw⟩

/-- Retain ordered native pre/post pairs for every implicit scheduler witness. -/
theorem implicit_exact_upserts {k root pairs steps last}
    (h : ImplicitTraceValid k root pairs steps last) (hl : k.L.numShards≤64) :
    ∃us : List SchedulerUpsertWitness,
      us.map (fun u=>(u.pre,u.run.output))=steps.map (fun s=>(s.pre,s.post)) ∧
      ∀u∈us,u.Valid ∧ u.value.length≤98341 := by
  induction h with
  | nil=>exact ⟨[],rfl,by simp⟩
  | cons root b t rest steps post last hr hp ht ih=>
    obtain ⟨u,hctx,hpre,hpost,hvalid⟩:=missing_exact_upsert hr
    obtain ⟨us,hus,hgood⟩:=ih
    have hlen:=SchedulerUpsertWitness.value_bound hvalid (by rw [hctx];exact hl)
    refine ⟨u::us,?_,?_⟩
    · simp [hpre,hpost,hus]
    · intro x hx
      rcases List.mem_cons.mp hx with rfl|hx
      · exact ⟨hvalid,hlen⟩
      · exact hgood x hx

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
