import ZkFormal.NearV3.Rcpt.Candidates.NativeRebasedUpsertWitness

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 Assembly Render.UpsGen

/-- Preserve the caller's already chosen replay tree and scheduler output. -/
theorem chosen_rebased_witness {ctx : ApplyCtx} {pre mid oldPost final : PTrie} {so : SchedOut}
    {writes : List (List Nat×Bytes)} (hs : schedStep prims ctx pre=.ok (mid,so))
    (hr : SizedAccountRun pre writes oldPost) (hd : ∀q∈writes.map Prod.fst,q≠keyBwState)
    (hfinal : oldPost.upsert keyBwState so.state=some final) :
    ∃u : SchedulerUpsertWitness,schedulerUpsertWitness ctx oldPost=.ok u ∧
      u.ctx=ctx ∧ u.pre=oldPost ∧ u.value=so.state ∧ u.run.output=final ∧ u.Valid := by
  have hf:=AccountWriteRun.find_untouched hr.forget keyBwState hd
  have hs':=schedStep_rebased hs hf hfinal
  obtain ⟨run,hrun,hout⟩:=traceUpsert_complete hfinal
  let u : SchedulerUpsertWitness:=⟨ctx,oldPost,so.state,run⟩
  have hv : u.Valid := ⟨hrun,so,by simpa only [u,hout] using hs',rfl⟩
  refine ⟨u,?_,rfl,rfl,rfl,hout,hv⟩
  simp [schedulerUpsertWitness,hs',hrun,bind,Except.bind,pure,Except.pure,u]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
