import ZkFormal.NearV3.Rcpt.Candidates.NativeReplayByteSize
import ZkFormal.NearV3.Assembly.SchedulerSizedWitness

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 Assembly Render.UpsGen

/-- The actual rebased UPS run reads the old-record post tree, reaches the
native final trie, and retains the accepted original unfolded byte charge. -/
theorem newchunk_rebased_upsert_witness {ctx : ApplyCtx} {pre : PTrie} {rs : List Receipt}
    {out : MainOut} (hw : TrieShape pre) (hwell : pre.wf=true)
    (h : applyNewChunk prims ctx pre rs=.ok out) :
    ∃writes,∃oldPost mid : PTrie,∃so : SchedOut,∃u : SchedulerUpsertWitness,
      schedStep prims ctx pre=.ok (mid,so) ∧
      schedulerUpsertWitness ctx oldPost=.ok u ∧
      u.ctx=ctx ∧ u.pre=oldPost ∧ u.value=so.state ∧ u.run.output=out.trie ∧ u.Valid ∧
      SizedAccountRun pre writes oldPost ∧ oldPost.wf=true ∧
      NearSpecV3.unfoldedBytesT oldPost=NearSpecV3.unfoldedBytesT pre := by
  obtain ⟨writes,oldPost,mid,so,hs,hs',hkeys,hr,hp,hpost,hlen⟩:=newchunk_rebased_scheduler hw hwell h
  obtain ⟨_,_,_,_,_,_,_,hu⟩:=schedStep_complete hs'
  obtain ⟨run,hrun,hout⟩:=traceUpsert_complete hu
  let u : SchedulerUpsertWitness:=⟨ctx,oldPost,so.state,run⟩
  have hv : u.Valid := ⟨hrun,so,by simpa only [u,hout] using hs',rfl⟩
  refine ⟨writes,oldPost,mid,so,u,hs,?_,rfl,rfl,rfl,hout,hv,hr,hpost,?_⟩
  · simp [schedulerUpsertWitness,hs',hrun,bind,Except.bind,pure,Except.pure,u]
  · exact SizedAccountRun.unfolded_bytes hr

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
