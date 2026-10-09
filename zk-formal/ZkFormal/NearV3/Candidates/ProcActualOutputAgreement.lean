import ZkFormal.NearV3.Candidates.ProcActualProcessFacts
import ZkFormal.NearV3.Candidates.ProcActualCoreTotal
import ZkFormal.NearV3.Candidates.ProcDistGrantBounds
namespace ZkFormal.NearV3.Candidates.ProcActualOutputAgreement
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler

theorem core_granted (sp : SchedPub) (hs : SchedPubOk sp)
    (ha : sp.allowed.size=sp.ids.length*sp.ids.length) (prev : NearSpec.Bandwidth.State)
    (st : PState) (rs : List Round) (ev : Ev)
    (hp : ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs))
    (hc : ActualRun.coreEv sp.ids sp.params sp.allowed (instOf sp).raw
      sp.seed sp.allShardsHash prev=.ok ev) :
    ev.granted=(ProcActualNativeResult.finish sp prev (ProcNativeGrant.native st)).granted.map Prod.snd := by
  obtain ⟨hinv,hshape⟩ := ProcActualProcessFacts.prepared_facts sp hs ha prev st rs hp
  have hM : sp.params.maxShardBandwidth≤u64Max := by rw [pv86_maxShard hs.params]; decide
  unfold ProcActualInput.process ProcActualInput.initial ProcPreparedSequence.input at hp
  unfold ActualRun.coreEv at hc
  simp only [hp,bind,Except.bind] at hc
  cases hd : distributeEv sp.ids.length sp.allowed st.sb st.rb
      (linkPass sp.ids.length sp.params sp.allowed (ProcActualInput.allowances sp.ids prev)).cntS
      (linkPass sp.ids.length sp.params sp.allowed (ProcActualInput.allowances sp.ids prev)).cntR with
  | error e => simp only [hd] at hc; cases hc
  | ok out =>
    rcases out with ⟨gd,sord,rord⟩
    simp only [hd,pure,Except.pure,Except.ok.injEq] at hc
    subst ev
    simp only [ProcActualNativeResult.finish,List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro l hl
    exact (ProcDistGrantBounds.event_granted sp.ids.length sp.params.maxShardBandwidth hs.n1 hM
      sp.params sp.allowed (ProcActualInput.allowances sp.ids prev) (ProcNativeGrant.native st)
      hinv hshape.1 hshape.2.1 ha hshape.2.2 gd sord rord hd l (List.mem_range.mp hl)).symm

/-- Native scheduler core success constructs a corrected core event with matching
poststate bytes and every grant amount in the same sender-major order. -/
theorem scheduled_output_exists (ctx : NearSpecV3.ApplyCtx) (sp : SchedPub)
    (hs : SchedPubOk sp) (hpub : NearSpecV3.schedPub ctx=some sp)
    (oldBytes : Option NearSpec.Bytes) (out : Output) (h : runCore sp oldBytes=some out) :
    ∃prev ev,ProcActualCore.decodePrevious oldBytes=some prev ∧
      ActualRun.coreEv sp.ids sp.params sp.allowed (instOf sp).raw
        sp.seed sp.allShardsHash prev=.ok ev ∧
      ev.state=out.state ∧ ev.granted=out.granted.map Prod.snd := by
  obtain ⟨prev,st,rs,hprev,hp,ho⟩ :=
    ProcActualNativeResult.scheduled_process_output ctx sp hs hpub oldBytes out h
  obtain ⟨ev,he⟩ := ProcActualCoreTotal.core_exists (ProcPreparedSequence.input sp prev) st rs hp
  refine ⟨prev,ev,hprev,he,ProcActualStateAgreement.scheduled_state ctx sp hs hpub oldBytes out h prev hprev ev he,?_⟩
  rw [core_granted sp hs (ProcActualPublic.schedPub_fields ctx sp hpub).1 prev st rs ev hp he,ho]
end ZkFormal.NearV3.Candidates.ProcActualOutputAgreement
