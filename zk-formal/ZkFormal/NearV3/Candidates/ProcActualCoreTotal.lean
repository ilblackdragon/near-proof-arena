import ZkFormal.NearV3.Candidates.ProcDistEventTotal
import ZkFormal.NearV3.Candidates.ProcActualStateAgreement
namespace ZkFormal.NearV3.Candidates.ProcActualCoreTotal
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler

/-- Once the process succeeds, the corrected core always completes distribution. -/
theorem core_exists (I : Input) (st : PState) (rs : List Round)
    (hp : ProcActualInput.process I=.ok (st,rs)) :
    ∃ev,ActualRun.coreEv I.ids I.p I.allowed I.raw I.seed I.ash I.prev=.ok ev := by
  obtain ⟨⟨gd,sord,rord⟩,hd⟩ := ProcDistEventTotal.link_pass_exists I.ids.length I.p I.allowed
    (ProcActualInput.allowances I.ids I.prev) st.sb st.rb
  unfold ProcActualInput.process ProcActualInput.initial at hp
  unfold ActualRun.coreEv
  simp only [hp,hd,bind,Except.bind,pure,Except.pure]
  exact ⟨_,rfl⟩

/-- Native core success yields a successful corrected core event with exactly
its native poststate bytes. Full replay-run success and grants agreement remain separate. -/
theorem scheduled_core_exists (ctx : NearSpecV3.ApplyCtx) (sp : SchedPub)
    (hs : SchedPubOk sp) (hpub : NearSpecV3.schedPub ctx=some sp)
    (oldBytes : Option NearSpec.Bytes) (out : Output) (h : runCore sp oldBytes=some out) :
    ∃prev ev,ProcActualCore.decodePrevious oldBytes=some prev ∧
      ActualRun.coreEv sp.ids sp.params sp.allowed (instOf sp).raw
        sp.seed sp.allShardsHash prev=.ok ev ∧ ev.state=out.state := by
  obtain ⟨prev,st,rs,hprev,hp,ho⟩ :=
    ProcActualNativeResult.scheduled_process_output ctx sp hs hpub oldBytes out h
  obtain ⟨ev,he⟩ := core_exists (ProcPreparedSequence.input sp prev) st rs hp
  refine ⟨prev,ev,hprev,he,?_⟩
  exact ProcActualStateAgreement.scheduled_state ctx sp hs hpub oldBytes out h prev hprev ev he
end ZkFormal.NearV3.Candidates.ProcActualCoreTotal
