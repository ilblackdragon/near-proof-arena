import ZkFormal.NearV3.Candidates.ProcActualSegmentFactor
namespace ZkFormal.NearV3.Candidates.ProcActualAfterMemoryReduction
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler
open ProcActualReplayRound ProcActualSegmentFactor

def pushCheck (s : Acc) : Except String Unit :=
  check (sortPush (ProcActualGeneratedPush.pushes (entryAcc s)).toList ==
    sortPush (ProcActualPoppedLog.buckets s).toList) "push log ≠ buckets"

theorem finish_group (I : Input) (tau : Nat) (cv : Array CReq) (st : PState) (s : Acc) :
    finishSegments I tau cv st s=(do
      pushCheck s
      ProcActualFinalStateGuards.checks s st
      let gs ← ProcActualSegments.build I tau s
      let cs ← forIn gs (#[] : ProcActualMemoryScan.Cmps) ProcActualMemoryScan.segmentStep
      afterMemory I tau cv st s gs cs) := by
  simp only [finishSegments,pushCheck,ProcActualFinalStateGuards.checks,bind_assoc]
  rfl

theorem finish_reduction (I : Input) (tau : Nat) (cv : Array CReq) (st : PState) (s : Acc)
    (hp : pushCheck s=.ok ()) (hf : ProcActualFinalStateGuards.checks s st=.ok ())
    (hm : ProcActualReplayMemory.Memory s) :
    ∃gs cs,ProcActualReplayFactor.finish I tau cv st s=afterMemory I tau cv st s gs cs ∧
      ProcActualSegments.build I tau s=.ok gs ∧
      forIn gs (#[] : ProcActualMemoryScan.Cmps) ProcActualMemoryScan.segmentStep=.ok cs := by
  obtain ⟨gs,cs,hg,hc⟩ := ProcActualSegments.build_scan I tau s hm
  refine ⟨gs,cs,?_,hg,hc⟩
  rw [ProcActualMemoryFactor.finish_eq,finish_eq,finish_group,hp]
  simp only [bind,Except.bind,hf,hg,hc]

theorem prepared_reduction (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (tau : Nat) (cv : Array CReq) (st : PState) (rs : List Round)
    (hcv : forIn (ProcPreparedSequence.input sp prev).raw #[]
      (ProcActualConverted.step (ProcPreparedSequence.input sp prev))=.ok cv)
    (hproc : ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs)) :
    ∃out gs cs,ProcActualReplayFactor.replay (ProcPreparedSequence.input sp prev) cv rs=.ok out ∧
      ProcActualRoundFactor.runRestRounds (ProcPreparedSequence.input sp prev) tau cv st rs=
        afterMemory (ProcPreparedSequence.input sp prev) tau cv st out gs cs := by
  obtain ⟨out,last,hr,ha,hf⟩ := ProcActualReplayTotal.prepared_replay sp hs prev cv st rs hcv hproc
  obtain ⟨out',hr',hp⟩ := ProcActualPushLogGuard.replay_push_guard sp hs prev cv st rs hcv hproc
  have he : out'=out := Except.ok.inj (hr'.symm.trans hr)
  subst out'
  have hm := ProcActualReplayMemory.replay_memory sp hs prev cv rs out hcv hr
  obtain ⟨gs,cs,heq,_,_⟩ := finish_reduction (ProcPreparedSequence.input sp prev) tau cv st out hp hf hm
  refine ⟨out,gs,cs,hr,?_⟩
  rw [ProcActualReplayFactor.rest_eq,hr]
  exact heq
theorem prefix_facts (I : Input) (cv : Array CReq) (st : PState) (rs : List Round) (ev : Ev)
    (h : ProcActualPrefix.runPrefix I=.ok (cv,st,rs,ev)) :
    forIn I.raw #[] (ProcActualConverted.step I)=.ok cv ∧ ProcActualInput.process I=.ok (st,rs) := by
  unfold ProcActualPrefix.runPrefix at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals exact ⟨by assumption,by assumption⟩

theorem run_reduction (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (tau : Nat) (cv : Array CReq) (st : PState)
    (rs : List Round) (ev : Ev)
    (h : ProcActualPrefix.runPrefix (ProcPreparedSequence.input sp prev)=.ok (cv,st,rs,ev)) :
    ∃out gs cs,ActualRun.run (ProcPreparedSequence.input sp prev) tau=
      afterMemory (ProcPreparedSequence.input sp prev) tau cv st out gs cs := by
  obtain ⟨hc,hp⟩ := prefix_facts _ cv st rs ev h
  obtain ⟨out,gs,cs,hr,he⟩ := prepared_reduction sp hs prev tau cv st rs hc hp
  refine ⟨out,gs,cs,?_⟩
  rw [ProcActualRunFactor.run_of_prefix _ tau cv st rs ev h,
    ProcActualEntryFactor.rest_eq,ProcActualRoundFactor.rest_eq]
  exact he
open NearSpec NearSpecV3 in
/-- Native execution and accepted preparation reduce the complete corrected
scheduler generator to its remaining round/operand checks. -/
theorem native_reduction {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (sp : SchedPub) (hsp : sp∈p.sched)
    (ctx : ApplyCtx) (hpub : schedPub ctx=some sp)
    (oldBytes : Option Bytes) (nativeOut : Output) (hcore : runCore sp oldBytes=some nativeOut) (tau : Nat) :
    ∃prev cv st,∃(ev : Ev),∃out gs cs,ProcActualCore.decodePrevious oldBytes=some prev ∧
      ActualRun.run (ProcPreparedSequence.input sp prev) tau=
        afterMemory (ProcPreparedSequence.input sp prev) tau cv st out gs cs ∧
      ev.state=nativeOut.state ∧ ev.granted=nativeOut.granted.map Prod.snd := by
  obtain ⟨prev,cv,st,rs,ev,hprev,hprefix,hstate,hgrants⟩ :=
    ProcActualPrefix.prepared_prefix hp sp hsp ctx hpub oldBytes nativeOut hcore
  obtain ⟨out,gs,cs,he⟩ := run_reduction sp (prepD0_sched hp sp hsp) prev tau cv st rs ev hprefix
  exact ⟨prev,cv,st,ev,out,gs,cs,hprev,he,hstate,hgrants⟩
end ZkFormal.NearV3.Candidates.ProcActualAfterMemoryReduction
