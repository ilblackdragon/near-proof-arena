import ZkFormal.NearV3.Candidates.ProcActualModelKeyCap
import ZkFormal.NearV3.Candidates.ProcActualParameterGuard
namespace ZkFormal.NearV3.Candidates.ProcActualOperandReduction
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler

theorem prepared_reduction (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (tau : Nat) (cv : Array CReq) (st : PState) (rs : List Round)
    (hcv : forIn (ProcPreparedSequence.input sp prev).raw #[]
      (ProcActualConverted.step (ProcPreparedSequence.input sp prev))=.ok cv)
    (hproc : ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs)) :
    ∃s gs cs,ProcActualReplayFactor.replay (ProcPreparedSequence.input sp prev) cv rs=.ok s ∧
      ProcActualRoundFactor.runRestRounds (ProcPreparedSequence.input sp prev) tau cv st rs =
      (do
        check (cs.all fun (x,y,_)=>x<2^29 && y<2^29) "comparison operand ≥ 2^29"
        pure (ProcActualParameterGuard.result (ProcPreparedSequence.input sp prev) tau cv st s gs cs)) := by
  apply ProcActualParameterGuard.suffix_reduction sp hs prev tau cv st rs hcv hproc
  intro s hr
  exact ProcActualModelKeyCap.replay_decreasing _ cv st rs s hs.params hproc hr

theorem run_reduction (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (tau : Nat) (cv : Array CReq) (st : PState)
    (rs : List Round) (ev : Ev)
    (h : ProcActualPrefix.runPrefix (ProcPreparedSequence.input sp prev)=.ok (cv,st,rs,ev)) :
    ∃s gs cs,ActualRun.run (ProcPreparedSequence.input sp prev) tau =
      (do
        check (cs.all fun (x,y,_)=>x<2^29 && y<2^29) "comparison operand ≥ 2^29"
        pure (ProcActualParameterGuard.result (ProcPreparedSequence.input sp prev) tau cv st s gs cs)) := by
  obtain ⟨hc,hp⟩ := ProcActualAfterMemoryReduction.prefix_facts _ cv st rs ev h
  obtain ⟨s,gs,cs,_,he⟩ := prepared_reduction sp hs prev tau cv st rs hc hp
  refine ⟨s,gs,cs,?_⟩
  rw [ProcActualRunFactor.run_of_prefix _ tau cv st rs ev h,
    ProcActualEntryFactor.rest_eq,ProcActualRoundFactor.rest_eq]
  exact he
open NearSpec NearSpecV3 in
/-- Accepted preparation and native execution construct the complete corrected
scheduler run up to the single remaining operand guard. -/
theorem native_reduction {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (sp : SchedPub) (hsp : sp∈p.sched)
    (ctx : ApplyCtx) (hpub : schedPub ctx=some sp)
    (oldBytes : Option Bytes) (nativeOut : Output) (hcore : runCore sp oldBytes=some nativeOut) (tau : Nat) :
    ∃prev cv st,∃(ev : Ev),∃s gs,∃cs : ProcActualMemoryScan.Cmps,ProcActualCore.decodePrevious oldBytes=some prev ∧
      ActualRun.run (ProcPreparedSequence.input sp prev) tau=
        (do
          Gen.check (cs.all fun (x,y,_)=>x<2^29 && y<2^29) "comparison operand ≥ 2^29"
          pure (ProcActualParameterGuard.result (ProcPreparedSequence.input sp prev) tau cv st s gs cs)) ∧
      ev.state=nativeOut.state ∧ ev.granted=nativeOut.granted.map Prod.snd := by
  obtain ⟨prev,cv,st,rs,ev,hprev,hprefix,hstate,hgrants⟩ :=
    ProcActualPrefix.prepared_prefix hp sp hsp ctx hpub oldBytes nativeOut hcore
  obtain ⟨s,gs,cs,he⟩ := run_reduction sp (prepD0_sched hp sp hsp) prev tau cv st rs ev hprefix
  exact ⟨prev,cv,st,ev,s,gs,cs,hprev,he,hstate,hgrants⟩

theorem guard_success_iff (cs : ProcActualMemoryScan.Cmps) (r : Run) :
    (∃out,(do
      check (cs.all fun (x,y,_)=>x<2^29 && y<2^29) "comparison operand ≥ 2^29"
      pure r : Except String Run)=.ok out) ↔
      (cs.all fun (x,y,_)=>x<2^29 && y<2^29)=true := by
  cases hc : cs.all (fun (x,y,_)=>x<2^29 && y<2^29) <;>
    simp [check,hc,bind,Except.bind,pure,Except.pure]

theorem run_success_iff (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (tau : Nat) (cv : Array CReq) (st : PState)
    (rs : List Round) (ev : Ev)
    (h : ProcActualPrefix.runPrefix (ProcPreparedSequence.input sp prev)=.ok (cv,st,rs,ev)) :
    ∃cs : ProcActualMemoryScan.Cmps,
      (∃r,ActualRun.run (ProcPreparedSequence.input sp prev) tau=.ok r) ↔
        (cs.all fun (x,y,_)=>x<2^29 && y<2^29)=true := by
  obtain ⟨s,gs,cs,he⟩ := run_reduction sp hs prev tau cv st rs ev h
  refine ⟨cs,?_⟩
  rw [he]
  exact guard_success_iff cs _
end ZkFormal.NearV3.Candidates.ProcActualOperandReduction
