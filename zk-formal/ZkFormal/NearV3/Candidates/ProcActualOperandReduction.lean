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
end ZkFormal.NearV3.Candidates.ProcActualOperandReduction
