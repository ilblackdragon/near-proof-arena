import ZkFormal.NearV3.Candidates.ProcActualMemoryValues
import ZkFormal.NearV3.Candidates.ProcReplayTimestampActual
import ZkFormal.NearV3.Candidates.ProcActualPriorKeyCap
import ZkFormal.NearV3.Candidates.ProcActualSegmentOperandBounds
namespace ZkFormal.NearV3.Candidates.ProcActualPreparedGenerator
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler ProcActualReplayRound

theorem selected_values (B : Nat) (logs : Array (Array Gen.MOp))
    (h : ProcActualMemoryValues.Values B logs) (i : Nat) :
    ∀o∈logs[i]!.toList,o.op=OP_GRANT → o.vin<B ∧ o.inc<B := by
  by_cases hi : i<logs.size
  · rw [getElem!_pos logs i hi]
    exact h logs[i] (by simpa using Array.getElem_mem hi)
  · rw [getElem!_neg logs i hi]
    change ∀o∈([] : List Gen.MOp),o.op=OP_GRANT → o.vin<B ∧ o.inc<B
    simp

theorem time_bound (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (cv : Array CReq) (st : PState) (rs : List Round) (s : Acc)
    (hcv : forIn (ProcPreparedSequence.input sp prev).raw #[]
      (ProcActualConverted.step (ProcPreparedSequence.input sp prev))=.ok cv)
    (hp : ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs))
    (hr : ProcActualReplayFactor.replay (ProcPreparedSequence.input sp prev) cv rs=.ok s) :
    time s<2^29 := by
  let I := ProcPreparedSequence.input sp prev
  have he : convRaw I.p I.ids.length I.raw=ProcActualConversionExact.view cv := by
    simpa [ProcActualConversionExact.view] using
      (ProcActualConversionExact.loop_view I I.raw #[] cv hcv).symm
  have hm := hp
  unfold ProcActualInput.process at hm
  rw [he] at hm
  have ht := ProcReplayTimestampActual.replay_bound I cv rs s hcv
    (ProcPreparedSequence.input_bounds sp prev hs).2.2 _ _ _ hm hr
  omega

theorem replay_finish (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (tau : Nat) (cv : Array CReq) (st : PState) (rs : List Round) (s : Acc)
    (hcv : forIn (ProcPreparedSequence.input sp prev).raw #[]
      (ProcActualConverted.step (ProcPreparedSequence.input sp prev))=.ok cv)
    (hp : ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs))
    (hr : ProcActualReplayFactor.replay (ProcPreparedSequence.input sp prev) cv rs=.ok s) :
    ∃r,ProcActualReplayFactor.finish (ProcPreparedSequence.input sp prev) tau cv st s=.ok r := by
  let I := ProcPreparedSequence.input sp prev
  obtain ⟨a,ha,hpush⟩ := ProcActualPushLogGuard.replay_push_guard sp hs prev cv st rs hcv hp
  have he := Except.ok.inj (ha.symm.trans hr)
  subst a
  obtain ⟨a,last,ha,halign,hfinal⟩ := ProcActualReplayTotal.prepared_replay sp hs prev cv st rs hcv hp
  have he := Except.ok.inj (ha.symm.trans hr)
  subst a
  have hm := ProcActualReplayMemory.replay_memory sp hs prev cv rs s hcv hr
  have ht := time_bound sp hs prev cv st rs s hcv hp hr
  have htimes := ProcActualReplayTimeEnvelope.memory_times (2^29) s hm (Nat.le_of_lt ht)
  have hv := ProcActualMemoryValues.replay_values sp hs prev cv rs s hcv hr
  apply ProcActualSegmentOperandBounds.finish_success sp hs prev tau cv st s hpush hfinal hm
    (ProcActualRoundTimes.replay_good sp hs prev cv st rs hcv hp s hr)
    (ProcActualReplayTimeEnvelope.replay_round_times _ I cv rs s hr ht)
    (fun rd hd hn=>⟨ProcActualModelKeyCap.replay_decreasing I cv st rs s hs.params hp hr rd hd hn,
      ProcActualPriorKeyCap.replay_prior_operand I cv st rs s hs.params hp hr rd hd⟩)
  apply ProcActualSegmentOperandBounds.make_bound
  · intro i o ho
    exact ⟨htimes.1 i o ho,selected_values _ _ hv.2.2.2.1 i o ho⟩
  · intro i o ho
    exact ⟨htimes.2.1 i o ho,selected_values _ _ hv.2.2.2.2.1 i o ho⟩
  · intro i o ho
    exact ⟨htimes.2.2 i o ho,selected_values _ _ hv.2.2.2.2.2 i o ho⟩
theorem suffix_success (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (tau : Nat) (cv : Array CReq) (st : PState) (rs : List Round)
    (hcv : forIn (ProcPreparedSequence.input sp prev).raw #[]
      (ProcActualConverted.step (ProcPreparedSequence.input sp prev))=.ok cv)
    (hp : ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs)) :
    ∃r,ProcActualRoundFactor.runRestRounds (ProcPreparedSequence.input sp prev) tau cv st rs=.ok r := by
  obtain ⟨s,last,hr,_,_⟩ := ProcActualReplayTotal.prepared_replay sp hs prev cv st rs hcv hp
  obtain ⟨r,hf⟩ := replay_finish sp hs prev tau cv st rs s hcv hp hr
  refine ⟨r,?_⟩
  rw [ProcActualReplayFactor.rest_eq,hr]
  exact hf

theorem run_success (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (tau : Nat) (cv : Array CReq) (st : PState)
    (rs : List Round) (ev : Ev)
    (h : ProcActualPrefix.runPrefix (ProcPreparedSequence.input sp prev)=.ok (cv,st,rs,ev)) :
    ∃r,ActualRun.run (ProcPreparedSequence.input sp prev) tau=.ok r := by
  obtain ⟨hc,hp⟩ := ProcActualAfterMemoryReduction.prefix_facts _ cv st rs ev h
  obtain ⟨r,hr⟩ := suffix_success sp hs prev tau cv st rs hc hp
  refine ⟨r,?_⟩
  rw [ProcActualRunFactor.run_of_prefix _ tau cv st rs ev h,
    ProcActualEntryFactor.rest_eq,ProcActualRoundFactor.rest_eq]
  exact hr

open NearSpec NearSpecV3 in
/-- Totality of the corrected scheduler generator for accepted D0 preparation
and successful native scheduler execution. This is not full proof-system completeness. -/
theorem native_success {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (sp : SchedPub) (hsp : sp∈p.sched)
    (ctx : ApplyCtx) (hpub : schedPub ctx=some sp)
    (oldBytes : Option Bytes) (nativeOut : Output) (hcore : runCore sp oldBytes=some nativeOut) (tau : Nat) :
    ∃prev r,ProcActualCore.decodePrevious oldBytes=some prev ∧
      ActualRun.run (ProcPreparedSequence.input sp prev) tau=.ok r := by
  obtain ⟨prev,cv,st,rs,ev,hprev,hprefix,_,_⟩ :=
    ProcActualPrefix.prepared_prefix hp sp hsp ctx hpub oldBytes nativeOut hcore
  obtain ⟨r,hr⟩ := run_success sp (prepD0_sched hp sp hsp) prev tau cv st rs ev hprefix
  exact ⟨prev,r,hprev,hr⟩
end ZkFormal.NearV3.Candidates.ProcActualPreparedGenerator
