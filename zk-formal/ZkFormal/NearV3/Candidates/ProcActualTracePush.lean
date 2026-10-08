import ZkFormal.NearV3.Candidates.ProcActualRoundPush
import ZkFormal.NearV3.Candidates.ProcActualModelValid
namespace ZkFormal.NearV3.Candidates.ProcActualTracePush
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler
open ProcActualReplayRound ProcActualRoundTransition
theorem trace_push (I : Input) (cv : Array CReq)
    (hcv : forIn I.raw #[] (ProcActualConverted.step I)=.ok cv)
    (key : List Nat) (initial : PState) (start : Nat) (rs : List Round) (st : PState) (t : Nat)
    (ht : ProcModelBatchTrace.Trace I.ids.length I.allowed (ProcActualConversionExact.view cv)
      initial start rs st t)
    (hs : ProcActualAllowanceShape.Shape I.ids.length initial)
    (hv : ∀rd∈rs,∀v∈rd.shuffled,ProcRequestPointers.Valid (ProcActualConversionExact.view cv) v)
    (hsize : ∀rd∈rs,1≤rd.bucket.length ∧ rd.bucket.length<16384)
    (htags : ∀rd∈rs,ProcActualBucketGuards.Tagged rd)
    (hz : ∀rd∈rs,rd.key≠0 → rd.z=0)
    (s : Acc) (hc : ProcActualReplayClock.Clock s) (ha : Aligned key cv s initial start) :
    ∃out,forIn rs s (step I cv key)=.ok out ∧ Aligned key cv out st t ∧ ProcActualReplayClock.Clock out ∧
      (ProcActualGeneratedPush.pushes (entryAcc out)).toList=
        (ProcActualGeneratedPush.pushes (entryAcc s)).toList++
          (ProcPushConservation.generated rs).map (ProcPushConservation.stamp cv.size) := by
  induction ht with
  | nil => exact ⟨s,rfl,ha,hc,by simp [ProcPushConservation.generated]⟩
  | @snoc rs st t ht rd st' t' hb ih =>
    obtain ⟨mid,hm,ham,hcm,hpm⟩ := ih (fun r hr=>hv r (by simp [hr]))
      (fun r hr=>hsize r (by simp [hr])) (fun r hr=>htags r (by simp [hr])) (fun r hr=>hz r (by simp [hr]))
    have hmshape := trace_shape I.ids.length I.allowed (ProcActualConversionExact.view cv)
      initial start rs st t hs ht
    have hb' := hb
    rw [←ham.1,←ham.2] at hb'
    have hms : ProcActualAllowanceShape.Shape I.ids.length
        (ProcActualReplayEntry.state (entryAcc mid) (ZkFormal.Chacha.rngAt key (position mid))) := by
      rw [ham.1]; exact hmshape
    obtain ⟨out,ho,hao,hco,hpo⟩ := ProcActualRoundPush.round_push I cv hcv key rd mid st' t' hcm (hz rd (by simp)) hms
      (hv rd (by simp)) (hsize rd (by simp)) (htags rd (by simp)) hb'
    refine ⟨out,?_,hao,hco,?_⟩
    · exact append_ok (step I cv key) (step_yields I cv key) rs [rd] s mid out hm
        (by simp only [List.forIn_cons,ho,bind,Except.bind,List.forIn_nil,pure,Except.pure])

    · rw [hpo,hpm]
      simp [ProcPushConservation.generated,List.map_append,List.append_assoc]

theorem prepared_push (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (cv : Array CReq) (st : PState) (rs : List Round)
    (hcv : forIn (ProcPreparedSequence.input sp prev).raw #[]
      (ProcActualConverted.step (ProcPreparedSequence.input sp prev))=.ok cv)
    (hproc : ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs))
    (s : Acc) (hclock : ProcActualReplayClock.Clock s)
    (ha : Aligned (NearSpecV3.leWords sp.seed) cv s
      (ProcActualInput.initial (ProcPreparedSequence.input sp prev)) cv.size) :
    ∃out last,forIn rs s (step (ProcPreparedSequence.input sp prev) cv (NearSpecV3.leWords sp.seed))=.ok out ∧
      Aligned (NearSpecV3.leWords sp.seed) cv out st last ∧ ProcActualReplayClock.Clock out ∧
      (ProcActualGeneratedPush.pushes (entryAcc out)).toList=
        (ProcActualGeneratedPush.pushes (entryAcc s)).toList++
          (ProcPushConservation.generated rs).map (ProcPushConservation.stamp cv.size) := by
  let I := ProcPreparedSequence.input sp prev
  have hreq : convRaw I.p I.ids.length I.raw=ProcActualConversionExact.view cv := by
    simpa [ProcActualConversionExact.view] using
      (ProcActualConversionExact.loop_view I I.raw #[] cv hcv).symm
  have hlen : (convRaw I.p I.ids.length I.raw).length=cv.size := by
    rw [hreq]; simp [ProcActualConversionExact.view]
  obtain ⟨last,ht⟩ := ProcModelBatchTrace.process_trace I.ids.length I.allowed
    (convRaw I.p I.ids.length I.raw) (ProcActualInput.initial I) st _ rs hproc
  rw [hlen,hreq] at ht
  have hgood := ProcPreparedRequestGood.converted_good I.p I.ids.length I.raw hs.params
  have hv := ProcShufflePointers.process_pointers I.ids.length I.allowed
    (convRaw I.p I.ids.length I.raw) (fun q hq=>Nat.le_of_lt (hgood q hq).1) _ st _ rs hproc
  have htags := ProcActualBucketGuards.process_tags I.ids.length I.allowed _ _ st _ rs hproc
  have hb := ProcBucketSize.process_bounds I.ids.length I.allowed _ hgood _ st _ rs
    (ProcActualInput.prepared_ready sp hs prev) hproc
  have hraw := (ProcPreparedSequence.input_bounds sp prev hs).2.2
  change I.raw.length≤4096 at hraw
  have hc : (convRaw I.p I.ids.length I.raw).length≤I.raw.length := List.length_filterMap_le _ _
  have hsize : ∀rd∈rs,1≤rd.bucket.length ∧ rd.bucket.length<16384 := by
    intro rd hr
    have hh := hb rd hr
    omega
  rw [hreq] at hv
  have hz : ∀rd∈rs,rd.key≠0 → rd.z=0 := by
    intro rd hr hk
    have hh := ProcActualModelValid.process_valid I.ids.length I.allowed _ _ st _ rs hproc rd hr
    simpa [ProcActualModelValid.Valid,hk] using hh
  obtain ⟨out,ho,he,hco,hpo⟩ := trace_push I cv hcv (NearSpecV3.leWords sp.seed)
    (ProcActualInput.initial I) cv.size rs st last ht (ProcActualAllowanceShape.initial_shape I)
    (fun rd hr => (hv rd hr).2) hsize htags hz s hclock ha
  exact ⟨out,last,ho,he,hco,hpo⟩
theorem replay_push (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (cv : Array CReq) (st : PState) (rs : List Round)
    (hcv : forIn (ProcPreparedSequence.input sp prev).raw #[]
      (ProcActualConverted.step (ProcPreparedSequence.input sp prev))=.ok cv)
    (hproc : ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs)) :
    ∃out last,ProcActualReplayFactor.replay (ProcPreparedSequence.input sp prev) cv rs=.ok out ∧
      Aligned (NearSpecV3.leWords sp.seed) cv out st last ∧ ProcActualReplayClock.Clock out ∧
      (ProcActualGeneratedPush.pushes (entryAcc out)).toList=
        cv.toList.map (fun c=>(c.cid,c.key,if c.key=0 then 1 else 0,c.cid*64))++
          (ProcPushConservation.generated rs).map (ProcPushConservation.stamp cv.size) ∧
      (ProcActualPoppedLog.buckets out).toList=
        (ProcPushConservation.popped rs).map (ProcPushConservation.stamp cv.size) := by
  let I := ProcPreparedSequence.input sp prev
  let lp := linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev)
  obtain ⟨ops,hop⟩ := ProcActualReplayTotal.reads_array lp.a2 lp.g2 cv
    (Array.replicate (I.ids.length*I.ids.length) #[])
  obtain ⟨out,last,ho,ha,hc,hp⟩ := prepared_push sp hs prev cv st rs hcv hproc
    (ProcActualReplayInitial.initial I cv ops) (ProcActualReplayClock.initial_clock I cv ops)
    (ProcActualReplayInitial.initial_aligned I cv ops)
  have hr : ProcActualReplayFactor.replay I cv rs=.ok out := by
    change (forIn cv _ (ProcActualReplayFactor.readStep lp.a2 lp.g2) >>= fun ops =>
      forIn rs (ProcActualReplayInitial.initial I cv ops) (step I cv (NearSpecV3.leWords sp.seed)))=.ok out
    rw [hop]
    exact ho
  refine ⟨out,last,hr,ha,hc,?_,?_⟩
  · simpa [ProcActualReplayInitial.initial,entryAcc,ProcActualGeneratedPush.pushes] using hp
  · exact ProcActualPoppedLog.replay_buckets I cv rs out
      (ProcActualBucketGuards.process_tags I.ids.length I.allowed _ _ st _ rs hproc) hr

end ZkFormal.NearV3.Candidates.ProcActualTracePush
