import ZkFormal.NearV3.Candidates.ProcReplayTimestampBounds
import ZkFormal.NearV3.Candidates.ProcActualReplayClock
import ZkFormal.NearV3.Candidates.ProcActualReplayTimeEnvelope
namespace ZkFormal.NearV3.Candidates.ProcReplayTimestampActual
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcActualReplayRound

theorem round_time (I : Input) (cv : Array CReq) (key : List Nat) (rd : Round)
    (s out : Acc) (h:step I cv key rd s=.ok (.yield out)) : time out=time s+rd.bucket.length := by
  unfold step at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals rfl

theorem loop_time (I : Input) (cv : Array CReq) (key : List Nat) (rs : List Round)
    (s out : Acc) (h:forIn rs s (step I cv key)=.ok out) :
    time out=time s+(rs.map (fun r=>r.bucket.length)).sum := by
  induction rs generalizing s with
  | nil => simp only [List.forIn_nil] at h; cases h; simp
  | cons rd rs ih =>
    rw [List.forIn_cons] at h
    cases he:step I cv key rd s with
    | error e => simp only [he,bind,Except.bind] at h; cases h
    | ok next =>
      obtain ⟨next,rfl⟩:=ProcActualRoundTransition.step_yields I cv key rd s next he
      simp only [he,bind,Except.bind] at h
      rw [ih next h,round_time I cv key rd s next he]
      simp [Nat.add_assoc]

theorem replay_time (I : Input) (cv : Array CReq) (rs : List Round) (out : Acc)
    (h:ProcActualReplayFactor.replay I cv rs=.ok out) :
    time out=T0+(rs.map (fun r=>r.bucket.length)).sum := by
  let lp:=linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev)
  obtain ⟨ops,hop⟩:=ProcActualReplayTotal.reads_array lp.a2 lp.g2 cv
    (Array.replicate (I.ids.length*I.ids.length) #[])
  change (forIn cv _ (ProcActualReplayFactor.readStep lp.a2 lp.g2) >>= fun ops =>
    forIn rs (ProcActualReplayInitial.initial I cv ops) (step I cv (NearSpecV3.leWords I.seed)))=.ok out at h
  rw [hop] at h
  exact loop_time I cv _ rs _ out h

theorem bucket_sum (rs : List Round) (h:∀rd∈rs,rd.steps.length=rd.bucket.length) :
    (rs.map (fun r=>r.bucket.length)).sum=(rs.flatMap Round.steps).length := by
  induction rs with
  | nil => rfl
  | cons rd rs ih =>
    simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.length_append]
    rw [←h rd (by simp),ih (fun rd hr=>h rd (by simp [hr]))]

theorem replay_bound (I : Input) (cv : Array CReq) (rs : List Round) (out : Acc)
    (hc:forIn I.raw #[] (ProcActualConverted.step I)=.ok cv) (hb:I.raw.length≤4096)
    (st0 st : PState) (fuel : Nat)
    (hm:processEv I.ids.length I.allowed (ProcActualConversionExact.view cv) st0 fuel=.ok (st,rs))
    (hr:ProcActualReplayFactor.replay I cv rs=.ok out) :
    time out≤1310720 ∧ 2*time out+1<2^29 := by
  have hv:=ProcActualConversionExact.loop_view I I.raw #[] cv hc
  simp only [ProcActualConversionExact.view,Array.toList_empty,List.map_nil,List.nil_append] at hv
  have hs:ProcRequestPointers.Small (ProcActualConversionExact.view cv) := by
    change ProcRequestPointers.Small (cv.toList.map _) 
    rw [hv]
    exact ProcConvertedPointers.convRaw_small _ _ _
  have hcount:(ProcActualConversionExact.view cv).length≤4096 := by
    change (cv.toList.map _).length≤4096
    rw [hv]
    exact Nat.le_trans (ProcReplayTimestampBounds.convRaw_count _ _ _) hb
  have he:=ProcReplayTimestampRounds.process_entries_bound _ _ _ hs st0 st fuel rs hm
  have ht:=replay_time I cv rs out hr
  rw [bucket_sum rs (ProcModelClock.process_clock _ _ _ _ _ _ _ hm).2] at ht
  unfold T0 at ht
  omega
theorem prepared_replay_bound (sp : NearSpecV3.Scheduler.SchedPub) (hs:SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (cv : Array CReq) (rs : List Round) (out : Acc)
    (hc:forIn (ProcPreparedSequence.input sp prev).raw #[]
      (ProcActualConverted.step (ProcPreparedSequence.input sp prev))=.ok cv)
    (st0 st : PState) (fuel : Nat)
    (hm:processEv sp.ids.length sp.allowed (ProcActualConversionExact.view cv) st0 fuel=.ok (st,rs))
    (hr:ProcActualReplayFactor.replay (ProcPreparedSequence.input sp prev) cv rs=.ok out) :
    time out≤1310720 ∧ 2*time out+1<2^29 ∧
    ∀rd∈(ProcActualReplayKeyTrace.rounds out).toList,rd.T<2^29 := by
  have hb:=replay_bound (ProcPreparedSequence.input sp prev) cv rs out hc
    (ProcPreparedSequence.input_bounds sp prev hs).2.2 st0 st fuel hm hr
  refine ⟨hb.1,hb.2,?_⟩
  exact ProcActualReplayTimeEnvelope.replay_round_times (2^29) _ _ _ _ hr (by omega)

end ZkFormal.NearV3.Candidates.ProcReplayTimestampActual
