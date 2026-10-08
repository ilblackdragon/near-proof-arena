import ZkFormal.NearV3.Candidates.ProcActualReplayRound
namespace ZkFormal.NearV3.Candidates.ProcActualRoundTransition
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcActualReplayRound

def Aligned (key : List Nat) (cv : Array CReq) (s : Acc) (st : PState) (t : Nat) : Prop :=
  ProcActualReplayEntry.state (entryAcc s) (ZkFormal.Chacha.rngAt key (position s))=st ∧
  cv.size+ProcActualEntryTransition.cursor (entryAcc s)=t

theorem round_transition (I : Input) (cv : Array CReq)
    (hcv : forIn I.raw #[] (ProcActualConverted.step I)=.ok cv)
    (key : List Nat) (rd : Round) (s : Acc) (st' : PState) (t' : Nat)
    (hs : ProcActualAllowanceShape.Shape I.ids.length
      (ProcActualReplayEntry.state (entryAcc s) (ZkFormal.Chacha.rngAt key (position s))))
    (hv : ∀v∈rd.shuffled,ProcRequestPointers.Valid (ProcActualConversionExact.view cv) v)
    (hsize : 1≤rd.bucket.length ∧ rd.bucket.length<16384)
    (htags : ProcActualBucketGuards.Tagged rd)
    (hb : ProcModelBatchTrace.Batch I.ids.length I.allowed (ProcActualConversionExact.view cv)
      (ProcActualReplayEntry.state (entryAcc s) (ZkFormal.Chacha.rngAt key (position s)))
      (cv.size+ProcActualEntryTransition.cursor (entryAcc s)) rd st' t') :
    ∃out,step I cv key rd s=.ok (.yield out) ∧ Aligned key cv out st' t' := by
  have hcount := batch_count _ _ _ _ _ _ _ _ hb
  obtain ⟨last,next,hshuffle,hentry,hstate,hclock,hcursor,hentries,hrng⟩ :=
    ProcActualBatchReplay.batch_replay I cv hcv key (position s) (time s) (entryAcc s) rd st' t' hs hv hb
  rcases s with ⟨sb,rb,aa,gg,opsL,opsS,opsR,pushes,bucketsAll,T,kpos,Kq,zq,used,rounds,gidx⟩
  obtain ⟨collected,hcollect,_⟩ := ProcActualBucketGuards.collect_success cv.size rd.key rd.z rd.bucket bucketsAll htags
  dsimp only [position,time,entryAcc] at hshuffle hentry
  unfold step
  change ∃out : Acc,(do
    check (rd.bucket.length≥1 && rd.bucket.length<16384) "bucket size"
    let (sh,kend) ← replayShuffle key kpos (rd.bucket.map (fun b : Push=>b.v))
    check (sh==rd.shuffled) "shuffle replay differs"
    check (rd.steps.length==rd.bucket.length) "steps ≠ bucket"
    let collected ← forIn rd.bucket bucketsAll (ProcActualBucketGuards.collectStep cv.size rd.key rd.z)
    let result ← forIn (List.range rd.bucket.length)
      (sb,rb,aa,gg,opsL,opsS,opsR,pushes,used,gidx,#[])
      (ProcActualReplayEntry.step I cv rd sh T)
    pure (ForInStep.yield (result.1,result.2.1,result.2.2.1,result.2.2.2.1,
      result.2.2.2.2.1,result.2.2.2.2.2.1,result.2.2.2.2.2.2.1,result.2.2.2.2.2.2.2.1,
      collected,T+rd.bucket.length,kend,rd.key,rd.z,result.2.2.2.2.2.2.2.2.1,
      rounds.push ⟨rd.key,rd.z,T,rd.bucket.length,kpos,kend,Kq,zq,result.2.2.2.2.2.2.2.2.2.2.toList⟩,
      result.2.2.2.2.2.2.2.2.2.1)))=.ok (.yield out) ∧ Aligned key cv out st' t'
  simp only [hshuffle,hcount,hcollect,hentry,check,hsize.1,hsize.2,decide_true,
    Bool.and_true,BEq.rfl,ite_true,bind,Except.bind,pure,Except.pure]
  exact ⟨_,rfl,hstate,hclock.symm⟩

theorem batch_shape (n : Nat) (allowed : Array Bool) (reqs : List NearSpecV3.Scheduler.Req)
    (st st' : PState) (t t' : Nat) (rd : Round)
    (hs : ProcActualAllowanceShape.Shape n st)
    (hb : ProcModelBatchTrace.Batch n allowed reqs st t rd st' t') :
    ProcActualAllowanceShape.Shape n st' := by
  obtain ⟨rng,pending,out,hshuffle,hmodel,hsteps,hstate,htime,hstart⟩ := hb
  rw [hstate]
  exact ProcActualAllowanceShape.entries_shape n allowed reqs rd.key rd.z rd.shuffled _ out hs hmodel

theorem trace_shape (n : Nat) (allowed : Array Bool) (reqs : List NearSpecV3.Scheduler.Req)
    (initial : PState) (start : Nat) (rs : List Round) (st : PState) (t : Nat)
    (hs : ProcActualAllowanceShape.Shape n initial)
    (ht : ProcModelBatchTrace.Trace n allowed reqs initial start rs st t) :
    ProcActualAllowanceShape.Shape n st := by
  induction ht with
  | nil => exact hs
  | snoc ht rd st' t' hb ih => exact batch_shape n allowed reqs _ st' _ t' rd ih hb

set_option maxHeartbeats 800000 in
theorem step_yields (I : Input) (cv : Array CReq) (key : List Nat) (rd : Round)
    (s : Acc) (out : ForInStep Acc) (h : step I cv key rd s=.ok out) :
    ∃next,out=.yield next := by
  unfold step at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals exact ⟨_,rfl⟩

theorem append_ok {α β : Type} (f : α → β → Except String (ForInStep β))
    (hf : ∀x s out,f x s=.ok out → ∃next,out=.yield next)
    (xs ys : List α) (s mid out : β)
    (hx : forIn xs s f=.ok mid) (hy : forIn ys mid f=.ok out) :
    forIn (xs++ys) s f=.ok out := by
  induction xs generalizing s with
  | nil => simp only [List.forIn_nil] at hx; cases hx; exact hy
  | cons x xs ih =>
    rw [List.forIn_cons] at hx
    cases he : f x s with
    | error e => simp only [he,bind,Except.bind] at hx; cases hx
    | ok next =>
      obtain ⟨next,rfl⟩ := hf x s next he
      simp only [he,bind,Except.bind] at hx
      simpa only [List.cons_append,List.forIn_cons,he,bind,Except.bind] using ih next hx

/-- The entire actual outer round loop succeeds and stays aligned with the
ordered model trace. Final post-loop checks remain separate. -/
theorem trace_replay (I : Input) (cv : Array CReq)
    (hcv : forIn I.raw #[] (ProcActualConverted.step I)=.ok cv)
    (key : List Nat) (initial : PState) (start : Nat) (rs : List Round) (st : PState) (t : Nat)
    (ht : ProcModelBatchTrace.Trace I.ids.length I.allowed (ProcActualConversionExact.view cv)
      initial start rs st t)
    (hs : ProcActualAllowanceShape.Shape I.ids.length initial)
    (hv : ∀rd∈rs,∀v∈rd.shuffled,ProcRequestPointers.Valid (ProcActualConversionExact.view cv) v)
    (hsize : ∀rd∈rs,1≤rd.bucket.length ∧ rd.bucket.length<16384)
    (htags : ∀rd∈rs,ProcActualBucketGuards.Tagged rd)
    (s : Acc) (ha : Aligned key cv s initial start) :
    ∃out,forIn rs s (step I cv key)=.ok out ∧ Aligned key cv out st t := by
  induction ht with
  | nil => exact ⟨s,rfl,ha⟩
  | @snoc rs st t ht rd st' t' hb ih =>
    obtain ⟨mid,hm,ham⟩ := ih (fun r hr=>hv r (by simp [hr]))
      (fun r hr=>hsize r (by simp [hr])) (fun r hr=>htags r (by simp [hr]))
    have hmshape := trace_shape I.ids.length I.allowed (ProcActualConversionExact.view cv)
      initial start rs st t hs ht
    have hb' := hb
    rw [←ham.1,←ham.2] at hb'
    have hms : ProcActualAllowanceShape.Shape I.ids.length
        (ProcActualReplayEntry.state (entryAcc mid) (ZkFormal.Chacha.rngAt key (position mid))) := by
      rw [ham.1]; exact hmshape
    obtain ⟨out,ho,hao⟩ := round_transition I cv hcv key rd mid st' t' hms
      (hv rd (by simp)) (hsize rd (by simp)) (htags rd (by simp)) hb'
    refine ⟨out,?_,hao⟩
    exact append_ok (step I cv key) (step_yields I cv key) rs [rd] s mid out hm
      (by simp only [List.forIn_cons,ho,bind,Except.bind,List.forIn_nil,pure,Except.pure])

end ZkFormal.NearV3.Candidates.ProcActualRoundTransition
