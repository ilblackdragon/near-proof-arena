import ZkFormal.NearV3.Candidates.ProcActualPoppedLog
namespace ZkFormal.NearV3.Candidates.ProcActualGeneratedPush
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcActualReplayEntry

def pushes (s : Acc) : Array (Nat×Nat×Nat×Nat) := s.2.2.2.2.2.2.2.1

theorem stamp_event (R T x K z : Nat) (e : Step)
    (ht : e.t=R+x) (hT : T=T0+x) (hz : K≠0 → z=0) :
    (ProcPushEntries.pushOf K z e).map (ProcPushConservation.stamp R)=
      (if e.ok && !e.last then [(T,e.aOut,if e.aOut=0 then z+1 else 0,e.v+1)] else []) := by
  have hc : (if K=0 then z+1 else 1)=z+1 := by
    split
    · rfl
    · rw [hz (by assumption)]
  simp [ProcPushEntries.pushOf,ht,hT,hc]
  split <;> simp_all [ProcPushConservation.stamp] <;> omega

/-- A successful actual entry appends exactly the corresponding model push,
provided its replay timestamp and zero-key ordinal are aligned. -/
theorem step_push (I : Input) (cv : Array CReq) (rd : Round) (sh : List Nat)
    (T x : Nat) (s out : Acc) (rng : NearSpecV3.Rng)
    (he : rd.steps[x]! =ProcModelEvent.replayEvent I.allowed cv[sh[x]!/64]! sh[x]!
      (cv.size+ProcActualEntryTransition.cursor s) (state s rng))
    (hT : T+x=T0+ProcActualEntryTransition.cursor s)
    (hz : rd.key≠0 → rd.z=0)
    (h : step I cv rd sh T x s=.ok (.yield out)) :
    (pushes out).toList=(pushes s).toList++
      (ProcPushEntries.pushOf rd.key rd.z rd.steps[x]!).map (ProcPushConservation.stamp cv.size) := by
  have ht : rd.steps[x]!.t=cv.size+ProcActualEntryTransition.cursor s := by rw [he]; rfl
  rw [stamp_event cv.size (T+x) (ProcActualEntryTransition.cursor s) rd.key rd.z _ ht hT hz]
  rcases s with ⟨sb,rb,aa,gg,ol,os,orr,ps,used,gi,es⟩
  dsimp only [ProcModelEvent.replayEvent,state,ProcActualEntryTransition.cursor] at he
  rw [he]
  unfold step at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals rename_i hp
  all_goals simpa [pushes,and_assoc] using hp
theorem loop_push (I : Input) (cv : Array CReq) (rd : Round) (sh : List Nat)
    (T start len : Nat) (s out : Acc) (rng : NearSpecV3.Rng)
    (he : (List.range' start len).map (fun x=>rd.steps[x]!)=
      ProcActualStateReplay.events I cv ((List.range' start len).map (fun x=>sh[x]!))
        (cv.size+ProcActualEntryTransition.cursor s) (state s rng))
    (hT : T+start=T0+ProcActualEntryTransition.cursor s)
    (hz : rd.key≠0 → rd.z=0)
    (h : forIn (List.range' start len) s (step I cv rd sh T)=.ok out) :
    (pushes out).toList=(pushes s).toList++
      ((List.range' start len).flatMap (fun x=>ProcPushEntries.pushOf rd.key rd.z rd.steps[x]!)).map
        (ProcPushConservation.stamp cv.size) := by
  induction len generalizing start s with
  | zero => simp only [List.range'_zero,List.forIn_nil] at h; cases h; simp
  | succ len ih =>
    simp only [List.range'_succ,List.map_cons,ProcActualStateReplay.events,List.cons.injEq] at he
    rw [List.range'_succ,List.forIn_cons] at h
    cases hs : step I cv rd sh T start s with
    | error e => simp only [hs,bind,Except.bind] at h; cases h
    | ok next =>
      obtain ⟨next,rfl,hstate,hcursor,_⟩ :=
        ProcActualEntryTransition.step_effect I cv rd sh T start s next rng hs
      simp only [hs,bind,Except.bind] at h
      have hp := step_push I cv rd sh T start s next rng he.1 hT hz hs
      have he' : (List.range' (start+1) len).map (fun x=>rd.steps[x]!)=
          ProcActualStateReplay.events I cv ((List.range' (start+1) len).map (fun x=>sh[x]!))
            (cv.size+ProcActualEntryTransition.cursor next) (state next rng) := by
        rw [hstate,hcursor]
        simpa only [Nat.add_assoc] using he.2
      have ht' : T+(start+1)=T0+ProcActualEntryTransition.cursor next := by omega
      have hh := ih (start+1) next he' ht' h
      rw [hp] at hh
      simpa only [List.range'_succ,List.flatMap_cons,List.map_append,List.append_assoc] using hh

open ProcActualEntryTransition in
theorem model_batch_push (I : Input) (cv : Array CReq)
    (hcv : forIn I.raw #[] (ProcActualConverted.step I)=.ok cv)
    (rd : Round) (sh : List Nat) (T : Nat) (s out : Acc) (rng : NearSpecV3.Rng)
    (pending : List Push) (modelOut : ProcModelStep.EntryAcc)
    (hv : ∀v∈sh,ProcRequestPointers.Valid (ProcActualConversionExact.view cv) v)
    (hs : ProcActualAllowanceShape.Shape I.ids.length (state s rng))
    (hmodel : forIn sh (pending,state s rng,cv.size+cursor s,[])
      (ProcModelStep.entryStep I.ids.length I.allowed (ProcActualConversionExact.view cv) rd.key rd.z)=.ok modelOut)
    (hsteps : rd.steps=modelOut.2.2.2) (hlen : rd.bucket.length=sh.length)
    (hT : T=T0+cursor s) (hz : rd.key≠0 → rd.z=0)
    (h : forIn (List.range rd.bucket.length) s (step I cv rd sh T)=.ok out) :
    (pushes out).toList=(pushes s).toList++
      (ProcPushEntries.pushes rd.key rd.z rd.steps).map (ProcPushConservation.stamp cv.size) := by
  have he := ProcActualStateReplay.entries_events I cv hcv rd.key rd.z sh
    (pending,state s rng,cv.size+cursor s,[]) modelOut hv hs hmodel
  simp only [List.nil_append] at he
  have hslen : rd.steps.length=sh.length := by rw [hsteps,he,events_length]
  have hindices : (List.range rd.bucket.length).map (fun x=>sh[x]!)=sh := by rw [hlen,map_indices]
  have hevents : (List.range rd.bucket.length).map (fun x=>rd.steps[x]!)=
      ProcActualStateReplay.events I cv ((List.range rd.bucket.length).map (fun x=>sh[x]!))
        (cv.size+cursor s) (state s rng) := by
    rw [hindices,hlen,←hslen,map_indices,hsteps,he]
  have he' : (List.range' 0 rd.bucket.length).map (fun x=>rd.steps[x]!)=
      ProcActualStateReplay.events I cv ((List.range' 0 rd.bucket.length).map (fun x=>sh[x]!))
        (cv.size+cursor s) (state s rng) := by simpa only [List.range_eq_range'] using hevents
  have hh := loop_push I cv rd sh T 0 rd.bucket.length s out rng he' (by simpa using hT) hz (by simpa only [List.range_eq_range'] using h)
  have hf : (List.range' 0 rd.bucket.length).flatMap
      (fun x=>ProcPushEntries.pushOf rd.key rd.z rd.steps[x]!)=
        ProcPushEntries.pushes rd.key rd.z rd.steps := by
    have hi : (List.range' 0 rd.bucket.length).map (fun x=>rd.steps[x]!)=rd.steps := by
      simpa only [List.range_eq_range',hlen,←hslen] using map_indices rd.steps
    rw [←List.flatMap_map,hi]
    rfl
  rw [hf] at hh
  exact hh

end ZkFormal.NearV3.Candidates.ProcActualGeneratedPush
