import ZkFormal.NearV3.Candidates.ProcActualBucketGuards
namespace ZkFormal.NearV3.Candidates.ProcBucketSize
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler

theorem pending_length (reqs : List Req) (s : ProcModelStep.Acc)
    (hs : ProcRoundSuccess.Ready reqs s) : s.1.length≤reqs.length := by
  have h := length_le_of_nodup_subset (s.1.map (fun p=>ProcPendingCurrent.link reqs p.v))
    (reqs.map (·.link)) hs.2.1 (by
      intro l hl
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hl
      have hv := (hs.2.2.1 p hp).1
      unfold ProcPendingCurrent.link
      rw [List.getElem!_toArray,getElem!_pos reqs _ hv]
      exact List.mem_map_of_mem (List.getElem_mem hv))
  simpa using h

theorem bucket_length (reqs : List Req) (s : ProcModelStep.Acc)
    (hs : ProcRoundSuccess.Ready reqs s) (hn : s.1≠[]) :
    0<(sortTs (s.1.filter (fun p=>p.key==ProcMaxBucket.maxKey s.1))).length ∧
    (sortTs (s.1.filter (fun p=>p.key==ProcMaxBucket.maxKey s.1))).length≤reqs.length := by
  have hp := ProcPushPerm.sort_perm (s.1.filter (fun p=>p.key==ProcMaxBucket.maxKey s.1))
  obtain ⟨p,hmem,hkey⟩ := ProcMaxBucket.max_mem s.1 hn
  have hmem' : p∈sortTs (s.1.filter (fun p=>p.key==ProcMaxBucket.maxKey s.1)) :=
    hp.mem_iff.mpr (List.mem_filter.mpr ⟨hmem,by simpa using hkey⟩)
  exact ⟨List.length_pos_of_mem hmem',by rw [hp.length_eq]; exact Nat.le_trans (List.length_filter_le _ _) (pending_length reqs s hs)⟩
private theorem throw_eq {α : Type} (e : String) : (throw e : Except String α)=.error e := rfl

set_option maxHeartbeats 800000 in
theorem step_ready (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (hr : ProcPoppedSuccess.GoodRequests reqs) (i : Nat) (s : ProcModelStep.Acc)
    (hs : ProcRoundSuccess.Ready reqs s) (out : ForInStep ProcModelStep.Acc)
    (h : ProcModelStep.step n allowed reqs i s=.ok out) :
    ExceptLoop.StepInv (ProcRoundSuccess.Ready reqs) out := by
  by_cases hn : s.1=[]
  · simp [ProcModelStep.step,hn,pure,Except.pure] at h
    subst out
    exact hs
  · cases hsh : NearSpecV3.shuffle
        ((sortTs (s.1.filter (fun p=>p.key==ProcMaxBucket.maxKey s.1))).map (·.v)) s.2.1.rng with
    | none =>
      unfold ProcModelStep.step at h
      simp only [ProcMaxBucket.maxKey] at hsh
      simp only [hsh,bind,Except.bind,pure,Except.pure,throw_eq] at h
      repeat first | cases h | split at h
      all_goals repeat first | cases h | split at h
      all_goals simp_all
    | some pair =>
      rcases pair with ⟨sh,rng⟩
      obtain ⟨next,he,hnext⟩ := ProcRoundSuccess.step_success n allowed reqs hr i s hs hn sh rng hsh
      rw [he] at h
      cases h
      exact hnext

def Inv (reqs : List Req) (s : ProcModelStep.Acc) : Prop :=
  ProcRoundSuccess.Ready reqs s ∧
  ∀rd∈s.2.2.2.1,0<rd.bucket.length ∧ rd.bucket.length≤reqs.length

set_option maxHeartbeats 1000000 in
theorem step_inv (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (hr : ProcPoppedSuccess.GoodRequests reqs) (i : Nat) (s : ProcModelStep.Acc)
    (hs : Inv reqs s) (out : ForInStep ProcModelStep.Acc)
    (h : ProcModelStep.step n allowed reqs i s=.ok out) :
    ExceptLoop.StepInv (Inv reqs) out := by
  have hready := step_ready n allowed reqs hr i s hs.1 out h
  unfold ProcModelStep.step at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals
    refine ⟨hready,?_⟩
    first
    | exact hs.2
    | simp only [List.mem_append,List.mem_singleton]
      intro rd hrd
      rcases hrd with hrd|rfl
      · exact hs.2 rd hrd
      · apply bucket_length reqs s hs.1
        have hh : s.1.isEmpty≠true := by assumption
        simpa using hh

set_option maxHeartbeats 400000 in
theorem process_bounds (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (hr : ProcPoppedSuccess.GoodRequests reqs) (st0 st : PState) (fuel : Nat)
    (rs : List Round) (hready : ProcRoundSuccess.Ready reqs (ProcModelStep.initial reqs st0))
    (h : processEv n allowed reqs st0 fuel=.ok (st,rs)) :
    ∀rd∈rs,0<rd.bucket.length ∧ rd.bucket.length≤reqs.length := by
  rw [ProcModelStep.process_eq] at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals
    have hi : Inv reqs ?out := by
      refine ExceptLoop.invariant (α := Nat) (ε := String) ?xs ?f (Inv reqs) ?step ?b _ ?init ?loop
      case loop => assumption
      case init => exact ⟨hready,by simp [ProcModelStep.initial]⟩
      case step => exact fun i _ s hs out h=>step_inv n allowed reqs hr i s hs out h
    exact hi.2

/-- Actual prepared processing discharges the replay bucket-size guard. -/
theorem prepared_guard (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (st : PState) (rs : List Round)
    (h : ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs)) :
    ∀rd∈rs,rd.bucket.length≤4096 ∧
      Gen.check (rd.bucket.length≥1 && rd.bucket.length<16384) "bucket size"=.ok () := by
  let I := ProcPreparedSequence.input sp prev
  have hb := process_bounds I.ids.length I.allowed (convRaw I.p I.ids.length I.raw)
    (ProcPreparedRequestGood.converted_good _ _ _ hs.params) _ st _ rs
    (ProcActualInput.prepared_ready sp hs prev) h
  have hc : (convRaw I.p I.ids.length I.raw).length≤I.raw.length := List.length_filterMap_le _ _
  have hi := (ProcPreparedSequence.input_bounds sp prev hs).2.2
  change I.raw.length≤4096 at hi
  intro rd hrd
  have hr := hb rd hrd
  have hsize : rd.bucket.length≤4096 := by omega
  exact ⟨hsize,by
    have hp : 1≤rd.bucket.length := hr.1
    have hl : rd.bucket.length<16384 := by omega
    simp [Gen.check,hp,hl,pure,Except.pure]⟩

end ZkFormal.NearV3.Candidates.ProcBucketSize
