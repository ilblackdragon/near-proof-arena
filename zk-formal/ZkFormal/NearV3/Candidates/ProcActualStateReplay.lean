import ZkFormal.NearV3.Candidates.ProcActualEntryAgreement
namespace ZkFormal.NearV3.Candidates.ProcActualStateReplay
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

def stateStep (I : Input) (cv : Array CReq) (st : PState) (v : Nat) : PState :=
  let c := cv[v/64]!
  ProcGrantAgreement.replayGrant I.allowed c.s c.r c.link c.incs[v%64]! st

/-- Actual converted coordinates make the generator's unconditional writes equal
the model's conditional grant, including denied requests. -/
theorem selected_grant (I : Input) (cv : Array CReq)
    (hcv : forIn I.raw #[] (ProcActualConverted.step I)=.ok cv)
    (v : Nat) (st : PState)
    (hv : ProcRequestPointers.Valid (ProcActualConversionExact.view cv) v) :
    ProcGrantAgreement.modelGrant I.ids.length I.allowed
      (ProcActualConversionExact.view cv).toArray[v/64]!.link
      ((ProcActualConversionExact.view cv).toArray[v/64]!.incs.getD (v%64) 0) st=
      stateStep I cv st v := by
  obtain ⟨hi,hj⟩ := ProcActualIndexGuards.view_bounds cv v hv
  have hm : cv[v/64]!∈cv.toList := by
    rw [getElem!_pos cv _ hi]
    exact Array.getElem_mem_toList hi
  have hf := ProcActualCoordinates.loop_facts I cv hcv _ hm
  have hq : (ProcActualConversionExact.view cv).toArray[v/64]! =
      NearSpecV3.Scheduler.Req.mk cv[v/64]!.link cv[v/64]!.incs := by
    simp [ProcActualConversionExact.view,hi]
  rw [hq]
  have hinc : cv[v/64]!.incs.getD (v%64) 0=cv[v/64]!.incs[v%64]! := by
    have he : ∀(xs : List Nat) (j : Nat),xs.getD j 0=xs[j]! := by
      intro xs j
      simp only [List.getD,getElem!_def]
      cases xs[j]? <;> rfl
    exact he _ _
  rw [hinc]
  exact ProcGrantAgreement.grant_eq _ _ _ _ _ _ _ hf.2.1 hf.2.2

/-- Whole successful model entry loops have exactly the replayed final state. -/
theorem entries_state (I : Input) (cv : Array CReq)
    (hcv : forIn I.raw #[] (ProcActualConverted.step I)=.ok cv)
    (K z : Nat) (vs : List Nat) (s out : ProcModelStep.EntryAcc)
    (hv : ∀v∈vs,ProcRequestPointers.Valid (ProcActualConversionExact.view cv) v)
    (h : forIn vs s (ProcModelStep.entryStep I.ids.length I.allowed
      (ProcActualConversionExact.view cv) K z)=.ok out) :
    out.2.1=vs.foldl (stateStep I cv) s.2.1 := by
  induction vs generalizing s with
  | nil => simp only [List.forIn_nil] at h; cases h; rfl
  | cons v vs ih =>
    rw [List.forIn_cons] at h
    cases he : ProcModelStep.entryStep I.ids.length I.allowed
        (ProcActualConversionExact.view cv) K z v s with
    | error e => simp only [he,bind,Except.bind] at h; cases h
    | ok next =>
      obtain ⟨next,rfl,ht,hlen⟩ := ProcModelEntryShape.entry_shape _ _ _ K z v s next he
      simp only [he,bind,Except.bind] at h
      have hg := ProcGrantAgreement.entry_grant _ _ _ K z v s _ he
      simp only [ExceptLoop.StepInv] at hg
      rw [selected_grant I cv hcv v s.2.1 (hv v (by simp))] at hg
      rw [ih next (fun v hm=>hv v (by simp [hm])) h,hg]
      rfl
def events (I : Input) (cv : Array CReq) : List Nat → Nat → PState → List Step
  | [],_,_ => []
  | v::vs,t,st => ProcModelEvent.replayEvent I.allowed cv[v/64]! v t st ::
      events I cv vs (t+1) (stateStep I cv st v)

/-- The entire model event list agrees with sequential replay, carrying the
updated state and clock between entries rather than assuming pointwise agreement. -/
theorem entries_events (I : Input) (cv : Array CReq)
    (hcv : forIn I.raw #[] (ProcActualConverted.step I)=.ok cv)
    (K z : Nat) (vs : List Nat) (s out : ProcModelStep.EntryAcc)
    (hv : ∀v∈vs,ProcRequestPointers.Valid (ProcActualConversionExact.view cv) v)
    (hs : ProcActualAllowanceShape.Shape I.ids.length s.2.1)
    (h : forIn vs s (ProcModelStep.entryStep I.ids.length I.allowed
      (ProcActualConversionExact.view cv) K z)=.ok out) :
    out.2.2.2=s.2.2.2++events I cv vs s.2.2.1 s.2.1 := by
  induction vs generalizing s with
  | nil => simp only [List.forIn_nil] at h; cases h; simp [events]
  | cons v vs ih =>
    rw [List.forIn_cons] at h
    cases he : ProcModelStep.entryStep I.ids.length I.allowed
        (ProcActualConversionExact.view cv) K z v s with
    | error e => simp only [he,bind,Except.bind] at h; cases h
    | ok next =>
      obtain ⟨next,rfl,ht,hlen⟩ := ProcModelEntryShape.entry_shape _ _ _ K z v s next he
      simp only [he,bind,Except.bind] at h
      have hag := ProcActualEntryAgreement.entry_agreement I cv hcv K z v s _ (hv v (by simp)) hs he
      simp only [ExceptLoop.StepInv] at hag
      have hg := ProcGrantAgreement.entry_grant _ _ _ K z v s _ he
      simp only [ExceptLoop.StepInv] at hg
      rw [selected_grant I cv hcv v s.2.1 (hv v (by simp))] at hg
      rw [ih next (fun v hm=>hv v (by simp [hm])) hag.1 h,hag.2,ht,hg]
      simp [events,List.append_assoc]

/-- Replaying the derived events passes every event-field and model-time check. -/
def verify (I : Input) (cv : Array CReq) : List Nat → List Step → Nat → PState → Except String PState
  | [],[],_,st => .ok st
  | v::vs,e::es,t,st => do
    check (e.t==t) "model time"
    ProcActualEntryAgreement.checkEvent I.allowed cv[v/64]! v st e
    verify I cv vs es (t+1) (stateStep I cv st v)
  | _,_,_,_ => .error "event length mismatch"

theorem verify_events (I : Input) (cv : Array CReq) (vs : List Nat) (t : Nat) (st : PState) :
    verify I cv vs (events I cv vs t st) t st=.ok (vs.foldl (stateStep I cv) st) := by
  induction vs generalizing t st with
  | nil => rfl
  | cons v vs ih =>
    have ht : (ProcModelEvent.replayEvent I.allowed cv[v/64]! v t st).t=t := rfl
    simp only [events,verify,ht,ProcActualEntryAgreement.check_event,
      BEq.rfl,check,ite_true,pure,Except.pure,bind,Except.bind,List.foldl_cons]
    exact ih _ _

/-- Successful model entry execution supplies a whole checked state replay.
This verifier covers time/event fields; memory logs and push accounting are separate. -/
theorem model_loop_verify (I : Input) (cv : Array CReq)
    (hcv : forIn I.raw #[] (ProcActualConverted.step I)=.ok cv)
    (K z : Nat) (vs : List Nat) (pending : List Push) (t : Nat) (st : PState)
    (out : ProcModelStep.EntryAcc)
    (hv : ∀v∈vs,ProcRequestPointers.Valid (ProcActualConversionExact.view cv) v)
    (hs : ProcActualAllowanceShape.Shape I.ids.length st)
    (h : forIn vs (pending,st,t,[]) (ProcModelStep.entryStep I.ids.length I.allowed
      (ProcActualConversionExact.view cv) K z)=.ok out) :
    verify I cv vs out.2.2.2 t st=.ok out.2.1 := by
  have he := entries_events I cv hcv K z vs (pending,st,t,[]) out hv hs h
  have hf := entries_state I cv hcv K z vs (pending,st,t,[]) out hv h
  simp only [List.nil_append] at he
  rw [he,verify_events,hf]

end ZkFormal.NearV3.Candidates.ProcActualStateReplay
