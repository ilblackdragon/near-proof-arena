import ZkFormal.NearV3.Candidates.ProcPushEntries
namespace ZkFormal.NearV3.Candidates.ProcPushConservation
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler
private theorem throw_eq {α : Type} (e : String) : (throw e : Except String α)=.error e := rfl

def generated (rs : List Round) : List Push := rs.flatMap (fun r=>ProcPushEntries.pushes r.key r.z r.steps)
def popped (rs : List Round) : List Push := rs.flatMap Round.bucket

def Inv (initial : List Push) (s : ProcModelStep.Acc) : Prop := ∀p : Push,
  initial.count p+(generated s.2.2.2.1).count p=s.1.count p+(popped s.2.2.2.1).count p

set_option maxHeartbeats 800000 in
theorem step_inv (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (initial : List Push) (i : Nat) (s : ProcModelStep.Acc) (hs : Inv initial s)
    (out : ForInStep ProcModelStep.Acc) (h : ProcModelStep.step n allowed reqs i s=.ok out) :
    ExceptLoop.StepInv (Inv initial) out := by
  let K := s.1.foldl (fun m p=>Nat.max m p.key) 0
  unfold ProcModelStep.step at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals first
    | exact hs
    | rename_i sh rng hsh unused entryOut hentry
      have hn := ProcPushEntries.entries_pushes n allowed reqs _ _ _ _ _ _ _ hentry
      intro p
      have hp := (ProcPushPerm.pop_perm s.1 K).count_eq p
      have hb := hs p
      simp only [ExceptLoop.StepInv,Inv,generated,popped,List.flatMap_append,List.flatMap_cons,
        List.flatMap_nil,List.append_nil,List.count_append] at hb ⊢
      rw [hn]
      simp only [List.count_append,K] at hp ⊢
      omega

theorem end_zero (ps : List Push) (h : (!ps.isEmpty)≠true) : ps=[] := by
  cases ps <;> simp_all

set_option maxHeartbeats 400000 in
theorem process_balance (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (st0 st : PState) (fuel : Nat) (rs : List Round)
    (h : processEv n allowed reqs st0 fuel=.ok (st,rs)) :
    ∀p : Push,((ProcModelStep.initial reqs st0).1++generated rs).count p=(popped rs).count p := by
  rw [ProcModelStep.process_eq] at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals
    have hh : Inv (ProcModelStep.initial reqs st0).1 ?out := by
      refine ExceptLoop.invariant (α := Nat) (ε := String) ?xs ?f
        (Inv (ProcModelStep.initial reqs st0).1) ?step ?b _ ?init ?loop
      case loop => assumption
      case init => simp [Inv,generated,popped,ProcModelStep.initial]
      case step => exact fun i _ s hs out h=>step_inv n allowed reqs _ i s hs out h
    have hz := end_zero _ (by assumption)
    intro p
    have hp := hh p
    rw [hz] at hp
    simpa only [List.count_append,List.count_nil,Nat.zero_add] using hp

theorem process_perm (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (st0 st : PState) (fuel : Nat) (rs : List Round)
    (h : processEv n allowed reqs st0 fuel=.ok (st,rs)) :
    ((ProcModelStep.initial reqs st0).1++generated rs).Perm (popped rs) :=
  List.perm_iff_count.mpr (process_balance n allowed reqs st0 st fuel rs h)

def stamp (R : Nat) (p : Push) : Nat×Nat×Nat×Nat :=
  (if p.ts<R then p.ts else T0+(p.ts-R),p.key,p.z,p.v)

/-- The actual event model accounts for every push once, including the
renderer time-stamp translation. This proves the multiset, not qsort's contract. -/
theorem process_log_perm (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (st0 st : PState) (fuel : Nat) (rs : List Round)
    (h : processEv n allowed reqs st0 fuel=.ok (st,rs)) :
    (((ProcModelStep.initial reqs st0).1++generated rs).map (stamp reqs.length)).Perm
      ((popped rs).map (stamp reqs.length)) :=
  (process_perm n allowed reqs st0 st fuel rs h).map (stamp reqs.length)
end ZkFormal.NearV3.Candidates.ProcPushConservation
