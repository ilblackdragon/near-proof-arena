import ZkFormal.NearV3.Candidates.ProcActualReadMemory
namespace ZkFormal.NearV3.Candidates.ProcActualGrantMemory
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcMemoryTimeInvariant ProcActualReplayEntry

def LogsBefore (t : Nat) (s : Acc) : Prop :=
  AllBefore t s.2.2.2.2.1 ∧ AllBefore t s.2.2.2.2.2.1 ∧ AllBefore t s.2.2.2.2.2.2.1

theorem step_logs (I : Input) (cv : Array CReq) (rd : Round) (sh : List Nat)
    (T x : Nat) (s out : Acc) (hs : LogsBefore (T+x) s) (ht : 0<T+x)
    (h : step I cv rd sh T x s=.ok (.yield out)) : LogsBefore (T+x+1) out := by
  rcases s with ⟨sb,rb,aa,gg,ol,os,orr,ps,used,gi,es⟩
  unfold step at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals
    exact ⟨modify_time _ ol _ _ hs.1 rfl ht,
      modify_time _ os _ _ hs.2.1 rfl ht,modify_time _ orr _ _ hs.2.2 rfl ht⟩

theorem loop_logs (I : Input) (cv : Array CReq) (rd : Round) (sh : List Nat)
    (T start len : Nat) (s out : Acc) (hs : LogsBefore (T+start) s) (ht : 0<T+start)
    (h : forIn (List.range' start len) s (step I cv rd sh T)=.ok out) :
    LogsBefore (T+start+len) out := by
  induction len generalizing start s with
  | zero => simp only [List.range'_zero,List.forIn_nil] at h; cases h; simpa using hs
  | succ len ih =>
    rw [List.range'_succ,List.forIn_cons] at h
    cases he : step I cv rd sh T start s with
    | error e => simp only [he,bind,Except.bind] at h; cases h
    | ok next =>
      obtain ⟨next,rfl,_,_,_⟩ := ProcActualEntryTransition.step_effect I cv rd sh T start s next
        (NearSpecV3.Rng.ofSeed I.seed) he
      simp only [he,bind,Except.bind] at h
      have hn := step_logs I cv rd sh T start s next hs ht he
      have hh := ih (start+1) next (by simpa [Nat.add_assoc] using hn) (by omega) h
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
end ZkFormal.NearV3.Candidates.ProcActualGrantMemory
