import ZkFormal.NearV3.Candidates.ProcPendingCurrent
namespace ZkFormal.NearV3.Candidates.ProcPendingTransition
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler ProcPendingCurrent
private theorem throw_eq {α : Type} (e : String) : (throw e : Except String α)=.error e := rfl

/-- A model entry preserves all pending current-allowance bindings when its
selected link is distinct from the other pending requests. New pushes use the
actual updated allowance and the same request's next increase. -/
theorem entry_current (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (K z v : Nat) (s : ProcModelStep.EntryAcc)
    (hs : Current reqs s.2.1.al s.1)
    (hl : link reqs v<s.2.1.al.size)
    (hn : ∀p∈s.1,link reqs v≠link reqs p.v)
    (hj : v%64+1<64)
    (out : ForInStep ProcModelStep.EntryAcc)
    (h : ProcModelStep.entryStep n allowed reqs K z v s=.ok out) :
    ExceptLoop.StepInv (fun s=>Current reqs s.2.1.al s.1) out := by
  have hm := update_other reqs s.2.1.al s.1 hs (link reqs v)
    (s.2.1.al[link reqs v]!-reqs.toArray[v/64]!.incs.getD (v%64) 0) hn
  have he := next_link reqs v hj
  unfold ProcModelStep.entryStep at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals first
    | exact hs
    | exact hm
    | apply append_current reqs _ _ hm _
      · simpa only [he,Array.size_set!] using hl
      · change _ = _[link reqs (v+1)]!
        rw [he]
        rfl
    | apply append_current reqs _ _ hs _
      · simpa only [he] using hl
      · change _ = _[link reqs (v+1)]!
        rw [he]
        rfl
end ZkFormal.NearV3.Candidates.ProcPendingTransition
