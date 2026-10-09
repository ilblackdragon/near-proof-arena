import ZkFormal.NearV3.Candidates.ProcModelTime
import ZkFormal.NearV3.Candidates.ProcPendingTransition
namespace ZkFormal.NearV3.Candidates.ProcLiveLinks
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler ProcPendingCurrent
open List
private theorem throw_eq {α : Type} (e : String) : (throw e : Except String α)=.error e := rfl

def live (reqs : List Req) (ps : List Push) (vs : List Nat) : List Nat :=
  ps.map (fun p=>link reqs p.v)++vs.map (link reqs)

theorem entry_sublist (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (K z v : Nat) (s : ProcModelStep.EntryAcc) (hj : v%64+1<64)
    (out : ForInStep ProcModelStep.EntryAcc)
    (h : ProcModelStep.entryStep n allowed reqs K z v s=.ok out) :
    ExceptLoop.StepInv (fun out=>out.1.map (fun p=>link reqs p.v) <+
      s.1.map (fun p=>link reqs p.v)++[link reqs v]) out := by
  unfold ProcModelStep.entryStep at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals simp only [ExceptLoop.StepInv,List.map_append,List.map_cons,List.map_nil,next_link reqs v hj]
  all_goals first | exact List.Sublist.refl _ | exact List.sublist_append_left _ _

theorem selected_distinct (reqs : List Req) (ps : List Push) (v : Nat) (vs : List Nat)
    (h : (live reqs ps (v::vs)).Nodup) :
    (∀p∈ps,link reqs v≠link reqs p.v) ∧ ∀w∈vs,link reqs v≠link reqs w := by
  simp only [live,List.map_cons,List.nodup_append,List.nodup_cons] at h
  refine ⟨?_,?_⟩
  · intro p hp he
    exact h.2.2 (link reqs p.v) (List.mem_map_of_mem hp) (link reqs v) (by simp) he.symm
  · intro w hw he
    exact h.2.1.1 (he ▸ List.mem_map_of_mem hw)

theorem entry_nodup (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (K z v : Nat) (vs : List Nat) (s : ProcModelStep.EntryAcc) (hj : v%64+1<64)
    (hs : (live reqs s.1 (v::vs)).Nodup) (out : ForInStep ProcModelStep.EntryAcc)
    (h : ProcModelStep.entryStep n allowed reqs K z v s=.ok out) :
    ExceptLoop.StepInv (fun out=>(live reqs out.1 vs).Nodup) out := by
  have hh := entry_sublist n allowed reqs K z v s hj out h
  cases out <;> simp only [ExceptLoop.StepInv] at hh ⊢
  all_goals
    apply (hh.append (List.Sublist.refl (vs.map (link reqs)))).nodup
    simpa [live,List.append_assoc] using hs
end ZkFormal.NearV3.Candidates.ProcLiveLinks
