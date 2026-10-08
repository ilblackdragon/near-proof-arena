import ZkFormal.NearV3.Candidates.ProcRoundGuards
namespace ZkFormal.NearV3.Candidates.ProcTagTransition
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler ProcZeroPending ProcZeroTransition ProcRoundGuards
private theorem throw_eq {α : Type} (e : String) : (throw e : Except String α)=.error e := rfl

theorem entry_positive (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (K z v : Nat) (s : ProcModelStep.EntryAcc)
    (hs : ∀p∈s.1,p.key≠0 → p.z=0)
    (out : ForInStep ProcModelStep.EntryAcc)
    (h : ProcModelStep.entryStep n allowed reqs K z v s=.ok out) :
    ExceptLoop.StepInv (fun s=>∀p∈s.1,p.key≠0 → p.z=0) out := by
  unfold ProcModelStep.entryStep at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals first
    | exact hs
    | intro p hp hk
      simp only [List.mem_append,List.mem_singleton] at hp
      rcases hp with hp|rfl
      · exact hs p hp hk
      · exact if_neg hk

theorem entry_below (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (K z v : Nat) (s : ProcModelStep.EntryAcc) (hs : ∀p∈s.1,Below K p.key)
    (out : ForInStep ProcModelStep.EntryAcc)
    (h : ProcModelStep.entryStep n allowed reqs K z v s=.ok out) :
    ExceptLoop.StepInv (fun s=>∀p∈s.1,Below K p.key) out := by
  unfold ProcModelStep.entryStep at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals first
    | exact hs
    | intro p hp
      simp only [List.mem_append,List.mem_singleton] at hp
      rcases hp with hp|rfl
      · exact hs p hp
      · unfold Below
        simp_all only [Bool.not_eq_true',Bool.eq_false_iff,
          Bool.or_eq_true,decide_eq_true_eq,Bool.and_eq_true,beq_iff_eq,Classical.not_not,and_true,true_and,false_and]

theorem filtered (ps : List Push) (last : Option (Nat×Nat)) (z : Nat)
    (hs : Tags last ps) (ho : Ordered last (ProcMaxBucket.maxKey ps) z) :
    Tags (some (ProcMaxBucket.maxKey ps,z)) (ps.filter (fun p=>p.key != ProcMaxBucket.maxKey ps)) := by
  refine ⟨filtered_pending ps last _ z hs.1 rfl ho,?_,?_⟩
  · intro p hp hk
    exact hs.2.1 p (List.mem_filter.mp hp).1 hk
  · intro p hp
    have hm := List.mem_filter.mp hp
    have hb := (ProcMaxBucket.fold_max ps 0).2.1 p hm.1
    change p.key≤ProcMaxBucket.maxKey ps at hb
    have hn : p.key≠ProcMaxBucket.maxKey ps := by simpa using hm.2
    exact Or.inl (by change p.key<ProcMaxBucket.maxKey ps; omega)

theorem entries_tags (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (K z : Nat) (vs : List Nat) (s out : ProcModelStep.EntryAcc)
    (hs : Tags (some (K,z)) s.1)
    (h : forIn vs s (ProcModelStep.entryStep n allowed reqs K z)=.ok out) :
    Tags (some (K,z)) out.1 := by
  refine ⟨entries_pending n allowed reqs K z vs s out hs.1 h,?_,?_⟩
  · exact ExceptLoop.invariant vs (ProcModelStep.entryStep n allowed reqs K z)
      (fun s=>∀p∈s.1,p.key≠0 → p.z=0)
      (fun v _ s hs out h=>entry_positive n allowed reqs K z v s hs out h) s out hs.2.1 h
  · exact ExceptLoop.invariant vs (ProcModelStep.entryStep n allowed reqs K z)
      (fun s=>∀p∈s.1,Below K p.key)
      (fun v _ s hs out h=>entry_below n allowed reqs K z v s hs out h) s out hs.2.2 h
end ZkFormal.NearV3.Candidates.ProcTagTransition
