import ZkFormal.NearV3.Candidates.ProcActualMemoryValues
namespace ZkFormal.NearV3.Candidates.ProcActualMemoryTags
open NearSpecV3.Scheduler ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcActualReplayEntry

def OpTag (o : Gen.MOp) : Prop :=
  (o.op=OP_READ ∨ o.op=OP_GRANT) ∧ (o.op=OP_GRANT→b2n o.sf=if o.inc≤o.vin then 1 else 0)
def Logs (logs : Array (Array Gen.MOp)) : Prop := ∀ops∈logs.toList,∀o∈ops.toList,OpTag o
def Inv (s : Acc) : Prop :=Logs s.2.2.2.2.1 ∧ Logs s.2.2.2.2.2.1 ∧ Logs s.2.2.2.2.2.2.1

theorem modify (logs : Array (Array Gen.MOp)) (i : Nat) (o : Gen.MOp)
    (h:Logs logs) (ho:OpTag o) : Logs (logs.modify i (·.push o)) := by
  intro ops hm
  obtain ⟨j,hj,he⟩:=List.getElem_of_mem hm
  have hj':j<logs.size:=by simpa using hj
  have h0:=h _ (Array.getElem_mem_toList hj')
  subst ops
  simp only [Array.getElem_toList,Array.getElem_modify]
  split
  · intro x hx
    simp only [Array.toList_push,List.mem_append,List.mem_singleton] at hx
    rcases hx with hx|rfl
    · exact h0 x hx
    · exact ho
  · exact h0

set_option maxHeartbeats 800000 in
theorem entry (I : Input) (cv : Array CReq) (rd : Round) (sh : List Nat)
    (T x : Nat) (s out : Acc) (hs:Inv s)
    (h:step I cv rd sh T x s=.ok (.yield out)) : Inv out := by
  rcases s with ⟨sb,rb,aa,gg,ol,os,orr,ps,used,gi,es⟩
  unfold step at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals refine ⟨modify _ _ _ hs.1 ?_,modify _ _ _ hs.2.1 ?_,modify _ _ _ hs.2.2 ?_⟩
  all_goals simp [OpTag,b2n]

theorem entries (I : Input) (cv : Array CReq) (rd : Round) (sh xs : List Nat)
    (T : Nat) (s out : Acc) (hs:Inv s)
    (h:forIn xs s (step I cv rd sh T)=.ok out) : Inv out := by
  induction xs generalizing s with
  | nil=>simp only [List.forIn_nil] at h;cases h;exact hs
  | cons x xs ih=>
    rw [List.forIn_cons] at h
    cases he:step I cv rd sh T x s with
    | error e=>simp only [he,bind,Except.bind] at h;cases h
    | ok next=>
      obtain ⟨next,rfl,_,_,_⟩:=ProcActualEntryTransition.step_effect I cv rd sh T x s next (NearSpecV3.Rng.ofSeed I.seed) he
      simp only [he,bind,Except.bind] at h
      exact ih next (entry I cv rd sh T x s next hs he) h
end ZkFormal.NearV3.Candidates.ProcActualMemoryTags
