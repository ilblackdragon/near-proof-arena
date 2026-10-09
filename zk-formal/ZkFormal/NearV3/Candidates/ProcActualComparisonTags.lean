import ZkFormal.NearV3.Candidates.ProcActualComparisonFactor
import ZkFormal.NearV3.Candidates.ExceptLoop
namespace ZkFormal.NearV3.Candidates.ProcActualComparisonTags
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
abbrev Cmps := ProcActualMemoryScan.Cmps

def Tag (q : Nat×Nat×Nat) := q.2.2=if q.2.1≤q.1 then 1 else 0
def Good (cs : Cmps) := ∀q∈cs.toList,Tag q

theorem push (cs : Cmps) (h:Good cs) (x y : Nat) : Good (cs.push (x,y,if y≤x then 1 else 0)) := by
  intro q hq
  simp only [Array.toList_push,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hq
  rcases hq with hq|rfl
  · exact h q hq
  · rfl

private theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α→Except ε β} {out : β}
    (h:x >>= f=.ok out) : ∃v,x=.ok v ∧ f v=.ok out := by
  cases x with
  | error e=>cases h
  | ok v=>exact ⟨v,rfl,h⟩

theorem memory_step (o : Gen.MOp) (s : Cmps×Nat) (out : ForInStep (Cmps×Nat))
    (hs:Good s.1) (h:ProcActualMemoryScan.actualStep o s=.ok out) : ExceptLoop.StepInv (fun s=>Good s.1) out := by
  unfold ProcActualMemoryScan.actualStep at h
  obtain ⟨_,_,h⟩:=bind_ok h
  simp only [pure,Except.pure] at h
  split at h <;> cases h
  · exact push _ (push _ hs _ _) _ _
  · exact push _ hs _ _

theorem memory_segment (g : Gen.Seg) (cs : Cmps) (out : ForInStep Cmps)
    (hs:Good cs) (h:ProcActualMemoryScan.segmentStep g cs=.ok out) : ExceptLoop.StepInv Good out := by
  rw [ProcActualMemoryScan.segment_eq] at h
  obtain ⟨s,hloop,h⟩:=bind_ok h
  simp only [pure,Except.pure,Except.ok.injEq] at h
  subst out
  exact ExceptLoop.invariant _ _ (fun s=>Good s.1)
    (fun o _ s hs out ho=>memory_step o s out hs ho) _ s hs hloop

theorem bucket (rd : Gen.RoundD) (i : Nat) (cs : Cmps) (out : ForInStep Cmps)
    (hs:Good cs) (h:ProcActualBucketComparisons.step rd i cs=.ok out) : ExceptLoop.StepInv Good out := by
  unfold ProcActualBucketComparisons.step at h
  dsimp only at h
  obtain ⟨_,_,h⟩:=bind_ok h
  cases h
  exact push _ hs _ _

theorem round_step (rd : Gen.RoundD) (cs : Cmps) (out : ForInStep Cmps)
    (hs:Good cs) (h:ProcActualComparisonFactor.roundStep rd cs=.ok out) : ExceptLoop.StepInv Good out := by
  unfold ProcActualComparisonFactor.roundStep at h
  split at h
  · obtain ⟨_,_,h⟩:=bind_ok h
    obtain ⟨s,hloop,h⟩:=bind_ok h
    cases h
    exact ExceptLoop.invariant _ _ Good (fun i _ c hc u hu=>bucket rd i c u hc hu) _ s (push _ hs _ _) hloop
  · obtain ⟨s,hloop,h⟩:=bind_ok h
    cases h
    exact ExceptLoop.invariant _ _ Good (fun i _ c hc u hu=>bucket rd i c u hc hu) _ s hs hloop

theorem memory (gs : List Gen.Seg) (cs out : Cmps) (hs:Good cs)
    (h:forIn gs cs ProcActualMemoryScan.segmentStep=.ok out) : Good out :=
  ExceptLoop.invariant _ _ Good (fun g _ c hc u hu=>memory_segment g c u hc hu) cs out hs h

theorem rounds (rs : List Gen.RoundD) (cs out : Cmps) (hs:Good cs)
    (h:forIn rs cs ProcActualComparisonFactor.roundStep=.ok out) : Good out :=
  ExceptLoop.invariant _ _ Good (fun r _ c hc u hu=>round_step r c u hc hu) cs out hs h
end ZkFormal.NearV3.Candidates.ProcActualComparisonTags
