import ZkFormal.NearV3.Candidates.ProcActualMemoryTagReplay
import ZkFormal.NearV3.Candidates.ProcActualComparisonFactor
namespace ZkFormal.NearV3.Candidates.ProcActualMemoryTagSegments
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcActualMemoryTags
open ZkFormal.NearV3.Sched.Complete

def SegTag (g : Gen.Seg) :=∀o∈g.ops,OpTag o

theorem selected (logs : Array (Array Gen.MOp)) (h:Logs logs) (i : Nat) : ∀o∈logs[i]!.toList,OpTag o := by
  by_cases hi:i<logs.size
  · rw [getElem!_pos logs i hi]
    exact h _ (Array.getElem_mem_toList hi)
  · rw [getElem!_neg logs i hi]
    change ∀o∈([]:List Gen.MOp),OpTag o
    simp

theorem make (I : Input) (tau : Nat) (s : ProcActualReplayRound.Acc)
    (hs:Inv (ProcActualReplayRound.entryAcc s)) (kind i : Nat) : SegTag (ProcActualSegments.make I tau s kind i) := by
  unfold ProcActualSegments.make
  split
  · exact selected _ hs.1 i
  · split
    · exact selected _ hs.2.1 i
    · exact selected _ hs.2.2 i

theorem append (f : Nat→Gen.Seg) (xs : List Nat) (gs out : Array Gen.Seg)
    (hf:∀i∈xs,SegTag (f i)) (hg:∀g∈gs.toList,SegTag g)
    (h:forIn xs gs (ProcActualSegments.appendStep f)=.ok out) : ∀g∈out.toList,SegTag g := by
  apply ExceptLoop.invariant xs _ (fun a=>∀g∈a.toList,SegTag g) ?_ gs out hg h
  intro i hi a ha u hu
  simp only [ProcActualSegments.appendStep,Except.ok.injEq] at hu
  subst u
  intro g hm
  simp only [Array.toList_push,List.mem_append,List.mem_singleton] at hm
  rcases hm with hm|rfl
  · exact ha g hm
  · exact hf i hi

private theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α→Except ε β} {out : β}
    (h:x >>= f=.ok out) : ∃v,x=.ok v ∧ f v=.ok out := by
  cases x with
  | error e=>cases h
  | ok v=>exact ⟨v,rfl,h⟩

theorem build (I : Input) (tau : Nat) (s : ProcActualReplayRound.Acc) (out : Array Gen.Seg)
    (hs:Inv (ProcActualReplayRound.entryAcc s)) (h:ProcActualSegments.build I tau s=.ok out) :
    ∀g∈out.toList,SegTag g := by
  unfold ProcActualSegments.build at h
  obtain ⟨a,ha,h⟩:=bind_ok h
  obtain ⟨b,hb,h⟩:=bind_ok h
  have hfa:=append _ _ _ a (fun i _=>make I tau s hs 0 i) (by simp) ha
  have hfb:=append _ _ a b (fun i _=>make I tau s hs 1 i) hfa hb
  exact append _ _ b out (fun i _=>make I tau s hs 2 i) hfb h

theorem run (I : Input) (tau : Nat) (R : Run) (h:ActualRun.run I tau=.ok R) : ∀g∈R.segs,SegTag g := by
  rw [ProcActualRunFactor.run_eq_prefix] at h
  obtain ⟨⟨cv,st,rs,ev⟩,_,h⟩:=bind_ok h
  dsimp only at h
  rw [ProcActualEntryFactor.rest_eq,ProcActualRoundFactor.rest_eq,ProcActualReplayFactor.rest_eq] at h
  obtain ⟨s,hs,h⟩:=bind_ok h
  have htag:=ProcActualMemoryTagReplay.replay I cv rs s hs
  rw [ProcActualMemoryFactor.finish_eq,ProcActualSegmentFactor.finish_eq] at h
  unfold ProcActualSegmentFactor.finishSegments at h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨gs,hgs,h⟩:=bind_ok h
  obtain ⟨cs,_,h⟩:=bind_ok h
  have hg:=build I tau s gs htag hgs
  rw [ProcActualComparisonFactor.afterMemory_eq] at h
  obtain ⟨ds,_,h⟩:=bind_ok h
  unfold ProcActualComparisonFactor.finish at h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  cases h
  exact hg
end ZkFormal.NearV3.Candidates.ProcActualMemoryTagSegments
