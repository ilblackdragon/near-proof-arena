import ZkFormal.NearV3.Candidates.ProcActualMemoryComparisonInventory
import ZkFormal.NearV3.Candidates.ProcActualRoundComparisonInventory
namespace ZkFormal.NearV3.Candidates.ProcActualRunComparisonInventory
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete


private theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α→Except ε β} {out : β}
    (h:x >>= f=.ok out) : ∃v,x=.ok v ∧ f v=.ok out := by
  cases x with
  | error e=>cases h
  | ok v=>exact ⟨v,rfl,h⟩

theorem run (I : Input) (tau : Nat) (R : Run) (h:ActualRun.run I tau=.ok R) : R.cmps=R.segs.flatMap (fun g=>ProcActualMemoryComparisonInventory.requests 0 g.ops)++
      R.rounds.flatMap ProcActualRoundComparisonInventory.requests := by
  rw [ProcActualRunFactor.run_eq_prefix] at h
  obtain ⟨⟨cv,st,rs,ev⟩,_,h⟩:=bind_ok h
  dsimp only at h
  rw [ProcActualEntryFactor.rest_eq,ProcActualRoundFactor.rest_eq,
    ProcActualReplayFactor.rest_eq] at h
  obtain ⟨s,hs,h⟩:=bind_ok h
  rw [ProcActualMemoryFactor.finish_eq,ProcActualSegmentFactor.finish_eq] at h
  unfold ProcActualSegmentFactor.finishSegments at h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨gs,hgs,h⟩:=bind_ok h
  obtain ⟨cs,hcs,h⟩:=bind_ok h
  rw [←Array.forIn_toList] at hcs
  have htag:=ProcActualMemoryTagSegments.build I tau s gs (ProcActualMemoryTagReplay.replay I cv rs s hs) hgs
  have hm:=ProcActualMemoryComparisonInventory.segments _ _ _ htag hcs
  rw [ProcActualComparisonFactor.afterMemory_eq] at h
  obtain ⟨ds,hds,h⟩:=bind_ok h
  rw [←Array.forIn_toList] at hds
  have hd:=ProcActualRoundComparisonInventory.rounds _ _ _ hds
  unfold ProcActualComparisonFactor.finish at h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  cases h
  simpa only [hm,Array.toList_empty,List.nil_append,ProcActualRoundTimes.rounds] using hd
end ZkFormal.NearV3.Candidates.ProcActualRunComparisonInventory
