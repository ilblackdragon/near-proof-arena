import ZkFormal.NearV3.Candidates.ProcActualMemoryMetadata
namespace ZkFormal.NearV3.Candidates.ProcActualMemorySegOk
open ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete NearSpecV3.Scheduler
private theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α→Except ε β} {out : β}
    (h:x >>= f=.ok out) : ∃v,x=.ok v ∧ f v=.ok out := by
  cases x with
  | error e=>cases h
  | ok v=>exact ⟨v,rfl,h⟩

theorem metadata (sp : SchedPub) (hs:SchedPubOk sp)
    (ha:sp.allowed.size=sp.ids.length*sp.ids.length) (prev : NearSpec.Bandwidth.State)
    (tau : Nat) (ht:tau≤32) (R : Run)
    (h:ActualRun.run (ProcPreparedSequence.input sp prev) tau=.ok R) :
    ∀g∈R.segs,g.vin0=b2n g.al ∧ g.addr<P ∧ g.vin0<P ∧ g.v0<P ∧ g.wfin<P := by
  let I:=ProcPreparedSequence.input sp prev
  rw [ProcActualRunFactor.run_eq_prefix] at h
  obtain ⟨⟨cv,st,rs,ev⟩,hpfx,h⟩:=bind_ok h
  dsimp only at h
  rw [ProcActualEntryFactor.rest_eq,ProcActualRoundFactor.rest_eq,ProcActualReplayFactor.rest_eq] at h
  obtain ⟨s,hreplay,h⟩:=bind_ok h
  obtain ⟨hcv,hp⟩:=ProcActualAfterMemoryReduction.prefix_facts I cv st rs ev hpfx
  rw [ProcActualMemoryFactor.finish_eq,ProcActualSegmentFactor.finish_eq] at h
  unfold ProcActualSegmentFactor.finishSegments at h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨gs,hgs,h⟩:=bind_ok h
  obtain ⟨cs,_,h⟩:=bind_ok h
  have hg:∀g∈gs.toList,g.vin0=b2n g.al ∧ g.addr<P ∧ g.vin0<P ∧ g.v0<P ∧ g.wfin<P := by
    intro g hg
    rw [ProcActualMemoryFinal.build_records I tau s gs hgs] at hg
    rcases List.mem_append.mp hg with hg|hg
    · rcases List.mem_append.mp hg with hg|hg
      · obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hg
        exact ProcActualMemoryMetadata.make sp hs ha prev tau ht cv rs s st hcv hp hreplay 0 i (by decide) (List.mem_range.mp hi)
      · obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hg
        exact ProcActualMemoryMetadata.make sp hs ha prev tau ht cv rs s st hcv hp hreplay 1 i (by decide) (List.mem_range.mp hi)
    · obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hg
      exact ProcActualMemoryMetadata.make sp hs ha prev tau ht cv rs s st hcv hp hreplay 2 i (by decide) (List.mem_range.mp hi)
  rw [ProcActualComparisonFactor.afterMemory_eq] at h
  obtain ⟨ds,_,h⟩:=bind_ok h
  unfold ProcActualComparisonFactor.finish at h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  cases h
  exact hg

theorem run (sp : SchedPub) (hs:SchedPubOk sp)
    (ha:sp.allowed.size=sp.ids.length*sp.ids.length) (prev : NearSpec.Bandwidth.State)
    (tau : Nat) (ht:tau≤32) (R : Run)
    (h:ActualRun.run (ProcPreparedSequence.input sp prev) tau=.ok R) : ∀g∈R.segs,SegOk g := by
  intro g hg
  have hm:=metadata sp hs ha prev tau ht R h g hg
  exact ⟨hm.1,ProcActualMemoryChainSegments.run _ tau R h g hg,
    ProcActualMemoryCanonical.run _ tau R h g hg hm.2.1 hm.2.2.1 hm.2.2.2.1 hm.2.2.2.2⟩
end ZkFormal.NearV3.Candidates.ProcActualMemorySegOk
