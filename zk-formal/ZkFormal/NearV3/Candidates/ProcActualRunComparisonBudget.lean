import ZkFormal.NearV3.Candidates.ProcActualSegmentCost
import ZkFormal.NearV3.Candidates.ProcActualSpendBudget
import ZkFormal.NearV3.Candidates.ProcActualRequestCount
namespace ZkFormal.NearV3.Candidates.ProcActualRunComparisonBudget
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcActualRoundLogCost
private theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α→Except ε β} {out : β}
    (h:x >>= f=.ok out) : ∃v,x=.ok v ∧ f v=.ok out := by
  cases x with
  | error e=>cases h
  | ok v=>exact ⟨v,rfl,h⟩

theorem run_cost (I:Input)(tau:Nat)(R:Run)(h:ActualRun.run I tau=.ok R) :
    R.cmps.length≤2*R.conv.length+8*(R.rounds.map (fun rd=>rd.entries.length)).sum := by
  rw [ProcActualRunFactor.run_eq_prefix] at h
  obtain ⟨⟨cv,st,rs,ev⟩,_,h⟩:=bind_ok h
  dsimp only at h
  rw [ProcActualEntryFactor.rest_eq,ProcActualRoundFactor.rest_eq,
    ProcActualReplayFactor.rest_eq] at h
  obtain ⟨s,hs,h⟩:=bind_ok h
  obtain ⟨hl,hr⟩:=ProcActualRoundLogCost.replay I cv rs s hs
  rw [ProcActualMemoryFactor.finish_eq,ProcActualSegmentFactor.finish_eq] at h
  unfold ProcActualSegmentFactor.finishSegments at h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨gs,hgs,h⟩:=bind_ok h
  obtain ⟨cs,hcs,h⟩:=bind_ok h
  have hg:=ProcActualSegmentCost.build I tau s gs hgs
  rw [←Array.forIn_toList] at hcs
  have hm:=ProcActualComparisonCost.memory_list _ _ _ hcs
  rw [ProcActualComparisonFactor.afterMemory_eq] at h
  obtain ⟨ds,hds,h⟩:=bind_ok h
  rw [←Array.forIn_toList] at hds
  have hd:=ProcActualComparisonCost.rounds _ _ _ hds
  unfold ProcActualComparisonFactor.finish at h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  cases h
  rcases s with ⟨sb,rb,aa,gg,l,s,r,p,bs,T,k,K,z,used,rsOut,idx⟩
  simp only [Array.length_toList,Array.size_empty,Nat.zero_add] at hm ⊢
  simp only [count,ProcActualRoundTimes.rounds,Array.length_toList] at hl hr hd
  omega

theorem native_cost (I:Input)(tau:Nat)(R:Run)
    (hp:NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length=some I.p)
    (h:ActualRun.run I tau=.ok R)(hn:I.ids.length≤64)(hc:R.conv.length≤4096) :
    R.cmps.length≤62976 := by
  have hb:=run_cost I tau R h
  have he:=ProcActualSpendBudget.run_steps_le I tau R hp h
  omega
theorem prepared_cost (sp:NearSpecV3.Scheduler.SchedPub)(hs:SchedPubOk sp)
    (prev:NearSpec.Bandwidth.State)(tau:Nat)(R:Run)
    (h:ActualRun.run (ProcPreparedSequence.input sp prev) tau=.ok R) : R.cmps.length≤62976 := by
  have hc:=ProcActualRequestCount.run_count _ tau R h
  have hb:=(ProcPreparedSequence.input_bounds sp prev hs).2.2
  exact native_cost _ tau R hs.params h hs.n64 (by omega)
end ZkFormal.NearV3.Candidates.ProcActualRunComparisonBudget
