import ZkFormal.NearV3.Candidates.ProcActualComparisonTags
import ZkFormal.NearV3.Candidates.CmpHeight
namespace ZkFormal.NearV3.Candidates.ProcActualComparisonValid
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcActualComparisonTags

private theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α→Except ε β} {out : β}
    (h:x >>= f=.ok out) : ∃v,x=.ok v ∧ f v=.ok out := by
  cases x with
  | error e=>cases h
  | ok v=>exact ⟨v,rfl,h⟩

private theorem checked (p : Bool) (msg : String) (u : Unit) (h:check p msg=.ok u) : p=true := by
  cases p <;> simp [check] at h ⊢

theorem run (I : Input) (tau : Nat) (R : Run) (h:ActualRun.run I tau=.ok R) : ∀q∈R.cmps,CmpOk q := by
  rw [ProcActualRunFactor.run_eq_prefix] at h
  obtain ⟨⟨cv,st,rs,ev⟩,_,h⟩:=bind_ok h
  dsimp only at h
  rw [ProcActualEntryFactor.rest_eq,ProcActualRoundFactor.rest_eq,
    ProcActualReplayFactor.rest_eq] at h
  obtain ⟨s,_,h⟩:=bind_ok h
  rw [ProcActualMemoryFactor.finish_eq,ProcActualSegmentFactor.finish_eq] at h
  unfold ProcActualSegmentFactor.finishSegments at h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨gs,_,h⟩:=bind_ok h
  obtain ⟨cs,hcs,h⟩:=bind_ok h
  rw [←Array.forIn_toList] at hcs
  have hm:=memory _ _ _ (by intro q hq; cases hq) hcs
  rw [ProcActualComparisonFactor.afterMemory_eq] at h
  obtain ⟨ds,hds,h⟩:=bind_ok h
  rw [←Array.forIn_toList] at hds
  have hd:=rounds _ _ _ hm hds
  unfold ProcActualComparisonFactor.finish at h
  obtain ⟨u,hcheck,h⟩:=bind_ok h
  have hrange:=checked _ _ u hcheck
  obtain ⟨_,_,h⟩:=bind_ok h
  cases h
  intro q hq
  have ht:=hd q hq
  have hb:= (List.all_eq_true.mp (show ds.toList.all (fun (x,y,_)=>x<2^29 && y<2^29)=true from by
    rw [Array.all_toList];exact hrange)) q hq
  have hb':q.1<2^29 ∧ q.2.1<2^29 := by simpa only [Bool.and_eq_true,decide_eq_true_eq] using hb
  exact ⟨hb'.1,hb'.2,ht⟩
end ZkFormal.NearV3.Candidates.ProcActualComparisonValid
