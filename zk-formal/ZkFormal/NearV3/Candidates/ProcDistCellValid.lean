import ZkFormal.NearV3.Candidates.ProcDistShardValid
namespace ZkFormal.NearV3.Candidates.ProcDistCellValid
open NearSpecV3.Scheduler ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcDistGeneratorFactor ProcDistShardValid ProcDistCellBridge

def Endpoints (a:Array Endpoint) := ∀i:Nat,(a[i]!).2≤4500000
def Inv (a:CellAcc) := CmpsOk a.2.1 ∧ a.2.2.2.2.2≤4500000 ∧ Endpoints a.2.2.2.1

theorem set_bound (a:Array Endpoint)(ha:Endpoints a)(i:Nat)(v:Endpoint)(hv:v.2≤4500000) :
    Endpoints (a.set! i v) := by
  intro j
  by_cases he:i=j
  · subst j
    by_cases hi:i<a.size
    · rw [Array.getElem!_set!_self _ _ _ hi];exact hv
    · rw [Array.set!_eq_setIfInBounds,Array.setIfInBounds_eq_of_size_le (by omega)]
      exact ha i
  · rw [Array.getElem!_set!_ne _ _ _ _ he];exact ha j

private theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α→Except ε β} {out : β}
    (h:x >>= f=.ok out) : ∃v,x=.ok v ∧ f v=.ok out := by
  cases x with
  | error e=>cases h
  | ok v=>exact ⟨v,rfl,h⟩

theorem step_valid (I:Input)(R:Run)(i j:Nat)(a:CellAcc)(ha:Inv a)(out:ForInStep CellAcc)
    (h:cellStep I R i j a=.ok out) : ExceptLoop.StepInv Inv out := by
  have hs:=ha.2.1
  have hr:=ha.2.2 (receiver I R j)
  have hq1:=Nat.div_le_self a.2.2.2.2.2 a.2.2.2.2.1
  have hq2:=Nat.div_le_self (a.2.2.2.1[receiver I R j]!).2 (a.2.2.2.1[receiver I R j]!).1
  by_cases hal:I.allowed[sender I R i*R.n+receiver I R j]! = true
  all_goals
    unfold cellStep at h
    dsimp only at h
    dsimp only [sender,receiver] at hal hr hq2
    simp only [hal,Bool.false_eq_true,ite_false,ite_true] at h
  · obtain ⟨_,_,h⟩:=bind_ok h
    cases h
    refine ⟨?_,?_,?_⟩
    · apply ProcDistShardValid.append _ _ _ ha.1 <;> omega
    · exact Nat.le_trans (Nat.sub_le _ _) hs
    · apply set_bound _ ha.2.2
      exact Nat.le_trans (Nat.sub_le _ _) hr
  · cases h
    refine ⟨ha.1,hs,?_⟩
    apply set_bound _ ha.2.2
    simpa using hr

theorem loop_valid (I:Input)(R:Run)(i:Nat)(xs:List Nat)(a out:CellAcc)(ha:Inv a)
    (h:forIn xs a (cellStep I R i)=.ok out) : Inv out :=
  ExceptLoop.invariant xs (cellStep I R i) Inv
    (fun j _ a ha o ho=>step_valid I R i j a ha o ho) a out ha h
end ZkFormal.NearV3.Candidates.ProcDistCellValid
