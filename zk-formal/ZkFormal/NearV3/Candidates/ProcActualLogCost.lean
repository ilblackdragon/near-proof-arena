import ZkFormal.NearV3.Candidates.ProcActualComparisonCost
namespace ZkFormal.NearV3.Candidates.ProcActualLogCost
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

def size (a:Array (Array Gen.MOp)) : Nat := (a.toList.map Array.size).sum

private theorem list_modify (xs:List (Array Gen.MOp))(i:Nat)(o:Gen.MOp) :
    ((xs.modify i (·.push o)).map Array.size).sum≤(xs.map Array.size).sum+1 := by
  induction xs generalizing i with
  | nil=>simp
  | cons a xs ih=>
    cases i with
    | zero=>simp; omega
    | succ i=>simpa [Nat.add_assoc] using Nat.add_le_add_left (ih i) a.size

theorem modify (a:Array (Array Gen.MOp))(i:Nat)(o:Gen.MOp) :
    size (a.modify i (·.push o))≤size a+1 := by
  simpa only [size,Array.toList_modify] using list_modify a.toList i o

def entrySize (a:ProcActualReplayEntry.Acc) : Nat :=
  size a.2.2.2.2.1+size a.2.2.2.2.2.1+size a.2.2.2.2.2.2.1

private theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α→Except ε β} {out : β}
    (h:x >>= f=.ok out) : ∃v,x=.ok v ∧ f v=.ok out := by
  cases x with
  | error e=>cases h
  | ok v=>exact ⟨v,rfl,h⟩

theorem entry (I:Input)(cv:Array CReq)(rd:Round)(sh:List Nat)(T x:Nat)
    (a:ProcActualReplayEntry.Acc)(out:ForInStep ProcActualReplayEntry.Acc)
    (h:ProcActualReplayEntry.step I cv rd sh T x a=.ok out) :
    ∃u,out=.yield u ∧ entrySize u≤entrySize a+3 := by
  rcases a with ⟨sb,rb,aa,gg,l,s,r,p,used,gidx,es⟩
  unfold ProcActualReplayEntry.step at h
  dsimp only at h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  simp only [pure,Except.pure] at h
  split at h <;> refine ⟨_,(Except.ok.inj h).symm,?_⟩
  all_goals
    dsimp only [entrySize]
    calc
      _ ≤ (size l+1)+(size s+1)+(size r+1) := by
        apply Nat.add_le_add
        · exact Nat.add_le_add (modify _ _ _) (modify _ _ _)
        · apply modify
      _ = _ := by omega

theorem entries (I:Input)(cv:Array CReq)(rd:Round)(sh:List Nat)(T:Nat)
    (xs:List Nat)(a out:ProcActualReplayEntry.Acc)
    (h:forIn xs a (ProcActualReplayEntry.step I cv rd sh T)=.ok out) :
    entrySize out≤entrySize a+3*xs.length := by
  have hc:=ProcCodecComparisonCost.loop_cost _ _ entrySize (fun _=>3)
    (fun x _ s u=>entry I cv rd sh T x s u) _ _ h
  simpa [List.map_const',List.sum_replicate_nat,Nat.mul_comm] using hc
end ZkFormal.NearV3.Candidates.ProcActualLogCost
