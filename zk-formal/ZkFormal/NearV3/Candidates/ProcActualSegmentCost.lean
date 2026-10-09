import ZkFormal.NearV3.Candidates.ProcActualRoundLogCost
namespace ZkFormal.NearV3.Candidates.ProcActualSegmentCost
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcActualRoundLogCost
private theorem list_prefix (xs:List (Array Gen.MOp))(n:Nat) :
    ((List.range n).map (fun i=>xs[i]!.size)).sum≤(xs.map Array.size).sum := by
  induction n generalizing xs with
  | zero=>simp
  | succ n ih=>
    cases xs with
    | nil=>simp [List.map_const',List.sum_replicate_nat,show (default:Array Gen.MOp).size=0 from rfl]
    | cons x xs=>
      rw [List.range_succ_eq_map]
      simp only [List.map_cons,List.map_map,List.sum_cons,Function.comp_def,List.getElem!_cons_zero,
        List.getElem!_cons_succ]
      exact Nat.add_le_add_left (ih xs) x.size

theorem prefix_bound (a:Array (Array Gen.MOp))(n:Nat) :
    ((List.range n).map (fun i=>a[i]!.size)).sum≤ProcActualLogCost.size a := by
  simpa [ProcActualLogCost.size,Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?] using list_prefix a.toList n

private theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α→Except ε β} {out : β}
    (h:x >>= f=.ok out) : ∃v,x=.ok v ∧ f v=.ok out := by
  cases x with
  | error e=>cases h
  | ok v=>exact ⟨v,rfl,h⟩

theorem append (f:Nat→Gen.Seg)(xs:List Nat)(gs out:Array Gen.Seg)
    (h:forIn xs gs (ProcActualSegments.appendStep f)=.ok out) :
    (out.toList.map (fun g=>g.ops.length)).sum=
      (gs.toList.map (fun g=>g.ops.length)).sum+(xs.map (fun i=>(f i).ops.length)).sum := by
  induction xs generalizing gs with
  | nil=>simp only [List.forIn_nil] at h;cases h;simp
  | cons i xs ih=>
    simp only [List.forIn_cons,ProcActualSegments.appendStep,bind,Except.bind] at h
    rw [ih _ h]
    simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem build (I:Input)(tau:Nat)(s:Acc)(gs:Array Gen.Seg)
    (h:ProcActualSegments.build I tau s=.ok gs) :
    (gs.toList.map (fun g=>g.ops.length)).sum≤logs s := by
  unfold ProcActualSegments.build at h
  obtain ⟨a,ha,h⟩:=bind_ok h
  obtain ⟨b,hb,h⟩:=bind_ok h
  rw [append _ _ _ _ h,append _ _ _ _ hb,append _ _ _ _ ha]
  simp only [Array.toList_empty,List.map_nil,List.sum_nil,Nat.zero_add,
    ProcActualSegments.make,ite_true,ite_false,Nat.reduceEqDiff,Array.length_toList]
  exact Nat.add_le_add (Nat.add_le_add (prefix_bound _ _) (prefix_bound _ _)) (prefix_bound _ _)
end ZkFormal.NearV3.Candidates.ProcActualSegmentCost
