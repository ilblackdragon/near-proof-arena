import ZkFormal.NearV3.Candidates.ProcCodecComparisonCost
import ZkFormal.NearV3.Sched.Gen.Dist
namespace ZkFormal.NearV3.Candidates.ProcDistRowCost
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcCodecComparisonCost
private theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α→Except ε β} {out : β}
    (h:x >>= f=.ok out) : ∃v,x=.ok v ∧ f v=.ok out := by
  cases x with
  | error e=>cases h
  | ok v=>exact ⟨v,rfl,h⟩
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
theorem generated_cost (I:Input)(R:Run)(out:DistOut)
    (h:distRows I R=.ok out) : out.rows.size≤3*R.n+R.n*R.n := by
  unfold distRows at h
  dsimp only at h
  obtain ⟨sh,hsh,h⟩:=bind_ok h
  obtain ⟨grid,hgrid,h⟩:=bind_ok h
  cases h
  have hshc := loop_cost _ _
    (fun s : Array (Array Nat) × List (Nat×Nat×Nat) => s.1.size)
    (fun _ => R.n) ?_ _ _ hsh
  · have hgc := loop_cost _ _
      (fun s : Array (Array Nat) × List (Nat×Nat×Nat) × Array Nat × Array (Nat×Nat) => s.1.size)
      (fun _ => R.n+1) ?_ _ _ hgrid
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_nil,Array.size_empty] at hshc
      simp only [List.map_const', List.length_range, List.sum_replicate_nat] at hgc
      try dsimp only at hshc hgc ⊢
      simp only [Nat.mul_add,Nat.mul_one] at hgc
      omega
    · intro i hi s o ho
      try dsimp only at ho
      obtain ⟨u,hu,ho⟩ := bind_ok ho
      simp only [pure, Except.pure, Except.ok.injEq] at ho
      subst o
      refine ⟨_,rfl,?_⟩
      have hh := loop_cost _ _
        (fun s : Array (Array Nat) × List (Nat×Nat×Nat) × Array Nat × Array (Nat×Nat) × (Nat×Nat) => s.1.size)
        (fun _ => 1) ?_ _ _ hu
      · simpa [List.map_const', List.sum_replicate_nat,Array.size_push,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
      · intro j hj a b hb
        try dsimp only at hb
        split at hb
        · obtain ⟨_,_,hb⟩ := bind_ok hb
          simp only [pure,Except.pure] at hb
          split at hb <;> refine ⟨_,(Except.ok.inj hb).symm,?_⟩ <;>
            simp only [List.length_append,List.length_cons,List.length_nil,Array.size_push] <;> omega
        · simp only [pure,Except.pure] at hb
          split at hb <;> refine ⟨_,(Except.ok.inj hb).symm,?_⟩ <;>
            simp only [List.length_append,List.length_cons,List.length_nil,Array.size_push] <;> omega
  · intro sd hsd s o ho
    try dsimp only at ho
    obtain ⟨u,hu,ho⟩ := bind_ok ho
    simp only [pure, Except.pure, Except.ok.injEq] at ho
    subst o
    refine ⟨_,rfl,?_⟩
    have hh := loop_cost _ _
      (fun s : Array (Array Nat) × List (Nat×Nat×Nat) × Nat => s.1.size)
      (fun _ => 1) ?_ _ _ hu
    · simpa [List.map_const', List.sum_replicate_nat,Array.size_push,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
    · intro i hi a b hb
      try dsimp only at hb
      obtain ⟨_,_,hb⟩ := bind_ok hb
      simp only [pure,Except.pure] at hb
      refine ⟨_,(Except.ok.inj hb).symm,?_⟩
      simp only [Array.size_push,Nat.le_refl]

end ZkFormal.NearV3.Candidates.ProcDistRowCost
