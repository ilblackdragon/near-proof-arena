import ZkFormal.NearV3.Candidates.ProcCodecComparisonCost
import ZkFormal.NearV3.Sched.Gen.Dist
namespace ZkFormal.NearV3.Candidates.ProcDistComparisonCost
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcCodecComparisonCost
private theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α→Except ε β} {out : β}
    (h:x >>= f=.ok out) : ∃v,x=.ok v ∧ f v=.ok out := by
  cases x with
  | error e=>cases h
  | ok v=>exact ⟨v,rfl,h⟩
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
theorem generated_cost (I:Input)(R:Run)(out:DistOut)
    (h:distRows I R=.ok out) : out.cmps.length≤2*R.n+R.n*R.n := by
  unfold distRows at h
  dsimp only at h
  obtain ⟨sh,hsh,h⟩:=bind_ok h
  obtain ⟨grid,hgrid,h⟩:=bind_ok h
  cases h
  have hshc := loop_cost _ _
    (fun s : Array (Array Nat) × List (Nat×Nat×Nat) => s.2.length)
    (fun _ => R.n) ?_ _ _ hsh
  · have hgc := loop_cost _ _
      (fun s : Array (Array Nat) × List (Nat×Nat×Nat) × Array Nat × Array (Nat×Nat) => s.2.1.length)
      (fun _ => R.n) ?_ _ _ hgrid
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_nil] at hshc
      simp only [List.map_const', List.length_range, List.sum_replicate_nat] at hgc
      try dsimp only at hshc hgc ⊢
      omega
    · intro i hi s o ho
      try dsimp only at ho
      obtain ⟨u,hu,ho⟩ := bind_ok ho
      simp only [pure, Except.pure, Except.ok.injEq] at ho
      subst o
      refine ⟨_,rfl,?_⟩
      have hh := loop_cost _ _
        (fun s : Array (Array Nat) × List (Nat×Nat×Nat) × Array Nat × Array (Nat×Nat) × (Nat×Nat) => s.2.1.length)
        (fun _ => 1) ?_ _ _ hu
      · simpa [List.map_const', List.sum_replicate_nat] using hh
      · intro j hj a b hb
        try dsimp only at hb
        split at hb
        · obtain ⟨_,_,hb⟩ := bind_ok hb
          simp only [pure,Except.pure] at hb
          split at hb <;> refine ⟨_,(Except.ok.inj hb).symm,?_⟩ <;>
            simp only [List.length_append,List.length_cons,List.length_nil] <;> omega
        · simp only [pure,Except.pure] at hb
          split at hb <;> refine ⟨_,(Except.ok.inj hb).symm,?_⟩ <;>
            simp only [List.length_append,List.length_cons,List.length_nil] <;> omega
  · intro sd hsd s o ho
    try dsimp only at ho
    obtain ⟨u,hu,ho⟩ := bind_ok ho
    simp only [pure, Except.pure, Except.ok.injEq] at ho
    subst o
    refine ⟨_,rfl,?_⟩
    have hh := loop_cost _ _
      (fun s : Array (Array Nat) × List (Nat×Nat×Nat) × Nat => s.2.1.length)
      (fun _ => 1) ?_ _ _ hu
    · simpa [List.map_const', List.sum_replicate_nat] using hh
    · intro i hi a b hb
      try dsimp only at hb
      obtain ⟨_,_,hb⟩ := bind_ok hb
      simp only [pure,Except.pure] at hb
      refine ⟨_,(Except.ok.inj hb).symm,?_⟩
      simp only [List.length_append,List.length_cons,List.length_nil,Nat.le_refl]
/-- All actual distribute requests, including both sorted shard sides. -/
theorem native_cost (I:Input)(R:Run)(out:DistOut)
    (h:distRows I R=.ok out)(hn:R.n≤64) : out.cmps.length≤4224 := by
  have hc:=generated_cost I R out h
  have hm:=Nat.mul_self_le_mul_self hn
  omega

theorem list_cost (xs:List (Input×Run×DistOut))
    (h:∀x∈xs,distRows x.1 x.2.1=.ok x.2.2 ∧ x.2.1.n≤64) :
    (xs.flatMap (fun x=>x.2.2.cmps)).length≤4224*xs.length := by
  induction xs with
  | nil=>simp
  | cons x xs ih=>
    have hx:=h x (by simp)
    have hc:=native_cost x.1 x.2.1 x.2.2 hx.1 hx.2
    have ht:=ih (fun y hy=>h y (by simp [hy]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    omega

theorem native_list_cost (xs:List (Input×Run×DistOut))
    (h:∀x∈xs,distRows x.1 x.2.1=.ok x.2.2 ∧ x.2.1.n≤64)(hlen:xs.length≤32) :
    (xs.flatMap (fun x=>x.2.2.cmps)).length≤135168 := by
  have hc:=list_cost xs h
  omega
end ZkFormal.NearV3.Candidates.ProcDistComparisonCost
