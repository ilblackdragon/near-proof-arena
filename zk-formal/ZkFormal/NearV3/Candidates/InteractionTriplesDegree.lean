import ZkFormal.NearV3.Candidates.InteractionTriplesTransport
namespace ZkFormal.NearV3.Candidates.InteractionTriples
open ZkFormal.Air

theorem constraint_bound (T : Air.Table) (d : Nat)
    (h : ∀e∈T.allConstraints,e.degree≤d) : ∀e∈(table T).allConstraints,e.degree≤d := by
  have hbits:∀i∈reorder T.interactions,∀e∈(i.mult.map fun b=>Expr.mul b (.add b (.neg (.const 1)))),e.degree≤d:=by
    apply (forall_iff _ (fun i=>∀e∈(i.mult.map fun b=>Expr.mul b (.add b (.neg (.const 1)))),e.degree≤d)
      (by simp [dummy])
      (by simp [dummy])).mpr
    intro i hi e he
    exact h e (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i,hi,he⟩))
  intro e he
  rcases List.mem_append.mp he with he|he
  · exact h e (List.mem_append_left _ he)
  · obtain ⟨i,hi,he⟩:=List.mem_flatMap.mp he
    exact hbits i hi e he

theorem pair_constraint_bound (T : Air.Table) (d : Nat)
    (h : ∀e∈T.allConstraints,e.degree≤d) :
    ∀e∈({T with interactions:=InteractionPairing.reorder T.interactions}:Air.Table).allConstraints,e.degree≤d := by
  intro e he
  rcases List.mem_append.mp he with he|he
  · exact h e (List.mem_append_left _ he)
  · obtain ⟨i,hi,he⟩:=List.mem_flatMap.mp he
    have hi':i∈T.interactions:=(InteractionPairing.reorder_perm _).mem_iff.mp hi
    exact h e (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i,hi',he⟩))
theorem paired_constraint_bound (T : Air.Table) (d : Nat)
    (h : ∀e∈T.allConstraints,e.degree≤d) :
    ∀e∈(table {T with interactions:=InteractionPairing.reorder T.interactions}).allConstraints,e.degree≤d :=
  constraint_bound _ d (pair_constraint_bound T d h)

theorem fused_paired_constraint_bound (ts : List Air.Table) (d : Nat)
    (h : ∀T∈ts,∀e∈T.allConstraints,e.degree≤d) :
    ∀e∈(table {(HorizontalTables.fuse ts) with interactions:=InteractionPairing.reorder (HorizontalTables.fuse ts).interactions}).allConstraints,e.degree≤d :=
  paired_constraint_bound _ d (HorizontalProfile.fused_constraint_bound ts d h)

theorem degree_eq (T : Air.Table) (g d : Nat) (hd : 2≤d)
    (hc : ∀e∈T.allConstraints,e.degree≤d) (ha : T.auxDegree g=d) : T.degree g=d := by
  have fold : ∀xs:List Nat,(∀x∈xs,x≤d)→xs.foldr max 2≤d:=by
    intro xs
    induction xs with
    | nil=>intro _; exact hd
    | cons x xs ih=>intro h; exact Nat.max_le.mpr ⟨h x (by simp),ih (by intro y hy; exact h y (by simp [hy]))⟩
  unfold Table.degree
  rw [ha]
  exact Nat.max_eq_left (fold _ (by intro x hx; obtain ⟨e,he,rfl⟩:=List.mem_map.mp hx; exact hc e he))
theorem shape_eq (T : Air.Table) (g w a d s r l : Nat)
    (hw:T.width=w) (ha:T.auxCount g=a) (hd:T.degree g=d)
    (hs:T.numSide true=s) (hr:T.numSide false=r) (hl:T.maxLog=l) :
    ZkFormal.Size.shapeOf g T=⟨w,a,d-1,ZkFormal.Stark.numGroups s g+ZkFormal.Stark.numGroups r g,l⟩ := by
  simp only [ZkFormal.Size.shapeOf,Table.quotCount,hw,ha,hd,hs,hr,hl]
end ZkFormal.NearV3.Candidates.InteractionTriples
