import ZkFormal.Near.Extract.NodePerNode

/-!
# ZkFormal.Near.Extract.NodeViewLists — the node traffic as a concatenation over nodes
-/

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node ZkFormal.Near

theorem perm_flatMap_congr' {α β : Type} (l : List α) (F G : α → List β) (h : ∀ x ∈ l, (F x).Perm (G x)) :
    (l.flatMap F).Perm (l.flatMap G) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons x l ih =>
    simp only [List.flatMap_cons]
    exact List.Perm.append (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem zrf {β : Type} (vs : List NodeS) (F : NodeS → Nat → List β) :
    (vs.zip (List.range vs.length)).flatMap (fun x => F x.1 x.2) =
      (List.range vs.length).flatMap fun q => F (vs.getD q default) q := zip_range_flatMap vs F

theorem zrf' {β : Type} (vs : List NodeS) (G : NodeS × Nat → List β) (F : NodeS → Nat → List β)
    (h : ∀ x, G x = F x.1 x.2) :
    (vs.zip (List.range vs.length)).flatMap G = (List.range vs.length).flatMap fun q => F (vs.getD q default) q := by
  rw [flatMap_congr' (fun x _ => h x)]; exact zrf vs F

theorem sends_eq (vs : List NodeS) (bb : Nat) :
    nodeSends vs bb = (List.range vs.length).flatMap fun n => pnSend n (vs.getD n default) bb := by
  unfold nodeSends pnSend
  by_cases h0 : bb = B_BYTES
  · simp only [if_pos h0]
    exact zrf' vs _ (fun S n => emitAt (msgId K_NPRE n) 0 (S.v.ser false) ++ emitAt (msgId K_NPOST n) 0 (S.v.ser true))
      (fun x => rfl)
  by_cases h2 : bb = B_PARENT
  · simp only [if_neg h0, if_pos h2]
    exact zrf' vs _ (fun S _ => pnParS S) (fun x => rfl)
  by_cases h4 : bb = B_EDGE
  · simp only [if_neg h0, if_neg h2, if_pos h4]
    exact zrf' vs _ (fun S n => (edgesOf n S).map (· ++ [0])) (fun x => rfl)
  simp only [if_neg h0, if_neg h2, if_neg h4]; simp

theorem zip_range'_map {α β : Type} [Inhabited α] (f : α → Nat → β) : ∀ (l : List α) (k : Nat),
    (l.zip (List.range' k l.length)).map (fun x => f x.1 x.2) = (List.range l.length).map fun q => f (l.getD q default) (k + q)
  | [], k => rfl
  | a :: l, k => by
    rw [List.length_cons, List.range'_succ, List.zip_cons_cons, List.map_cons, zip_range'_map f l (k + 1),
      List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [List.getD_cons_zero, Nat.add_zero, List.cons.injEq, true_and]
    apply List.map_congr_left; intro q _; simp only [Function.comp, List.getD_cons_succ]; congr 1; omega

theorem drop1_map_eq {α β : Type} [Inhabited α] (l : List α) (G : α × Nat → β) (f : α → Nat → β)
    (hG : ∀ x, G x = f x.1 x.2) :
    ((l.zip (List.range l.length)).drop 1).map G =
      (List.range l.length).flatMap fun n => if n = 0 then [] else [f (l.getD n default) n] := by
  rw [List.map_congr_left (fun x _ => hG x)]
  cases l with
  | nil => rfl
  | cons a l =>
    have hr : List.range (l.length + 1) = 0 :: List.range' 1 l.length := by
      rw [List.range_eq_range', List.range'_succ]
    rw [List.length_cons, hr, List.zip_cons_cons, List.drop_one, List.tail_cons,
      zip_range'_map f l 1, List.flatMap_cons, if_pos rfl, List.nil_append, List.range'_eq_map_range,
      List.flatMap_map, map_eq_flatMap]
    apply flatMap_congr'; intro q _
    simp only [show 1 + q = q + 1 by omega, List.getD_cons_succ, Nat.add_one_ne_zero, if_false]

end ZkFormal.Near.NodeProof

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node ZkFormal.Near

theorem roots_front {α : Type} (k : Nat) (R : Nat → List α) (D : Nat → List α) :
    (List.range (k + 1)).flatMap (fun n => (if n = 0 then R n else []) ++ D n) = R 0 ++ (List.range (k + 1)).flatMap D := by
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_cons, if_pos rfl, List.flatMap_map, List.flatMap_map,
    List.append_assoc]
  congr 2

theorem recvs_eq (vs : List NodeS) (pub : List Fp) (bb : Nat) (hne : vs ≠ []) :
    nodeRecvs vs pub bb = (List.range vs.length).flatMap fun n => pnRecv pub n (vs.getD n default) bb := by
  unfold nodeRecvs pnRecv
  by_cases h1 : bb = B_DIGEST
  · simp only [if_pos h1]
    obtain ⟨k, hk⟩ : ∃ k, vs.length = k + 1 := ⟨vs.length - 1, by
      have : vs.length ≠ 0 := fun h => hne (List.length_eq_zero_iff.mp h); omega⟩
    rw [hk, roots_front, ← hk]
    congr 1
    · unfold roots0
      rw [show vs.headD default = vs.getD 0 default by cases vs <;> simp at hne ⊢]
    · exact zrf' vs _ (fun S n => pnDig n S) (fun x => rfl)
  by_cases h2 : bb = B_PARENT
  · simp only [if_neg h1, if_pos h2]
    rw [drop1_map_eq vs _ (fun S n => [n, S.depth, (S.v.ser false).length, S.res]) (fun x => rfl)]
    apply flatMap_congr'; intro n _; unfold pnParR; split <;> rfl
  by_cases h3 : bb = B_VSLOT
  · simp only [if_neg h1, if_neg h2, if_pos h3]
    rw [ZkFormal.Near.NodeProof.filterMap_eq_flatMap']
    exact zrf' vs _ (fun S n => pnVs n S) (fun x => by obtain ⟨S, n⟩ := x; unfold pnVs; split <;> simp_all)
  by_cases h4 : bb = B_EDGE
  · simp only [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
    exact zrf' vs _ (fun S n => ((edgesOf n S).zip S.uses).map fun (e, u) => e ++ [u]) (fun x => rfl)
  simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4]; simp

end ZkFormal.Near.NodeProof
