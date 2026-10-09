import ZkFormal.NearV3.Extract.Node.PerNode

/-!
# ZkFormal.Near.Extract.NodeViewLists — the node traffic as a concatenation over nodes
-/

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

theorem perm_flatMap_congr' {α β : Type} (l : List α) (F G : α → List β) (h : ∀ x ∈ l, (F x).Perm (G x)) :
    (l.flatMap F).Perm (l.flatMap G) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons x l ih =>
    simp only [List.flatMap_cons]
    exact List.Perm.append (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem zrf {β : Type} (vs : List NodeS3) (F : NodeS3 → Nat → List β) :
    (vs.zip (List.range vs.length)).flatMap (fun x => F x.1 x.2) =
      (List.range vs.length).flatMap fun q => F (vs.getD q default) q := zip_range_flatMap vs F

theorem zrf' {β : Type} (vs : List NodeS3) (G : NodeS3 × Nat → List β) (F : NodeS3 → Nat → List β)
    (h : ∀ x, G x = F x.1 x.2) :
    (vs.zip (List.range vs.length)).flatMap G = (List.range vs.length).flatMap fun q => F (vs.getD q default) q := by
  rw [flatMap_congr' (fun x _ => h x)]; exact zrf vs F

theorem sends_eq (vs : List NodeS3) (bb : Nat) (hb : bb ≠ B_SIZE) :
    nodeSends3 vs bb = (List.range vs.length).flatMap fun n => pnSend n (vs.getD n default) bb := by
  unfold nodeSends3 pnSend
  by_cases h0 : bb = B_BYTES
  · simp only [if_pos h0]
    exact zrf' vs _ (fun S n => emitAt (msgId K_NPRE n) 0 (S.v.ser false) ++ emitAt (msgId K_NPOST n) 0 (S.v.ser true))
      (fun x => rfl)
  by_cases h2 : bb = B_PARENT
  · simp only [if_neg h0, if_pos h2]
    exact zrf' vs _ (fun S _ => pnParS S) (fun x => rfl)
  by_cases h3 : bb = B_VPARENT
  · simp only [if_neg h0, if_neg h2, if_pos h3]
    exact zrf' vs _ (fun S _ => pnVpar S) (fun x => rfl)
  by_cases h4 : bb = B_EDGE
  · simp only [if_neg h0, if_neg h2, if_neg h3, if_pos h4]
    exact zrf' vs _ (fun S n => (edgesOf3 n S).map (· ++ [0])) (fun x => rfl)
  by_cases h5 : bb = B_BMAP
  · simp only [if_neg h0, if_neg h2, if_neg h3, if_neg h4, if_pos h5]
    exact zrf' vs _ (fun S n => pnBmS n S) (fun x => rfl)
  by_cases h6 : bb = B_DIGS
  · simp only [if_neg h0, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6]
    exact zrf' vs _ (fun S _ => pnDigs S) (fun x => rfl)
  by_cases h7 : bb = B_ENT
  · simp only [if_neg h0, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_pos h7]
    exact zrf' vs _ (fun S n => pnEntS n S) (fun x => rfl)
  by_cases h8 : bb = B_UPB
  · simp only [if_neg h0, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg hb, if_pos h8]
    exact zrf' vs _ (fun S n => upbOf n S fun _ => 0) (fun x => rfl)
  simp only [if_neg h0, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg hb, if_neg h8]; simp

theorem sends_size_nil (vs : List NodeS3) :
    (List.range vs.length).flatMap (fun n => pnSend n (vs.getD n default) B_SIZE) = [] := by
  apply flatMap_eq_nil'; intro n _; unfold pnSend; simp [B_SIZE, B_BYTES, B_PARENT, B_VPARENT, B_EDGE, B_BMAP, B_DIGS, B_ENT, B_UPB, B_VSLOT]

theorem recvs_eq (vs : List NodeS3) (bb : Nat) :
    nodeRecvs3 vs bb = (List.range vs.length).flatMap fun n => pnRecv n (vs.getD n default) bb := by
  unfold nodeRecvs3 pnRecv
  by_cases h1 : bb = B_DIGEST
  · simp only [if_pos h1]
    exact zrf' vs _ (fun S _ => pnDig S) (fun x => rfl)
  by_cases h2 : bb = B_PARENT
  · simp only [if_neg h1, if_pos h2]
    rw [map_eq_flatMap]
    exact zrf' vs _ (fun S n => pnParR n S) (fun x => rfl)
  by_cases h4 : bb = B_EDGE
  · simp only [if_neg h1, if_neg h2, if_pos h4]
    exact zrf' vs _ (fun S n => ((edgesOf3 n S).zip S.uses).map fun (e, u) => e ++ [u]) (fun x => rfl)
  by_cases h5 : bb = B_BMAP
  · simp only [if_neg h1, if_neg h2, if_neg h4, if_pos h5]
    exact zrf' vs _ (fun S n => pnBmR n S) (fun x => rfl)
  by_cases h6 : bb = B_DUP
  · simp only [if_neg h1, if_neg h2, if_neg h4, if_neg h5, if_pos h6]
    rw [filterMap_eq_flatMap']
    exact zrf' vs _ (fun S n => pnDup n S) (fun x => by obtain ⟨S, n⟩ := x; unfold pnDup; split <;> simp_all)
  by_cases h7 : bb = B_ENT
  · simp only [if_neg h1, if_neg h2, if_neg h4, if_neg h5, if_neg h6, if_pos h7]
    exact zrf' vs _ (fun S _ => pnEntR S) (fun x => rfl)
  by_cases h8 : bb = B_UPB
  · simp only [if_neg h1, if_neg h2, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_pos h8]
    exact zrf' vs _ (fun S n => upbOf n S fun p => S.mU.getD p 0) (fun x => rfl)
  by_cases h9 : bb = B_VSLOT
  · simp only [if_neg h1, if_neg h2, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_pos h9]
    exact zrf' vs _ (fun S _ => pnVslot S) (fun x => rfl)
  simp only [if_neg h1, if_neg h2, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9]; simp

end ZkFormal.NearV3.NodeProof3
