import ZkFormal.Near.Link.NodeSer

/-!
# ZkFormal.Near.Link.Streams — positions in concatenated streams (`RC`, `RF`)
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false

namespace Link

theorem getD_append_left' {l₁ l₂ : List Nat} {i : Nat} (h : i < l₁.length) :
    (l₁ ++ l₂).getD i 0 = l₁.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right' (l₁ l₂ : List Nat) (i : Nat) :
    (l₁ ++ l₂).getD (l₁.length + i) 0 = l₂.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left]

theorem flatMap_split {α β : Type} (f : α → List β) (l : List α) (r : Nat) (hr : r < l.length) :
    l.flatMap f = (l.take r).flatMap f ++ (f l[r] ++ (l.drop (r + 1)).flatMap f) := by
  conv => lhs; rw [← List.take_append_drop r l, List.drop_eq_getElem_cons hr]
  rw [List.flatMap_append, List.flatMap_cons]

theorem getD_flatMap_at {α : Type} (f : α → List Nat) (l : List α) (r : Nat) (hr : r < l.length)
    (i : Nat) (hi : i < (f l[r]).length) :
    ((l.take r).flatMap f).length + i < (l.flatMap f).length ∧
      (l.flatMap f).getD (((l.take r).flatMap f).length + i) 0 = (f l[r]).getD i 0 := by
  rw [flatMap_split f l r hr]
  refine ⟨by simp only [List.length_append]; omega, ?_⟩
  rw [getD_append_right', getD_append_left' hi]

theorem rcOffs_eq (rs : RcptVs) : ∀ r, r ≤ rs.length →
    rcOffs rs r = 12 + ((rs.take r).flatMap RcptV.enc).length
  | 0, _ => rfl
  | r + 1, h => by
    rw [rcOffs, rcOffs_eq rs r (by omega), List.take_add_one, List.getElem?_eq_getElem (by omega),
      Option.toList_some, List.flatMap_append, List.length_append, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    simp; omega

def rfPart (x : RcptV) : List Nat := if x.hr then x.encRefund else []

theorem rfOffs_eq (rs : RcptVs) : ∀ r, r ≤ rs.length →
    rfOffs rs r = 4 + ((rs.take r).flatMap rfPart).length
  | 0, _ => rfl
  | r + 1, h => by
    rw [rfOffs, rfOffs_eq rs r (by omega), List.take_add_one, List.getElem?_eq_getElem (by omega),
      Option.toList_some, List.flatMap_append, List.length_append, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    simp only [Option.getD_some, List.flatMap_cons, List.flatMap_nil, List.append_nil, rfPart]
    split <;> simp <;> omega

theorem filter_flatMap_eq (rs : RcptVs) :
    (rs.filter (·.hr)).flatMap RcptV.encRefund = rs.flatMap rfPart := by
  induction rs with
  | nil => rfl
  | cons x rs ih =>
    simp only [List.filter_cons, List.flatMap_cons, rfPart]
    cases x.hr <;> simp [ih]

theorem rfMsg_eq (pub : List Fp) (rs : RcptVs) :
    rfMsg pub rs = pubBytes pub PV_NREF 4 ++ rs.flatMap rfPart := by
  rw [rfMsg, filter_flatMap_eq]

theorem pubBytes_length (pub : List Fp) (off len : Nat) : (pubBytes pub off len).length = len := by
  simp [pubBytes]

end Link

end ZkFormal.Near
