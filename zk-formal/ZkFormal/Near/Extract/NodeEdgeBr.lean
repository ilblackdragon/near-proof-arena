import ZkFormal.Near.Extract.NodeEdgeMatch

/-!
# ZkFormal.Near.Extract.NodeEdgeBr — branch edges match `edgesOf`
-/

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node ZkFormal.Near

theorem filterMap_eq_flatMap' {α β : Type} (l : List α) (f : α → Option β) :
    l.filterMap f = l.flatMap fun a => (f a).toList := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.filterMap_cons, List.flatMap_cons, ih]; cases f a <;> simp

theorem filterMap_congr'' {α β : Type} {l : List α} {f g : α → Option β} (h : ∀ x, f x = g x) :
    l.filterMap f = l.filterMap g := by
  have : f = g := funext h
  rw [this]

theorem zip_map_range {α : Type} (g : Nat → α) (n : Nat) :
    ((List.range n).map g).zip (List.range n) = (List.range n).map fun j => (g j, j) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.zip_append (by simp), ih]; simp

/-- Child edge of window `w` (row `r`), as the rows provide it. -/
def winE (tr : Trace Fp) (n r : Nat) : List Msg :=
  if cv tr T_NODE r rv = 1 then [[n, 0, cv tr T_NODE r aS, cv tr T_NODE r cres, 0]] else []

def kidEdgeF (n : Nat) : NKid × Nat → Option Msg
  | (.node _ _ cr _ _, j) => some [n, 0, j, cr, 0]
  | _ => none

theorem edgesOf_branch (n : Nat) (S : NodeS) (v : Option NSlot) (kids : List NKid) (m : List Nat)
    (hv : S.v = .branch v kids m) :
    edgesOf n S = (if n = 0 then [[0, 0, SYM_START, S.res, 0]] else []) ++
      ((kids.zip (List.range kids.length)).filterMap (kidEdgeF n) ++
        (match v with | some (.touched _ _) => [[n, 0, SYM_END, n, 0]] | _ => [])) := by
  obtain ⟨sv, sd, sr, su⟩ := S
  simp only at hv; subst hv
  unfold edgesOf; simp only
  rw [filterMap_congr'' (g := kidEdgeF n) (fun x => by obtain ⟨kd, j⟩ := x; cases kd <;> rfl)]
  rcases v with _ | ⟨_ | _⟩ <;> rfl

theorem winMem (o p w : Nat) (hw : w < p) : (o + 2 + 32 * w, 32) ∈ brFL o p := by
  unfold brFL; simp only [List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl (Or.inr ⟨w, hw, rfl⟩)

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

set_option maxHeartbeats 1000000 in
/-- The children's edges in slot order are the windows' edges in window order. -/
theorem kidsEdges (hC : NodeCtx tr s ℓ fl) (hb : tr.cell T_NODE s tb1 + tr.cell T_NODE s tb2 = 1) {n : Nat} :
    ((kidsOf tr s (brOff tr s)).zip (List.range (kidsOf tr s (brOff tr s)).length)).filterMap (kidEdgeF n) =
      (List.range (popN tr s)).flatMap fun w => winE tr n (s + (brOff tr s + 2 + 32 * w)) := by
  have B := brFields hL hC hb
  simp only at B
  rw [← brOff_eq hL hC] at B
  obtain ⟨hfl, -, -, -, -, -, -, hW⟩ := B
  have mem : ∀ p ∈ brFL (brOff tr s) (popN tr s), p ∈ fl := fun p hp => hfl ▸ hp
  have hbv : ∀ j, j < 16 → cv tr T_NODE s (bm j) ≤ 1 := fun j hj => cvb hL (nodeStart hL hC).1 (bm_bool hj)
  -- each window's slot
  have hslot : ∀ w, w < popN tr s → cv tr T_NODE (s + (brOff tr s + 2 + 32 * w)) rv = 1 →
      ∃ j, j < 16 ∧ cv tr T_NODE s (bm j) = 1 ∧ belowN tr s j = w ∧
        cv tr T_NODE (s + (brOff tr s + 2 + 32 * w)) aS = j := by
    intro w hw hrv
    obtain ⟨cj, wj, -⟩ := hW w hw
    have hpS := popN_small hL (nodeStart hL hC).1
    obtain ⟨j, hj, hbj, hbel, hji⟩ := slotOfWin hL hC (pub := pub)
      (mem _ (winMem _ _ _ hw)) cj hb wj (by omega)
    refine ⟨j, hj, hbj, hbel, ?_⟩
    have hr : s + (brOff tr s + 2 + 32 * w) < tr.height T_NODE := by
      have := (fieldAt hL hC (mem _ (winMem _ _ _ hw))).2; omega
    have hgP : tr.cell T_NODE (s + (brOff tr s + 2 + 32 * w)) gP = 1 := by
      have G := linkGates hL hr; simp only at G
      obtain ⟨hF, -⟩ := fieldAt hL hC (mem _ (winMem _ _ _ hw))
      rw [G.1, show tr.cell T_NODE (s + (brOff tr s + 2 + 32 * w)) fs = 1 by simpa using (hF.fs 0 (by omega)).2 rfl, cj,
        of_cv_one hrv]; decide
    have hoℓ : brOff tr s + 2 + 32 * w < ℓ := by
      have := (hC.fields.field _ (mem _ (winMem _ _ _ hw))).2; simp only at this; omega
    have E := (edgeFacts hL hr (pub := pub)).2.2.1 hgP (show tr.cell T_NODE _ tb1 + tr.cell T_NODE _ tb2 = 1 by
      rw [segConst hL hC (by simp [nodeConst]) hoℓ, segConst hL hC (x := tb2) (by simp [nodeConst]) hoℓ, hb])
    simp only at E
    unfold cv; rw [E.2.1, hji, toNat_natCast, Nat.mod_eq_of_lt (by unfold P; omega)]
  rw [show (kidsOf tr s (brOff tr s)).length = 16 by simp [kidsOf]]
  unfold kidsOf
  rw [zip_map_range, filterMap_eq_flatMap', List.flatMap_map, popN_eq]
  unfold belowN
  rw [← flatMap_bits (fun j => cv tr T_NODE s (bm j)) (fun w => winE tr n (s + (brOff tr s + 2 + 32 * w))) 16 hbv]
  apply flatMap_congr'; intro j hj; rw [List.mem_range] at hj
  by_cases hbj : cv tr T_NODE s (bm j) = 1
  · rw [if_pos hbj, if_pos hbj]
    rw [← belowN]
    have hwj : belowN tr s j < popN tr s := by
      rw [popN_eq]; exact belowN_lt (by omega) hbj
    unfold kidOf winE
    by_cases hrv : cv tr T_NODE (s + (brOff tr s + 2 + 32 * belowN tr s j)) rv = 1
    · rw [if_pos hrv, if_pos hrv]
      obtain ⟨j', hj', hbj', hbel', haS⟩ := hslot _ hwj hrv
      have := belowN_inj hbj hbj' hbel'.symm
      subst this
      simp [kidEdgeF, haS]
    · rw [if_neg hrv, if_neg hrv]; simp [kidEdgeF]
  · rw [if_neg hbj, if_neg hbj]; simp [kidEdgeF]

end ZkFormal.Near.NodeProof
