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

def endE (n : Nat) (v : Option NSlot) : List Msg := match v with
  | some (.touched _ _) => [[n, 0, SYM_END, n, 0]]
  | _ => []

theorem edgesOf_branch (n : Nat) (S : NodeS) (v : Option NSlot) (kids : List NKid) (m : List Nat)
    (hv : S.v = .branch v kids m) :
    edgesOf n S = (if n = 0 then [[0, 0, SYM_START, S.res, 0]] else []) ++
      ((kids.zip (List.range kids.length)).filterMap (kidEdgeF n) ++ endE n v) := by
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
theorem winAS (hC : NodeCtx tr s ℓ fl) (hb : tr.cell T_NODE s tb1 + tr.cell T_NODE s tb2 = 1) :
    ∀ w, w < popN tr s → cv tr T_NODE (s + (brOff tr s + 2 + 32 * w)) rv = 1 →
      ∃ j, j < 16 ∧ cv tr T_NODE s (bm j) = 1 ∧ belowN tr s j = w ∧
        cv tr T_NODE (s + (brOff tr s + 2 + 32 * w)) aS = j := by
  have B := brFields hL hC hb
  simp only at B
  rw [← brOff_eq hL hC] at B
  obtain ⟨hfl, -, -, -, -, -, -, hW⟩ := B
  have mem : ∀ p ∈ brFL (brOff tr s) (popN tr s), p ∈ fl := fun p hp => hfl ▸ hp
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
  have hslot := winAS hL hC hb (pub := pub)
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

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node ZkFormal.Near

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

set_option maxHeartbeats 2000000 in
theorem brEdges (hC : NodeCtx tr s ℓ fl) (hb : tr.cell T_NODE s tb1 + tr.cell T_NODE s tb2 = 1) {n : Nat}
    (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp)) (hnP : n < P) (h0 : s = 0 ↔ n = 0) :
    (canonE (rowEdgesN tr pub s ℓ)).map (·.1) = edgesOf n (nodeSOf tr pub s ℓ) := by
  have B := brFields hL hC hb
  simp only at B
  rw [← brOff_eq hL hC] at B
  obtain ⟨hfl, hℓ, sT, sVV, sB, -, sM, hW⟩ := B
  have mem : ∀ p ∈ brFL (brOff tr s) (popN tr s), p ∈ fl := fun p hp => hfl ▸ hp
  obtain ⟨hr0, ha0⟩ := nodeStart hL hC
  have T := typeSumNat hL hr0 ha0
  have hcb : cv tr T_NODE s tb1 + cv tr T_NODE s tb2 = 1 := by
    have e := hb
    rw [cell_eq_cast tr T_NODE s tb1, cell_eq_cast tr T_NODE s tb2, ← natCast_add] at e
    have := cvb hL hr0 (x := tb1) (by simp [boolCols]); have := cvb hL hr0 (x := tb2) (by simp [boolCols])
    exact fp_cast_eq (b := 1) (by unfold P; omega) (by unfold P; omega) (e.trans rfl)
  have hcl : cv tr T_NODE s tl = 0 := by omega
  have hce : cv tr T_NODE s te = 0 := by omega
  have htl : tr.cell T_NODE s tl = 0 := of_cv_zero hcl
  have hoff : brOff tr s = 1 ∨ brOff tr s = 37 := by unfold brOff; split <;> simp
  -- windows
  have FW : ∀ j, j < popN tr s → (List.range' (s + (brOff tr s + 2 + 32 * j)) 32).flatMap (rowEdgeN tr pub) =
      if cv tr T_NODE (s + (brOff tr s + 2 + 32 * j)) rv = 1 then
        [([n, 0, cv tr T_NODE (s + (brOff tr s + 2 + 32 * j)) aS, cv tr T_NODE (s + (brOff tr s + 2 + 32 * j)) cres, 0],
          cv tr T_NODE (s + (brOff tr s + 2 + 32 * j)) mA)] else [] := by
    intro j hj
    obtain ⟨cj, -, -⟩ := hW j hj
    have hm := mem _ (winMem _ _ _ hj)
    rw [winEdges hL hC hm (by omega) (by rw [cj, stOnly hL (fieldRow' hL hC hm) (segAct hL hC (fieldIn hC hm)) cj
      (by simp [states]) (y := sVH) (by simp [states]) (by decide)]; decide), chEdge hL hC hm (by omega) cj hn hnP htl, hce]
    simp
  have FB := plainEdges hL hC (pub := pub) (L := 2) (mem _ (by simp [brFL])) (by rcases hoff with h | h <;> omega) sB
    (by simp [states]) (by decide) (by decide) (by decide) (by decide)
  have FM := plainEdges hL hC (pub := pub) (L := 8) (mem _ (by simp [brFL])) (by omega) sM (by simp [states])
    (by decide) (by decide) (by decide) (by decide)
  have hWin := flatMap_congr' (l := List.range (popN tr s)) (fun j hj => FW j (List.mem_range.mp hj))
  generalize hWdef : (List.range (popN tr s)).flatMap (fun j =>
      if cv tr T_NODE (s + (brOff tr s + 2 + 32 * j)) rv = 1 then
        [([n, 0, cv tr T_NODE (s + (brOff tr s + 2 + 32 * j)) aS, cv tr T_NODE (s + (brOff tr s + 2 + 32 * j)) cres, 0],
          cv tr T_NODE (s + (brOff tr s + 2 + 32 * j)) mA)] else []) = W at hWin
  have Wfst : W.map (·.1) = (List.range (popN tr s)).flatMap fun w => winE tr n (s + (brOff tr s + 2 + 32 * w)) := by
    rw [← hWdef, List.map_flatMap]; apply flatMap_congr'; intro j _; unfold winE; split <;> simp
  have hWsym : ∀ e ∈ W, e.1.getD 2 0 ≠ SYM_END := by
    rw [← hWdef]; intro e he
    rw [List.mem_flatMap] at he; obtain ⟨j, hj, he⟩ := he; rw [List.mem_range] at hj
    split at he
    · rename_i hrv
      simp at he; subst he; simp
      obtain ⟨j', hj', -, -, haS⟩ := winAS hL hC hb (pub := pub) j hj hrv
      rw [haS]; unfold SYM_END; omega
    · simp at he
  have hS : ∀ e ∈ startE tr s, e.1.getD 2 0 ≠ SYM_END := by
    intro e he; unfold startE at he; split at he
    · simp at he; subst he; simp [SYM_START, SYM_END]
    · simp at he
  have hkids := kidsEdges hL hC hb (n := n) (pub := pub)
  unfold nodeSOf
  have hVB : nodeVOf tr s = .branch (if cv tr T_NODE s tb2 = 1 then some (slotOf tr s (s + 1) (s + 5)) else none)
      (kidsOf tr s (brOff tr s)) (rowsB tr b (s + (brOff tr s + 2 + 32 * popN tr s)) 8) := by
    unfold nodeVOf; simp only [show ¬ cv tr T_NODE s tl = 1 by omega, show ¬ cv tr T_NODE s te = 1 by omega, if_false]
  rw [edgesOf_branch n _ _ _ _ hVB, hkids]
  simp only
  rcases hoff with ho | ho
  · -- b1: no value
    have hb2 : cv tr T_NODE s tb2 ≠ 1 := by intro h; unfold brOff at ho; rw [if_pos h] at ho; omega
    have R : rowEdgesN tr pub s ℓ = startE tr s ++ W := by
      unfold rowEdgesN; rw [rowsFields hL hC, hfl]; unfold brFL
      simp only [if_pos ho, List.append_nil, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_append,
        List.flatMap_map, List.flatMap_nil]
      rw [tagRows hL hC, show (List.range' (s + brOff tr s) 2).flatMap (rowEdgeN tr pub) = [] from FB, hWin, FM]
      simp
    rw [R, show startE tr s ++ W = (startE tr s ++ W) ++ [] by simp,
      canonE_split _ [] (fun e he => by rcases List.mem_append.mp he with h | h; exact hS e h; exact hWsym e h)
        (by simp), List.append_nil, List.map_append, Wfst, if_neg hb2]
    unfold startE endE
    congr 1
    · by_cases hs : s = 0
      · rw [if_pos hs, if_pos (h0.1 hs)]; subst hs; simp
      · rw [if_neg hs, if_neg (fun h => hs (h0.2 h))]; simp
    · simp
  · -- b2: value slot
    have hb2 : cv tr T_NODE s tb2 = 1 := by
      unfold brOff at ho; split at ho
      · assumption
      · omega
    obtain ⟨sV, sH⟩ := sVV ho
    have FV := plainEdges hL hC (pub := pub) (L := 4) (mem _ (by simp [brFL, ho])) (by omega) sV (by simp [states])
      (by decide) (by decide) (by decide) (by decide)
    have hm5 : (5, 32) ∈ fl := mem _ (by simp [brFL, ho])
    have FH : (List.range' (s + 5) 32).flatMap (rowEdgeN tr pub) =
        if cv tr T_NODE s tv = 1 then [([n, 0, SYM_END, n, 0], cv tr T_NODE (s + 5) mA)] else [] := by
      rw [winEdges hL hC hm5 (by omega) (by rw [sH, stOnly hL (fieldRow' hL hC hm5) (segAct hL hC (fieldIn hC hm5)) sH
        (by simp [states]) (y := sCH) (by simp [states]) (by decide)]; decide),
        vhEdge hL hC hm5 (by omega) sH hn hnP (fun h => absurd h (by omega)),
        if_neg (show ¬ cv tr T_NODE s tl = 1 by omega)]
    have R : rowEdgesN tr pub s ℓ = startE tr s ++
        ((if cv tr T_NODE s tv = 1 then [([n, 0, SYM_END, n, 0], cv tr T_NODE (s + 5) mA)] else []) ++ W) := by
      unfold rowEdgesN; rw [rowsFields hL hC, hfl]; unfold brFL
      simp only [if_neg (show ¬ brOff tr s = 1 by omega), List.cons_append, List.nil_append, List.flatMap_cons,
        List.flatMap_append, List.flatMap_map, List.flatMap_nil, List.append_nil]
      rw [tagRows hL hC, FV, FH, show (List.range' (s + brOff tr s) 2).flatMap (rowEdgeN tr pub) = [] from FB, hWin, FM]
      simp
    rw [R, canonE_swap _ _ _ hS (fun e he => by split at he <;> simp at he; subst he; simp) hWsym,
      List.map_append, List.map_append, Wfst, if_pos hb2]
    unfold startE slotOf endE
    simp only [List.append_assoc]
    congr 1
    · by_cases hs : s = 0
      · rw [if_pos hs, if_pos (h0.1 hs)]; subst hs; simp
      · rw [if_neg hs, if_neg (fun h => hs (h0.2 h))]; simp
    · congr 1
      by_cases htv : cv tr T_NODE s tv = 1
      · rw [if_pos htv, if_pos htv]; simp
      · rw [if_neg htv, if_neg htv]; simp

end ZkFormal.Near.NodeProof
