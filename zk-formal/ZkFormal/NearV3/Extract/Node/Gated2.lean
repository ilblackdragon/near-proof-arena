import ZkFormal.NearV3.Extract.Node.Gated

/-!
# ZkFormal.Near.Extract.NodeGated2 — per-node gated traffic against the view
-/

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

/-! ## Per-node view lists -/

def pnDig (n : Nat) (S : NodeS) : List Msg :=
  (S.v.revealed.flatMap fun (c, l, _, pre, po) => [digMsg (msgId K_NPRE c) l pre, digMsg (msgId K_NPOST c) l po]) ++
  (match S.v with
   | .leaf _ (.touched pre po) _ | .branch (some (.touched pre po)) _ _ =>
     [digMsg (msgId K_VPRE n) 72 pre, digMsg (msgId K_VPOST n) 72 po]
   | _ => [])

def pnParS (S : NodeS) : List Msg := S.v.revealed.map fun (c, l, r, _, _) => [c, S.depth + 1, l, r]

def pnParR (n : Nat) (S : NodeS) : List Msg := if n = 0 then [] else [[n, S.depth, (S.v.ser false).length, S.res]]

def pnVs (n : Nat) (S : NodeS) : List Msg := if S.v.touched then [[n]] else []

def roots0 (S : NodeS) (pub : List Fp) : List Msg :=
  [digMsg K_NPRE (S.v.ser false).length ((List.range 32).map fun j => pubNat pub (PV_PRE + j)),
   digMsg K_NPOST (S.v.ser false).length ((List.range 32).map fun j => pubNat pub (PV_POST + j))]

theorem touched_iff (tr : Trace Fp) (s : Nat) (h0 : cv tr T_NODE s tv * (cv tr T_NODE s tb1 + cv tr T_NODE s te) = 0)
    (hT : cv tr T_NODE s tl + cv tr T_NODE s te + cv tr T_NODE s tb1 + cv tr T_NODE s tb2 = 1) :
    (nodeVOf tr s).touched = (cv tr T_NODE s tv == 1) := by
  unfold nodeVOf
  by_cases h1 : cv tr T_NODE s tl = 1
  · rw [if_pos h1]; unfold slotOf; by_cases ht : cv tr T_NODE s tv = 1 <;> simp [ht, NodeV.touched]
  · rw [if_neg h1]
    by_cases h2 : cv tr T_NODE s te = 1
    · rw [if_pos h2]
      have : cv tr T_NODE s tv = 0 := by
        rcases Nat.eq_zero_or_pos (cv tr T_NODE s tv) with h | h
        · exact h
        · exfalso; have := Nat.mul_le_mul_left (cv tr T_NODE s tv) (show 1 ≤ cv tr T_NODE s tb1 + cv tr T_NODE s te by omega)
          omega
      simp [NodeV.touched, this]
    · rw [if_neg h2]
      by_cases hb : cv tr T_NODE s tb2 = 1
      · rw [if_pos hb]; unfold slotOf; by_cases ht : cv tr T_NODE s tv = 1 <;> simp [ht, NodeV.touched]
      · rw [if_neg hb]
        have : cv tr T_NODE s tv = 0 := by
          rcases Nat.eq_zero_or_pos (cv tr T_NODE s tv) with h | h
          · exact h
          · exfalso; have := Nat.mul_le_mul_left (cv tr T_NODE s tv) (show 1 ≤ cv tr T_NODE s tb1 + cv tr T_NODE s te by omega)
            omega
        simp [NodeV.touched, this]

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

theorem flHead (hC : NodeCtx tr s ℓ fl) : ∃ rest, fl = (0, 1) :: rest ∧ ∀ p ∈ rest, 0 < p.1 := by
  obtain ⟨h0, f0, sT⟩ := firstField hL hC
  have l0 := (lens hL hC h0).1 (by rw [f0, Nat.add_zero]; exact sT)
  have hc := hC.fields.consec
  match fl, h0, hc with
  | (a, b') :: rest, _, hc' =>
    simp at f0 l0; subst f0; subst l0
    refine ⟨rest, rfl, fun p hp => ?_⟩
    have := seg_le_end rest 1 hc'.2 p hp
    omega

theorem tagOnly (hC : NodeCtx tr s ℓ fl) {bb : Nat} {sd : Bool} (hg : Gated bb sd)
    (hq : ∀ p ∈ fl, 0 < p.1 → rowT tr pub (s + p.1) bb sd = []) :
    (List.range' s ℓ).flatMap (fun r => rowT tr pub r bb sd) = rowT tr pub s bb sd := by
  rw [gatedFields hL hC hg]
  obtain ⟨rest, hfl, hpos⟩ := flHead hL hC
  have : rest.flatMap (fun p => rowT tr pub (s + p.1) bb sd) = [] := by
    rw [List.flatMap_eq_nil_iff]; intro p hp; exact hq p (by rw [hfl]; simp [hp]) (hpos p hp)
  rw [hfl, List.flatMap_cons, this, List.append_nil, Nat.add_zero]

theorem lenCell (hC : NodeCtx tr s ℓ fl) : tr.cell T_NODE s len = ((ℓ : Nat) : Fp) := by
  have hp := hC.seg.1
  have hb := hC.bound
  have hl := hC.seg.2.2.1; rw [one_iff] at hl
  have E := ((rowFacts hL (by omega)).2.2.2.2.1 hl).2.2.2
  have hpos := counter_of (f := fun q => tr.cell T_NODE q Node.pos) (s := s) (ℓ := ℓ) (v0 := 0)
    (by have := hC.seg.2.1; rw [one_iff] at this
        show tr.cell T_NODE s Node.pos = _
        rw [((rowFacts hL (by omega)).2.2.2.1 this).2.2.2.1]; rfl)
    (fun q h1 h2 => by
      have ha := hC.seg.2.2.2.1 q h1 (by omega); rw [one_iff] at ha
      have hl' := zero_of hL (by omega) (by simp [boolCols]) (hC.seg.2.2.2.2.2 q h1 h2)
      exact (inNode hL (by omega) ha hl').2.2.1) (s + ℓ - 1) (by omega) (by omega)
  rw [hpos, show s + ℓ - 1 = s + (ℓ - 1) by omega, segConst hL hC (by simp [nodeConst]) (by omega)] at E
  rw [← E, show ((1 : Fp)) = ((1 : Nat) : Fp) from rfl, ← natCast_add]; congr 1; omega

/-- PARENT receive of one node. -/
theorem nodeParR (hC : NodeCtx tr s ℓ fl) {n : Nat} (S : NodeS) (hv : S.v = nodeVOf tr s)
    (hd : S.depth = cv tr T_NODE s depth) (hr : S.res = cv tr T_NODE s res)
    (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp)) (h0 : s = 0 ↔ n = 0) :
    (List.range' s ℓ).flatMap (fun r => rowT tr pub r B_PARENT false) = (pnParR n S).map Msg.toFp := by
  rw [tagOnly hL hC (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) (fun p hp h => (innerStart hL hC hp h).1)]
  rw [(tagStart hL hC).2.2.1, pnParR, hv, hd, hr, ← (nodeSer hL hC).1, rowsB_length]
  by_cases hs : s = 0
  · rw [if_pos hs, if_pos (h0.1 hs)]; simp [gate]
  · rw [if_neg hs, if_neg (fun h => hs (h0.2 h))]
    simp [gate, Msg.toFp, hn, lenCell hL hC, ← natCast_eq, cast_cv]

/-- VSLOT receive of one node. -/
theorem nodeVs (hC : NodeCtx tr s ℓ fl) {n : Nat} (S : NodeS) (hv : S.v = nodeVOf tr s)
    (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp)) :
    (List.range' s ℓ).flatMap (fun r => rowT tr pub r B_VSLOT false) = (pnVs n S).map Msg.toFp := by
  rw [tagOnly hL hC (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) (fun p hp h => (innerStart hL hC hp h).2.1)]
  rw [(tagStart hL hC).2.2.2, pnVs, hv]
  obtain ⟨hr0, ha0⟩ := nodeStart hL hC
  have T := typeSumNat hL hr0 ha0
  have F := (flags hL hr0).2.2.1
  have hz : cv tr T_NODE s tv * (cv tr T_NODE s tb1 + cv tr T_NODE s te) = 0 := by
    rw [cell_eq_cast tr T_NODE s tv, cell_eq_cast tr T_NODE s tb1, cell_eq_cast tr T_NODE s te, ← natCast_add,
      ← natCast_mul] at F
    have b1 := cvb hL hr0 (x := tv) (by simp [boolCols])
    have b2 := cvb hL hr0 (x := tb1) (by simp [boolCols])
    have b3 := cvb hL hr0 (x := te) (by simp [boolCols])
    have := Nat.mul_le_mul b1 (show cv tr T_NODE s tb1 + cv tr T_NODE s te ≤ 2 by omega)
    exact fp_cast_eq (by unfold P; omega) (by unfold P; omega) (F.trans rfl)
  rw [touched_iff tr s hz (by omega)]
  rcases isBool hL hr0 (x := tv) (by simp [boolCols]) with h | h
  · rw [h, cv_zero h]; simp [gate]
  · rw [h, cv_one h]; simp [gate, Msg.toFp, hn, ← natCast_eq]

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

theorem cell_eq_cast' (x : Fp) : ((x.toNat : Nat) : Fp) = x := by rw [natCast_eq, Fp.ofNat_toNat]

theorem flatMap_filterMap {α β γ : Type} (l : List α) (f : α → Option β) (g : β → List γ) :
    (l.filterMap f).flatMap g = l.flatMap fun a => (f a).toList.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filterMap_cons, List.flatMap_cons]
    cases h : f a <;> simp [ih, h]

def revF : NKid → Option (Nat × Nat × Nat × List Nat × List Nat)
  | .node c l r pre po => some (c, l, r, pre, po)
  | _ => none

theorem revealed_branch (v : Option NSlot) (kids : List NKid) (m : List Nat) :
    (NodeV.branch v kids m).revealed = kids.filterMap revF := by
  simp only [NodeV.revealed]; congr

theorem revF_digs (kd : NKid) :
    (revF kd).toList.flatMap (fun x : Nat × Nat × Nat × List Nat × List Nat =>
      [digMsg (msgId K_NPRE x.1) x.2.1 x.2.2.2.1, digMsg (msgId K_NPOST x.1) x.2.1 x.2.2.2.2]) = revDigs kd := by
  cases kd <;> simp [revF, revDigs]

theorem revF_par (d : Nat) (kd : NKid) :
    (revF kd).toList.flatMap (fun x : Nat × Nat × Nat × List Nat × List Nat => [[x.1, d + 1, x.2.1, x.2.2.1]]) =
      revPar d kd := by
  cases kd <;> simp [revF, revPar]

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

theorem kidsFlat (hC : NodeCtx tr s ℓ fl) {α : Type} (o : Nat) (G : NKid → List α) (hG : G .none = []) :
    (kidsOf tr s o).flatMap G = (List.range (popN tr s)).flatMap fun w => G (kidOf tr (s + (o + 2 + 32 * w))) := by
  have hbv : ∀ j, j < 16 → cv tr T_NODE s (bm j) ≤ 1 := fun j hj => cvb hL (nodeStart hL hC).1 (bm_bool hj)
  unfold kidsOf; rw [List.flatMap_map]
  have := flatMap_bits (fun j => cv tr T_NODE s (bm j)) (fun w => G (kidOf tr (s + (o + 2 + 32 * w)))) 16 hbv
  rw [popN_eq]; unfold belowN; rw [← this]
  apply flatMap_congr'; intro j _
  split <;> simp [hG]

/-- The roots (node 0's DIGEST lookups of the claimed state roots). -/
theorem tagDig (hC : NodeCtx tr s ℓ fl) {n : Nat} (S : NodeS) (hv : S.v = nodeVOf tr s) (h0 : s = 0 ↔ n = 0) :
    rowT tr pub s B_DIGEST false = (if n = 0 then roots0 S pub else []).map Msg.toFp := by
  rw [(tagStart hL hC).2.1]
  by_cases hs : s = 0
  · rw [if_pos hs, if_pos (h0.1 hs), roots0, hv, ← (nodeSer hL hC).1, rowsB_length, lenCell hL hC]
    simp [gate, Msg.toFp, digMsg, pubNat, ← natCast_eq, Function.comp_def]
    exact ⟨fun a _ => (cell_eq_cast' _).symm, fun a _ => (cell_eq_cast' _).symm⟩
  · rw [if_neg hs, if_neg (fun h => hs (h0.2 h))]; simp [gate]

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

theorem revealed_ext (k : List Nat) (kid : NKid) (m : List Nat) : (NodeV.ext k kid m).revealed = (revF kid).toList := by
  cases kid <;> rfl

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

set_option maxHeartbeats 1000000 in
/-- DIGEST receive and PARENT send of one node. -/
theorem nodeDigPar (hC : NodeCtx tr s ℓ fl) {n : Nat} (S : NodeS) (hv : S.v = nodeVOf tr s)
    (hd : S.depth = cv tr T_NODE s depth) (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp)) (h0 : s = 0 ↔ n = 0) :
    ((List.range' s ℓ).flatMap (fun r => rowT tr pub r B_DIGEST false)).Perm
      (((if n = 0 then roots0 S pub else []) ++ pnDig n S).map Msg.toFp) ∧
    (List.range' s ℓ).flatMap (fun r => rowT tr pub r B_PARENT true) = (pnParS S).map Msg.toFp := by
  have gD : Gated B_DIGEST false := Or.inl ⟨rfl, rfl⟩
  have gP : Gated B_PARENT true := Or.inr (Or.inl ⟨rfl, rfl⟩)
  have TD := tagDig hL hC S hv h0 (pub := pub)
  have TP := (tagStart hL hC (pub := pub)).1
  obtain ⟨hr0, ha0⟩ := nodeStart hL hC
  have T := typeSumNat hL hr0 ha0
  simp only [pnDig, pnParS, hv, hd, List.map_append]
  by_cases h1 : cv tr T_NODE s tl = 1
  · -- leaf
    have ht := of_cv_one h1
    obtain ⟨-, -, hfl, -, -, -, -, -, -, sVH, -⟩ := leafFields hL hC ht
    have hm : (9 + cv tr T_NODE s hplen, 32) ∈ fl := hfl ▸ (by simp [leafFL])
    obtain ⟨VP, VD⟩ := vhView hL hC hm (by omega) sVH hn (pub := pub)
    rw [leafGated hL hC ht gD, leafGated hL hC ht gP, TD, TP, VP, VD]
    unfold nodeVOf; rw [if_pos h1]
    unfold slotOf
    by_cases htv : cv tr T_NODE s tv = 1
    · rw [if_pos htv, if_pos htv]; simp [NodeV.revealed]
    · rw [if_neg htv, if_neg htv]; simp [NodeV.revealed]
  by_cases h2 : cv tr T_NODE s te = 1
  · -- extension
    have ht := of_cv_one h2
    obtain ⟨-, -, hfl, -, -, -, -, -, sC, -⟩ := extFields hL hC ht
    have hm : (5 + cv tr T_NODE s hplen, 32) ∈ fl := hfl ▸ (by simp [extFL])
    obtain ⟨CD, CP⟩ := chView hL hC hm (by omega) sC (pub := pub)
    rw [extGated hL hC ht gD, extGated hL hC ht gP, TD, TP, CD, CP]
    unfold nodeVOf; rw [if_neg h1, if_pos h2]
    simp only [revealed_ext, revF_digs, List.map_nil, List.nil_append, List.append_nil]
    refine ⟨List.Perm.refl _, ?_⟩
    generalize kidOf tr (s + (5 + cv tr T_NODE s hplen)) = kd
    cases kd <;> simp [revPar, revF]
  -- branch
  have hb : tr.cell T_NODE s tb1 + tr.cell T_NODE s tb2 = 1 := by
    have b1 := cvb hL hr0 (x := tb1) (by simp [boolCols])
    have b2 := cvb hL hr0 (x := tb2) (by simp [boolCols])
    rw [cell_eq_cast tr T_NODE s tb1, cell_eq_cast tr T_NODE s tb2, ← natCast_add,
      show cv tr T_NODE s tb1 + cv tr T_NODE s tb2 = 1 by omega]; rfl
  have B := brFields hL hC hb
  simp only at B
  rw [← brOff_eq hL hC] at B
  obtain ⟨hfl, -, -, sVV, -, -, -, hW⟩ := B
  have mem : ∀ p ∈ brFL (brOff tr s) (popN tr s), p ∈ fl := fun p hp => hfl ▸ hp
  have hWin : ∀ j, j < popN tr s →
      rowT tr pub (s + (brOff tr s + 2 + 32 * j)) B_DIGEST false = (revDigs (kidOf tr (s + (brOff tr s + 2 + 32 * j)))).map Msg.toFp ∧
      rowT tr pub (s + (brOff tr s + 2 + 32 * j)) B_PARENT true =
        (revPar (cv tr T_NODE s depth) (kidOf tr (s + (brOff tr s + 2 + 32 * j)))).map Msg.toFp := fun j hj =>
    chView hL hC (mem _ (by simp [brFL]; exact Or.inr ⟨j, hj, rfl⟩)) (by omega) (hW j hj).1
  rw [brGated hL hC hb gD, brGated hL hC hb gP, TD, TP]
  rw [flatMap_congr' (fun j hj => (hWin j (List.mem_range.mp hj)).1),
    flatMap_congr' (l := List.range (popN tr s)) (G := fun j => (revPar (cv tr T_NODE s depth)
      (kidOf tr (s + (brOff tr s + 2 + 32 * j)))).map Msg.toFp) (fun j hj => (hWin j (List.mem_range.mp hj)).2)]
  unfold nodeVOf; rw [if_neg h1, if_neg h2]
  simp only [revealed_branch, flatMap_filterMap, revF_digs]
  rw [kidsFlat hL hC (brOff tr s) revDigs rfl]
  have hpar : ((kidsOf tr s (brOff tr s)).filterMap revF).map (fun x : Nat × Nat × Nat × List Nat × List Nat =>
      [x.1, cv tr T_NODE s depth + 1, x.2.1, x.2.2.1]) =
      (List.range (popN tr s)).flatMap fun w => revPar (cv tr T_NODE s depth) (kidOf tr (s + (brOff tr s + 2 + 32 * w))) := by
    rw [List.map_eq_flatMap, flatMap_filterMap]
    simp only [revF_par]
    exact kidsFlat hL hC (brOff tr s) (revPar _) rfl
  have hmap : ∀ (G : Nat → List Msg), (List.range (popN tr s)).flatMap (fun j => (G j).map Msg.toFp) =
      ((List.range (popN tr s)).flatMap G).map Msg.toFp := by
    intro G; rw [List.map_flatMap]
  by_cases h37 : brOff tr s = 37
  · obtain ⟨sV, sH⟩ := sVV h37
    have hm5 : (5, 32) ∈ fl := mem _ (by simp [brFL, h37])
    obtain ⟨VP, VD⟩ := vhView hL hC hm5 (by omega) sH hn (pub := pub)
    have hb2 : cv tr T_NODE s tb2 = 1 := by unfold brOff at h37; split at h37 <;> simp_all
    rw [if_pos h37, if_pos h37, VP, VD, if_pos hb2]
    refine ⟨?_, ?_⟩
    · unfold slotOf
      rw [hmap]
      by_cases htv : cv tr T_NODE s tv = 1
      · rw [if_pos htv, if_pos htv]
        simp only [List.map_append, List.append_assoc]
        exact List.Perm.append_left _ (List.perm_append_comm)
      · rw [if_neg htv, if_neg htv]; simp
    · simp only [List.nil_append]
      rw [hpar, hmap]
  · have hb1 : cv tr T_NODE s tb2 ≠ 1 := by intro h; apply h37; unfold brOff; rw [if_pos h]
    rw [if_neg h37, if_neg h37, if_neg hb1]
    refine ⟨?_, ?_⟩
    · rw [hmap]; simp
    · simp only [List.nil_append]
      rw [hpar, hmap]

end ZkFormal.NearV3.NodeProof3
