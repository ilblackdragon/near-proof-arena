import ZkFormal.NearV3.Extract.Node.Gated

/-!
# ZkFormal.Near.Extract.NodeGated2 — per-node gated traffic against the view
-/

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

/-! ## Per-node view lists -/

def pnDig (S : NodeS3) : List Msg :=
  (S.v.revealed.flatMap fun (c, l, _, pre, po) => [digMsg (msgId K_NPRE c) l pre, digMsg (msgId K_NPOST c) l po]) ++
  (match S.v.value with
   | some (i, l, pre, po, w) => [digMsg (msgId K_VPRE i) l pre] ++ (if w then [digMsg (msgId K_VPOST i) l po] else [])
   | none => [])

def pnParS (S : NodeS3) : List Msg := S.v.revealed.map fun (c, l, r, _, _) => [c, S.tau, S.depth + 1, l, r]

def pnParR (n : Nat) (S : NodeS3) : List Msg := [[n, S.tau, S.depth, (S.v.ser false).length, S.res]]

def pnVpar (S : NodeS3) : List Msg := match S.v.value with | some (i, l, _, _, _) => [[i, l]] | none => []

def pnBmS (n : Nat) (S : NodeS3) : List Msg := match S.v.bmap with | some (bm, hv) => [[n, bm, hv, 0]] | none => []
def pnBmR (n : Nat) (S : NodeS3) : List Msg := match S.v.bmap with | some (bm, hv) => [[n, bm, hv, S.ubm]] | none => []

def pnDup (n : Nat) (S : NodeS3) : List Msg := if S.dup then [[eidN n, S.repE]] else []

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
  have hpos := counter_of (f := fun q => tr.cell T_NODE q NodeV3.pos) (s := s) (ℓ := ℓ) (v0 := 0)
    (by have := hC.seg.2.1; rw [one_iff] at this
        show tr.cell T_NODE s NodeV3.pos = _
        rw [((rowFacts hL (by omega)).2.2.2.1 this).2.2.2.1]; rfl)
    (fun q h1 h2 => by
      have ha := hC.seg.2.2.2.1 q h1 (by omega); rw [one_iff] at ha
      have hl' := zero_of hL (by omega) (by simp [boolCols]) (hC.seg.2.2.2.2.2 q h1 h2)
      exact (inNode hL (by omega) ha hl').2.2.1) (s + ℓ - 1) (by omega) (by omega)
  rw [hpos, show s + ℓ - 1 = s + (ℓ - 1) by omega, segConst hL hC (by simp [nodeConst]) (by omega)] at E
  rw [← E, show ((1 : Fp)) = ((1 : Nat) : Fp) from rfl, ← natCast_add]; congr 1; omega

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

/-- The revealed value of a slot. -/
def slotValue : NSlot3 → Option (Nat × Nat × List Nat × List Nat × Bool)
  | .val _ i l pre po w => some (i, l, pre, po, w)
  | _ => none

theorem valDigs_eq (sl : NSlot3) : valDigs sl = match slotValue sl with
    | some (i, l, pre, po, w) => [digMsg (msgId K_VPRE i) l pre] ++ (if w then [digMsg (msgId K_VPOST i) l po] else [])
    | none => [] := by cases sl <;> rfl

theorem valPar_eq (sl : NSlot3) : valPar sl = match slotValue sl with
    | some (i, l, _, _, _) => [[i, l]] | none => [] := by cases sl <;> rfl

theorem value_leaf (k : List Nat) (sl : NSlot3) (m : List Nat) : (NodeV3.leaf k sl m).value = slotValue sl := by
  cases sl <;> rfl
theorem value_ext (k : List Nat) (kd : NKid) (m : List Nat) : (NodeV3.ext k kd m).value = none := rfl
theorem value_br (v : Option NSlot3) (kids : List NKid) (m : List Nat) :
    (NodeV3.branch v kids m).value = (v.bind slotValue) := by
  cases v with
  | none => rfl
  | some sl => cases sl <;> rfl

def revF : NKid → Option (Nat × Nat × Nat × List Nat × List Nat)
  | .node c l r pre po => some (c, l, r, pre, po)
  | _ => none

theorem flatMap_filterMap {α β γ : Type} (l : List α) (f : α → Option β) (g : β → List γ) :
    (l.filterMap f).flatMap g = l.flatMap fun a => (f a).toList.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filterMap_cons, List.flatMap_cons]
    cases h : f a <;> simp [ih, h]

theorem revealed_branch (v : Option NSlot3) (kids : List NKid) (m : List Nat) :
    (NodeV3.branch v kids m).revealed = kids.filterMap revF := by
  simp only [NodeV3.revealed]
  congr 1

theorem revealed_ext (k : List Nat) (kid : NKid) (m : List Nat) :
    (NodeV3.ext k kid m).revealed = (revF kid).toList := by cases kid <;> rfl

theorem revF_digs (kd : NKid) :
    (revF kd).toList.flatMap (fun x : Nat × Nat × Nat × List Nat × List Nat =>
      [digMsg (msgId K_NPRE x.1) x.2.1 x.2.2.2.1, digMsg (msgId K_NPOST x.1) x.2.1 x.2.2.2.2]) = revDigs kd := by
  cases kd <;> simp [revF, revDigs]

theorem revF_par (t d : Nat) (kd : NKid) :
    (revF kd).toList.flatMap (fun x : Nat × Nat × Nat × List Nat × List Nat => [[x.1, t, d + 1, x.2.1, x.2.2.1]]) =
      revPar t d kd := by
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

/-- `PARENT` receive of one record. -/
theorem nodeParR (hC : NodeCtx tr s ℓ fl) {n : Nat} (S : NodeS3) (hv : S.v = nodeVOf tr s)
    (ht : S.tau = cv tr T_NODE s tau) (hd : S.depth = cv tr T_NODE s depth) (hr : S.res = cv tr T_NODE s res)
    (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp)) :
    (List.range' s ℓ).flatMap (fun r => rowT tr pub r B_PARENT false) = (pnParR n S).map Msg.toFp := by
  rw [tagOnly hL hC (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) (fun p hp h => (innerStart hL hC hp h).1)]
  rw [(tagStart hL hC).2.2.2.2.2.1, pnParR, hv, ht, hd, hr, ← (nodeSer hL hC).1, rowsB_length]
  simp [Msg.toFp, hn, lenCell hL hC, ← natCast_eq, cast_cv]

/-- `DUP` receive of one record. -/
theorem nodeDup (hC : NodeCtx tr s ℓ fl) {n : Nat} (S : NodeS3) (hdu : S.dup = decide (cv tr T_NODE s dup = 1))
    (hre : S.repE = cv tr T_NODE s repE) (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp)) :
    (List.range' s ℓ).flatMap (fun r => rowT tr pub r B_DUP false) = (pnDup n S).map Msg.toFp := by
  rw [tagOnly hL hC (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))))
    (fun p hp h => (innerStart hL hC hp h).2)]
  rw [(tagStart hL hC).2.2.2.2.2.2, pnDup, hdu, hre]
  rcases isBool hL (nodeStart hL hC).1 (x := dup) (by simp [boolCols]) with h | h
  · rw [h, cv_zero h]; simp [gate]
  · rw [h, cv_one h]; simp [gate, Msg.toFp, hn, eidN, ← natCast_eq, cast_cv, toFp_msgId]

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

theorem bitsVal_congr16 (f g : Nat → Nat) (h : ∀ j, j < 16 → f (0 + j) = g j) :
    bitsVal f 0 16 = bitsVal (fun j => g j) 0 16 := by
  have gen : ∀ n, n ≤ 16 → bitsVal f 0 n = bitsVal (fun j => g j) 0 n := by
    intro n; induction n with
    | zero => intro _; rfl
    | succ n ih => intro hn; simp only [bitsVal]; rw [ih (by omega), h n (by omega)]; simp
  exact gen 16 (Nat.le_refl _)

set_option maxHeartbeats 1000000 in
/-- `DIGEST` receive, `PARENT` send, `VPARENT` send and `BMAP` of one record. -/
theorem nodeDPVB (hC : NodeCtx tr s ℓ fl) {n : Nat} (S : NodeS3) (hv : S.v = nodeVOf tr s)
    (ht : S.tau = cv tr T_NODE s tau) (hd : S.depth = cv tr T_NODE s depth) (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp))
    (hub : S.ubm = cv tr T_NODE (s + brOff tr s) mBm) :
    ((List.range' s ℓ).flatMap (fun r => rowT tr pub r B_DIGEST false)).Perm ((pnDig S).map Msg.toFp) ∧
    (List.range' s ℓ).flatMap (fun r => rowT tr pub r B_PARENT true) = (pnParS S).map Msg.toFp ∧
    (List.range' s ℓ).flatMap (fun r => rowT tr pub r B_VPARENT true) = (pnVpar S).map Msg.toFp ∧
    (List.range' s ℓ).flatMap (fun r => rowT tr pub r B_BMAP true) = (pnBmS n S).map Msg.toFp ∧
    (List.range' s ℓ).flatMap (fun r => rowT tr pub r B_BMAP false) = (pnBmR n S).map Msg.toFp := by
  have gD : Gated B_DIGEST false := Or.inl ⟨rfl, rfl⟩
  have gP : Gated B_PARENT true := Or.inr (Or.inl ⟨rfl, rfl⟩)
  have gV : Gated B_VPARENT true := Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have gBs : Gated B_BMAP true := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  have gBr : Gated B_BMAP false := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
  obtain ⟨T1, T2, T3, T4, T5, -, -⟩ := tagStart hL hC (pub := pub)
  obtain ⟨hr0, ha0⟩ := nodeStart hL hC
  have T := typeSumNat hL hr0 ha0
  simp only [pnDig, pnParS, pnVpar, pnBmS, pnBmR, hv, ht, hd, hub]
  by_cases h1 : cv tr T_NODE s tl = 1
  · -- leaf
    have htl := of_cv_one h1
    obtain ⟨-, -, hfl, -, -, -, -, -, -, sVH, -⟩ := leafFields hL hC htl
    have hm : (9 + cv tr T_NODE s hplen, 32) ∈ fl := hfl ▸ (by simp [leafFL])
    obtain ⟨VP, VB1, VB2, VD, VV⟩ := vhView hL hC (rV := s + (5 + cv tr T_NODE s hplen)) hm sVH (pub := pub)
    rw [leafGated hL hC htl gD, leafGated hL hC htl gP, leafGated hL hC htl gV, leafGated hL hC htl gBs,
      leafGated hL hC htl gBr, T1, T2, T3, T4, T5, VP, VB1, VB2, VD, VV]
    unfold nodeVOf; rw [if_pos h1]
    simp only [NodeV3.revealed, NodeV3.bmap, value_leaf, valDigs_eq, valPar_eq, List.flatMap_nil, List.nil_append,
      List.map_nil, List.append_nil]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | exact List.Perm.refl _ | simp
  by_cases h2 : cv tr T_NODE s te = 1
  · -- extension
    have hte := of_cv_one h2
    obtain ⟨-, -, hfl, -, -, -, -, -, sC, -⟩ := extFields hL hC hte
    have hm : (5 + cv tr T_NODE s hplen, 32) ∈ fl := hfl ▸ (by simp [extFL])
    obtain ⟨CD, CP⟩ := chView hL hC hm sC (pub := pub)
    obtain ⟨CV, CB1, CB2, -, -⟩ := chStartMsgs hL hC hm sC (pub := pub)
    rw [extGated hL hC hte gD, extGated hL hC hte gP, extGated hL hC hte gV, extGated hL hC hte gBs,
      extGated hL hC hte gBr, T1, T2, T3, T4, T5, CD, CP, CV, CB1, CB2]
    unfold nodeVOf; rw [if_neg h1, if_pos h2]
    simp only [revealed_ext, value_ext, NodeV3.bmap, List.nil_append, List.append_nil, List.map_nil]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [revF_digs]
    · generalize kidOf tr (s + (5 + cv tr T_NODE s hplen)) = kd
      cases kd <;> simp [revPar, revF]
    all_goals first | trivial | rfl | simp
  -- branch
  have hb : tr.cell T_NODE s tb1 + tr.cell T_NODE s tb2 = 1 := by
    have b1 := cvb hL hr0 (x := tb1) (by simp [boolCols])
    have b2 := cvb hL hr0 (x := tb2) (by simp [boolCols])
    rw [cell_eq_cast tr T_NODE s tb1, cell_eq_cast tr T_NODE s tb2, ← natCast_add,
      show cv tr T_NODE s tb1 + cv tr T_NODE s tb2 = 1 by omega]; rfl
  have B := brFields hL hC hb
  simp only at B
  rw [← brOff_eq hL hC] at B
  obtain ⟨hfl, -, -, sVV, sB, -, -, hW⟩ := B
  have mem : ∀ p ∈ brFL (brOff tr s) (popN tr s), p ∈ fl := fun p hp => hfl ▸ hp
  have hWin : ∀ j, j < popN tr s →
      rowT tr pub (s + (brOff tr s + 2 + 32 * j)) B_DIGEST false =
        (revDigs (kidOf tr (s + (brOff tr s + 2 + 32 * j)))).map Msg.toFp ∧
      rowT tr pub (s + (brOff tr s + 2 + 32 * j)) B_PARENT true =
        (revPar (cv tr T_NODE s tau) (cv tr T_NODE s depth) (kidOf tr (s + (brOff tr s + 2 + 32 * j)))).map Msg.toFp ∧
      rowT tr pub (s + (brOff tr s + 2 + 32 * j)) B_VPARENT true = [] ∧
      rowT tr pub (s + (brOff tr s + 2 + 32 * j)) B_BMAP true = [] ∧
      rowT tr pub (s + (brOff tr s + 2 + 32 * j)) B_BMAP false = [] := fun j hj => by
    have hmj : (brOff tr s + 2 + 32 * j, 32) ∈ fl := mem _ (by simp [brFL]; exact Or.inr ⟨j, hj, rfl⟩)
    obtain ⟨a1, a2⟩ := chView hL hC hmj (hW j hj).1 (pub := pub)
    obtain ⟨a3, a4, a5, -, -⟩ := chStartMsgs hL hC hmj (hW j hj).1 (pub := pub)
    exact ⟨a1, a2, a3, a4, a5⟩
  have hmB : (brOff tr s, 2) ∈ fl := mem _ (by simp [brFL])
  obtain ⟨BP, BD, BV, BS, BR⟩ := bmStartMsgs hL hC hmB sB (pub := pub)
  rw [brGated hL hC hb gD, brGated hL hC hb gP, brGated hL hC hb gV, brGated hL hC hb gBs, brGated hL hC hb gBr,
    T1, T2, T3, T4, T5, BP, BD, BV, BS, BR]
  rw [flatMap_congr' (fun j hj => (hWin j (List.mem_range.mp hj)).1),
    flatMap_congr' (l := List.range (popN tr s)) (G := fun j => (revPar (cv tr T_NODE s tau) (cv tr T_NODE s depth)
      (kidOf tr (s + (brOff tr s + 2 + 32 * j)))).map Msg.toFp) (fun j hj => (hWin j (List.mem_range.mp hj)).2.1),
    flatMap_congr' (l := List.range (popN tr s)) (G := fun _ => ([] : List (List Fp)))
      (fun j hj => (hWin j (List.mem_range.mp hj)).2.2.1)]
  rw [flatMap_congr' (l := List.range (popN tr s)) (G := fun _ => ([] : List (List Fp)))
      (fun j hj => (hWin j (List.mem_range.mp hj)).2.2.2.1),
    flatMap_congr' (l := List.range (popN tr s)) (G := fun _ => ([] : List (List Fp)))
      (fun j hj => (hWin j (List.mem_range.mp hj)).2.2.2.2)]
  simp only [flatMap_nil_fun, List.append_nil]
  -- the view of the branch
  have hbv : ∀ j, j < 16 → cv tr T_NODE s (bm j) ≤ 1 := fun j hj => cvb hL hr0 (bm_bool hj)
  have hrB : s + brOff tr s < tr.height T_NODE := by
    have := (fieldAt hL hC hmB).2; omega
  have hin : brOff tr s < ℓ := by have := (hC.fields.field _ hmB).2; simp at this; omega
  have hbmc : ∀ j, j < 16 → cv tr T_NODE (s + brOff tr s) (bm (0 + j)) = cv tr T_NODE s (bm j) := by
    intro j hj
    have hmem : bm j ∈ nodeConst := by
      unfold nodeConst; simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inr ⟨j, hj, rfl⟩)
    unfold cv; rw [Nat.zero_add, segConst hL hC hmem hin]
  have hbmE : bmE.eval tr T_NODE (s + brOff tr s) pub = ((kidBitmap (kidsOf tr s (brOff tr s)) : Nat) : Fp) := by
    rw [bmE, eval_bits tr T_NODE (s + brOff tr s) pub bm 0 16
      (fun j hj => isBool hL hrB (bm_bool (by omega))), kidBitmap_kidsOf tr s (brOff tr s) hbv,
      bitsVal_congr16 hL _ _ hbmc]
  have hrevs : ((kidsOf tr s (brOff tr s)).filterMap revF).map (fun x : Nat × Nat × Nat × List Nat × List Nat =>
      [x.1, cv tr T_NODE s tau, cv tr T_NODE s depth + 1, x.2.1, x.2.2.1]) =
      (List.range (popN tr s)).flatMap fun w => revPar (cv tr T_NODE s tau) (cv tr T_NODE s depth)
        (kidOf tr (s + (brOff tr s + 2 + 32 * w))) := by
    rw [List.map_eq_flatMap, flatMap_filterMap]
    simp only [revF_par]
    exact kidsFlat hL hC (brOff tr s) (revPar _ _) rfl
  have hdigs : ((kidsOf tr s (brOff tr s)).filterMap revF).flatMap (fun x : Nat × Nat × Nat × List Nat × List Nat =>
      [digMsg (msgId K_NPRE x.1) x.2.1 x.2.2.2.1, digMsg (msgId K_NPOST x.1) x.2.1 x.2.2.2.2]) =
      (List.range (popN tr s)).flatMap fun w => revDigs (kidOf tr (s + (brOff tr s + 2 + 32 * w))) := by
    rw [flatMap_filterMap]; simp only [revF_digs]
    exact kidsFlat hL hC (brOff tr s) revDigs rfl
  have hmap : ∀ (G : Nat → List Msg), (List.range (popN tr s)).flatMap (fun j => (G j).map Msg.toFp) =
      ((List.range (popN tr s)).flatMap G).map Msg.toFp := by intro G; rw [List.map_flatMap]
  have hBm : tr.cell T_NODE (s + brOff tr s) nid = ((n : Nat) : Fp) ∧
      tr.cell T_NODE (s + brOff tr s) tb2 = tr.cell T_NODE s tb2 := by
    have hin : brOff tr s < ℓ := by have := (hC.fields.field _ hmB).2; simp at this; omega
    exact ⟨by rw [segConst hL hC (by simp [nodeConst]) hin, hn], segConst hL hC (by simp [nodeConst]) hin⟩
  unfold nodeVOf; rw [if_neg h1, if_neg h2]
  simp only [revealed_branch, value_br, NodeV3.bmap, hrevs, hdigs]
  rw [hmap, hmap]
  have hsome : ∀ (x : NSlot3), (if (if cv tr T_NODE s tb2 = 1 then some x else none).isSome then 1 else 0) =
      cv tr T_NODE s tb2 := by
    intro x
    rcases isBool hL hr0 (x := tb2) (by simp [boolCols]) with h | h
    · rw [cv_zero h]; rfl
    · rw [cv_one h]; rfl
  have hbmS : [[tr.cell T_NODE (s + brOff tr s) nid, bmE.eval tr T_NODE (s + brOff tr s) pub,
      tr.cell T_NODE (s + brOff tr s) tb2, 0]] =
      [Msg.toFp [n, kidBitmap (kidsOf tr s (brOff tr s)),
        if (if cv tr T_NODE s tb2 = 1 then some (slotOf tr s (s + 1) (s + 5)) else none).isSome then 1 else 0, 0]] := by
    rw [hBm.1, hBm.2, hbmE, hsome]; simp [Msg.toFp, ← natCast_eq, cast_cv]; rfl
  have hbmR : [[tr.cell T_NODE (s + brOff tr s) nid, bmE.eval tr T_NODE (s + brOff tr s) pub,
      tr.cell T_NODE (s + brOff tr s) tb2, tr.cell T_NODE (s + brOff tr s) mBm]] =
      [Msg.toFp [n, kidBitmap (kidsOf tr s (brOff tr s)),
        if (if cv tr T_NODE s tb2 = 1 then some (slotOf tr s (s + 1) (s + 5)) else none).isSome then 1 else 0,
        cv tr T_NODE (s + brOff tr s) mBm]] := by
    rw [hBm.1, hBm.2, hbmE, hsome]; simp [Msg.toFp, ← natCast_eq, cast_cv]
  by_cases h37 : brOff tr s = 37
  · obtain ⟨sV, sH⟩ := sVV h37
    have hm5 : (5, 32) ∈ fl := mem _ (by simp [brFL, h37])
    obtain ⟨VP, VB1, VB2, VD, VV⟩ := vhView hL hC (rV := s + 1) hm5 sH (pub := pub)
    have hb2 : cv tr T_NODE s tb2 = 1 := by unfold brOff at h37; split at h37 <;> simp_all
    rw [hbmS, hbmR]
    rw [if_pos h37, if_pos h37, if_pos h37, if_pos h37, if_pos h37, VP, VB1, VB2, VD, VV, if_pos hb2]
    simp only [List.nil_append, List.append_nil, Option.bind_some, valDigs_eq, valPar_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [List.map_append]; exact List.perm_append_comm
    all_goals first | rfl | simp
  · have hb1 : cv tr T_NODE s tb2 ≠ 1 := by intro h; apply h37; unfold brOff; rw [if_pos h]
    rw [hbmS, hbmR]
    rw [if_neg h37, if_neg h37, if_neg h37, if_neg h37, if_neg h37, if_neg hb1]
    simp only [List.nil_append, List.append_nil, Option.bind_none]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals first | rfl | simp

end ZkFormal.NearV3.NodeProof3
