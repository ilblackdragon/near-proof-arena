import ZkFormal.Near.Extract.NodeGated

/-!
# ZkFormal.Near.Extract.NodeGated2 — per-node gated traffic against the view
-/

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node ZkFormal.Near

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

end ZkFormal.Near.NodeProof

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node ZkFormal.Near

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
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

end ZkFormal.Near.NodeProof
