import ZkFormal.Near.Extract.NodeTraffic

/-!
# ZkFormal.Near.Extract.NodeGated — DIGEST / PARENT / VSLOT messages of a node
-/

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node ZkFormal.Near

/-- The gated (bus, side) pairs. -/
def Gated (bb : Nat) (sd : Bool) : Prop :=
  (bb = B_DIGEST ∧ sd = false) ∨ (bb = B_PARENT ∧ sd = true) ∨ (bb = B_PARENT ∧ sd = false) ∨
    (bb = B_VSLOT ∧ sd = false)

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

theorem gatedQuiet (hC : NodeCtx tr s ℓ fl) {bb : Nat} {sd : Bool} (hg : Gated bb sd) :
    ∀ r, s ≤ r → r < s + ℓ → tr.cell T_NODE r fs = 0 → rowT tr pub r bb sd = [] := by
  intro r h1 h2 h3
  have Q := quietRow hL hC h1 h2 h3
  rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Q.1
  · exact Q.2.1
  · exact Q.2.2.1
  · exact Q.2.2.2

theorem gatedFields (hC : NodeCtx tr s ℓ fl) {bb : Nat} {sd : Bool} (hg : Gated bb sd) :
    (List.range' s ℓ).flatMap (fun r => rowT tr pub r bb sd) = fl.flatMap fun p => rowT tr pub (s + p.1) bb sd := by
  rw [rowsFields hL hC]
  exact flatMap_congr' (fun p hp => fieldGated hL hC hp (gatedQuiet hL hC hg))

/-- A field start that is not a window and not the node start is silent on gated buses. -/
theorem plainStart (hC : NodeCtx tr s ℓ fl) {o L x : Nat} (hm : (o, L) ∈ fl) (ho : 0 < o)
    (hx : tr.cell T_NODE (s + o) x = 1) (hxs : x ∈ states) (h1 : sVH ≠ x) (h2 : sCH ≠ x)
    {bb : Nat} {sd : Bool} (hg : Gated bb sd) : rowT tr pub (s + o) bb sd = [] := by
  obtain ⟨hF, hH⟩ := fieldAt hL hC hm
  have hr : s + o < tr.height T_NODE := by have := hF.pos; omega
  have ha : tr.cell T_NODE (s + o) act = 1 := by simpa using hF.act 0 hF.pos
  have hv := stOnly hL hr ha hx hxs (by simp [states]) h1
  have hc := stOnly hL hr ha hx hxs (by simp [states]) h2
  obtain ⟨P1, P2, hgP, hgD, h0⟩ := innerStart hL hC hm ho
  rw [hv, hc] at hgD; rw [hc] at hgP
  have hgP' : tr.cell T_NODE (s + o) gP = 0 := by rw [hgP]; grind
  have hgD' : tr.cell T_NODE (s + o) gD = 0 := by rw [hgD]; grind
  rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [rowT_digest, hgD', if_neg h0]; simp [gate]
  · rw [rowT_parentS, hgP']; simp [gate]
  · exact P1
  · exact P2

end ZkFormal.Near.NodeProof

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node ZkFormal.Near

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

theorem leafGated (hC : NodeCtx tr s ℓ fl) (ht : tr.cell T_NODE s tl = 1) {bb : Nat} {sd : Bool} (hg : Gated bb sd) :
    (List.range' s ℓ).flatMap (fun r => rowT tr pub r bb sd) =
      rowT tr pub s bb sd ++ rowT tr pub (s + (9 + cv tr T_NODE s hplen)) bb sd := by
  obtain ⟨hh1, -, hfl, hℓ, sT, sH, sF, sK, sV, sVH, sM⟩ := leafFields hL hC ht
  have mem : ∀ p ∈ leafFL (cv tr T_NODE s hplen), p ∈ fl := fun p hp => hfl ▸ hp
  rw [gatedFields hL hC hg, hfl]
  have z1 := plainStart hL hC (L := 4) (mem _ (by simp [leafFL, keyFL])) (by omega) sH (by simp [states]) (by decide) (by decide) hg
  have z5 := plainStart hL hC (L := 1) (mem _ (by simp [leafFL, keyFL])) (by omega) sF (by simp [states]) (by decide) (by decide) hg
  have zV := plainStart hL hC (L := 4) (mem _ (by simp [leafFL, keyFL])) (by omega) sV (by simp [states]) (by decide) (by decide) hg
  have zM := plainStart hL hC (L := 8) (mem _ (by simp [leafFL, keyFL])) (by omega) sM (by simp [states]) (by decide) (by decide) hg
  unfold leafFL keyFL
  by_cases h1 : cv tr T_NODE s hplen = 1
  · simp only [if_pos h1, List.append_nil, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil,
      Nat.add_zero]
    simp only [z1, z5, zV, zM, List.nil_append, List.append_nil]
  · have zK := plainStart hL hC (L := cv tr T_NODE s hplen - 1) (mem _ (by simp [leafFL, keyFL, h1])) (by omega)
      (sK h1) (by simp [states]) (by decide) (by decide) hg
    simp only [if_neg h1, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil,
      Nat.add_zero]
    simp only [z1, z5, zV, zM, zK, List.nil_append, List.append_nil]

theorem extGated (hC : NodeCtx tr s ℓ fl) (ht : tr.cell T_NODE s te = 1) {bb : Nat} {sd : Bool} (hg : Gated bb sd) :
    (List.range' s ℓ).flatMap (fun r => rowT tr pub r bb sd) =
      rowT tr pub s bb sd ++ rowT tr pub (s + (5 + cv tr T_NODE s hplen)) bb sd := by
  obtain ⟨hh1, -, hfl, hℓ, sT, sH, sF, sK, sC, sM⟩ := extFields hL hC ht
  have mem : ∀ p ∈ extFL (cv tr T_NODE s hplen), p ∈ fl := fun p hp => hfl ▸ hp
  rw [gatedFields hL hC hg, hfl]
  have z1 := plainStart hL hC (L := 4) (mem _ (by simp [extFL, keyFL])) (by omega) sH (by simp [states]) (by decide) (by decide) hg
  have z5 := plainStart hL hC (L := 1) (mem _ (by simp [extFL, keyFL])) (by omega) sF (by simp [states]) (by decide) (by decide) hg
  have zM := plainStart hL hC (L := 8) (mem _ (by simp [extFL, keyFL])) (by omega) sM (by simp [states]) (by decide) (by decide) hg
  unfold extFL keyFL
  by_cases h1 : cv tr T_NODE s hplen = 1
  · simp only [if_pos h1, List.append_nil, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil,
      Nat.add_zero]
    simp only [z1, z5, zM, List.nil_append, List.append_nil]
  · have zK := plainStart hL hC (L := cv tr T_NODE s hplen - 1) (mem _ (by simp [extFL, keyFL, h1])) (by omega)
      (sK h1) (by simp [states]) (by decide) (by decide) hg
    simp only [if_neg h1, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil,
      Nat.add_zero]
    simp only [z1, z5, zM, zK, List.nil_append, List.append_nil]

theorem brGated (hC : NodeCtx tr s ℓ fl) (hb : tr.cell T_NODE s tb1 + tr.cell T_NODE s tb2 = 1) {bb : Nat} {sd : Bool}
    (hg : Gated bb sd) :
    (List.range' s ℓ).flatMap (fun r => rowT tr pub r bb sd) =
      rowT tr pub s bb sd ++ ((if brOff tr s = 37 then rowT tr pub (s + 5) bb sd else []) ++
        (List.range (popN tr s)).flatMap fun j => rowT tr pub (s + (brOff tr s + 2 + 32 * j)) bb sd) := by
  have B := brFields hL hC hb
  simp only at B
  rw [← brOff_eq hL hC] at B
  obtain ⟨hfl, hℓ, sT, sVV, sB, -, sM, -⟩ := B
  have mem : ∀ p ∈ brFL (brOff tr s) (popN tr s), p ∈ fl := fun p hp => hfl ▸ hp
  have hoff : brOff tr s = 1 ∨ brOff tr s = 37 := by unfold brOff; split <;> simp
  rw [gatedFields hL hC hg, hfl]
  have zB := plainStart hL hC (L := 2) (mem _ (by simp [brFL])) (by omega) sB (by simp [states]) (by decide) (by decide) hg
  have zM := plainStart hL hC (L := 8) (mem _ (by simp [brFL])) (by omega) sM (by simp [states]) (by decide) (by decide) hg
  unfold brFL
  rcases hoff with ho | ho
  · rw [ho] at zB zM ⊢
    simp only [List.append_nil, List.cons_append, List.nil_append,
      List.flatMap_cons, List.flatMap_nil, List.flatMap_append, List.flatMap_map, Nat.add_zero, zB, zM,
      show (1 : Nat) ≠ 37 by decide, if_false, ite_true]
  · rw [ho] at zB zM sVV ⊢
    obtain ⟨sV, sH⟩ := sVV rfl
    have zV := plainStart hL hC (L := 4) (mem _ (by simp [brFL, ho])) (by omega) sV (by simp [states]) (by decide) (by decide) hg
    simp only [show (37 : Nat) ≠ 1 by decide, if_false, if_true, List.append_nil, List.cons_append, List.nil_append,
      List.flatMap_cons, List.flatMap_nil, List.flatMap_append, List.flatMap_map, Nat.add_zero, zB, zM, zV]

end ZkFormal.Near.NodeProof
