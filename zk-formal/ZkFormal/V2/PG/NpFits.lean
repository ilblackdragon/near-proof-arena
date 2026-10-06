import ZkFormal.V2.PG.NpBasic

/-!
# ZkFormal.V2.PG.NpFits (P2 copy of `Prover.NpFits` at `dp = pg g`) — every honest message fits its slot (`MsgFitsStmt`)
-/

namespace ZkFormal.V2.PG

variable [AuxG]

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np ZkFormal.Prover ZkFormal.Prover.Np

theorem fits_nil : Entry.Fits (.msg ([] : List (PartV Fp8 (Oracle Fp)))) (.msg []) :=
  ⟨rfl, fun k hk => absurd hk (by simp)⟩

theorem fits_cons {p : PartV Fp8 (Oracle Fp)} {ps : List (PartV Fp8 (Oracle Fp))} {q : Part}
    {qs : List Part} (h1 : PartV.Fits p q) (h2 : Entry.Fits (.msg ps) (.msg qs)) :
    Entry.Fits (.msg (p :: ps)) (.msg (q :: qs)) := by
  obtain ⟨hl, hk⟩ := h2
  refine ⟨by simp [hl], fun k hk' => ?_⟩
  match k with
  | 0 => exact ⟨q, rfl, h1⟩
  | k + 1 => exact hk k (by simpa using hk')

theorem fits_oracle_range (n : Nat) (M : Nat → Mat Fp) (sh : Nat → Nat × Nat)
    (h : ∀ t, t < n → (M t).log = (sh t).1 ∧ (M t).width = (sh t).2 ∧
      ∀ i, ((M t).row i).length = (M t).width) :
    PartV.Fits (K := Fp8) (.oracle ((List.range n).map M)) (.oracle ((List.range n).map sh)) := by
  refine ⟨by simp, fun k hk => ?_⟩
  simp only [List.length_map, List.length_range] at hk
  obtain ⟨h1, h2, h3⟩ := h k hk
  exact ⟨sh k, by simp [hk], by simp [h1], by simp [h2], fun i _ => by simp [h3]⟩

section
variable (A : Air) (tr : Trace Fp)

theorem nB_pos : 1 ≤ nB A tr := Nat.le_max_left _ _

theorem slotPairs_get (j : Nat) :
    (slotPairs A tr)[j]? =
      if j < 5 then
        ([([.header A.tables.length, .oracle ((layout A dp (hdr A tr)).map fun L => (L.lde, L.width))],
            false), ([], false),
          ([.oracle ((layout A dp (hdr A tr)).map fun L => (L.lde, 8 * L.aux)),
            .elems ((layout A dp (hdr A tr)).map fun L => L.sendG + L.recvG).sum], false),
          ([.oracle ((layout A dp (hdr A tr)).map fun L => (L.lde, 8 * L.quot))], true),
          ([.elems ((layout A dp (hdr A tr)).map fun L => 2 * L.width + 2 * L.aux + L.quot).sum],
            false)] : List (List Part × Bool))[j]?
      else if j < 4 + nB A tr then some ([], false)
      else ((kinds A tr)[j - (4 + nB A tr)]?).map fun k => (kindParts A tr k, false) := by
  have hb := nB_pos A tr
  unfold slotPairs
  by_cases h5 : j < 5
  · rw [if_pos h5, List.append_assoc, List.getElem?_append_left (by simpa using h5)]
  · rw [if_neg h5, List.append_assoc, List.getElem?_append_right (by simp; omega)]
    by_cases hb' : j < 4 + nB A tr
    · rw [if_pos hb', List.getElem?_append_left (by simp; omega)]
      simp [List.getElem?_replicate]; omega
    · rw [if_neg hb', List.getElem?_append_right (by simp; omega), List.getElem?_map]
      congr 2; simp; omega

end

theorem fits_kind (A : Air) (cb : Bytes) (tr : Trace Fp) (cs : List Fp8) (k : Bool × Nat) :
    Entry.Fits (.msg (kindMsg A cb tr cs k)) (.msg (kindParts A tr k)) := by
  obtain ⟨b, i⟩ := k
  cases b
  · simp only [kindParts, kindMsg, Bool.false_eq_true, ite_false]
    cases h : (commits A tr).lookup i with
    | some a =>
      simp only
      refine fits_cons ⟨rfl, fun k hk => ?_⟩ fits_nil
      simp only [List.length_singleton, Nat.lt_one_iff] at hk
      subst hk
      refine ⟨_, rfl, rfl, rfl, fun j _ => ?_⟩
      simp [friMat, length_limbsL]
    | none => exact fits_nil
  · simp only [kindParts, kindMsg, ite_true]; exact fits_nil

theorem msgFits : MsgFitsStmt := by
  intro A cb tr cs j hj
  have hb := nB_pos A tr
  have hlay := lay_eq A tr
  unfold msgParts
  rw [slotPairs_get]
  unfold npMsg
  by_cases h0 : j = 0
  · subst h0
    simp only [ite_true, show (0 : Nat) < 5 by decide]
    refine fits_cons (hdr_length A tr) (fits_cons ?_ fits_nil)
    show PartV.Fits (.oracle ((List.range A.tables.length).map (mainMat A tr))) _
    rw [hlay, List.map_map]
    exact fits_oracle_range _ _ _ fun t _ => ⟨rfl, rfl, fun i => by simp [mainMat, mainRow]⟩
  by_cases h1 : j = 1
  · subst h1
    simp only [show (1 : Nat) < 5 by decide, ite_true, show (1 : Nat) ≠ 0 by decide, ite_false]
    exact fits_nil
  by_cases h2 : j = 2
  · subst h2
    simp only [show (2 : Nat) < 5 by decide, ite_true, show (2 : Nat) ≠ 0 by decide,
      show (2 : Nat) ≠ 1 by decide, ite_false]
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some, Option.getD_some]
    refine fits_cons ?_ (fits_cons ?_ fits_nil)
    · show PartV.Fits (.oracle ((List.range A.tables.length).map (auxMat A cb tr _ _))) _
      rw [hlay, List.map_map]
      exact fits_oracle_range _ _ _ fun t _ => ⟨rfl, rfl, fun i => by
        simp [auxMat, length_limbsL, auxV, layT]⟩
    · show (finalsAll A cb tr _ _).length = _
      rw [hlay, List.map_map, finalsAll, sum_flatMap_length]
      congr 1; apply List.map_congr_left; intro t _
      simp [finsT, layT, nG]
  by_cases h3 : j = 3
  · subst h3
    simp only [show (3 : Nat) < 5 by decide, ite_true, show (3 : Nat) ≠ 0 by decide,
      show (3 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 2 by decide, ite_false]
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some, Option.getD_some]
    refine fits_cons ?_ fits_nil
    show PartV.Fits (.oracle ((List.range A.tables.length).map (quotMat A cb tr _ _ _))) _
    rw [hlay, List.map_map]
    exact fits_oracle_range _ _ _ fun t _ => ⟨rfl, rfl, fun i => by
      simp [quotMat, length_limbsL, quotV, layT]⟩
  by_cases h4 : j = 4
  · subst h4
    simp only [show (4 : Nat) < 5 by decide, ite_true, show (4 : Nat) ≠ 0 by decide,
      show (4 : Nat) ≠ 1 by decide, show (4 : Nat) ≠ 2 by decide, show (4 : Nat) ≠ 3 by decide,
      ite_false]
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some, Option.getD_some]
    refine fits_cons ?_ fits_nil
    show (oodAll A cb tr _ _ _ _).length = _
    rw [hlay, List.map_map, oodAll, sum_flatMap_length]
    congr 1; apply List.map_congr_left; intro t _
    simp [oodT, mainV, auxV, quotV, layT]; omega
  simp only [h0, h1, h2, h3, h4, ite_false, show ¬ j < 5 by omega]
  by_cases hB : j < 4 + nB A tr
  · simp only [hB, ite_true]; exact fits_nil
  · simp only [hB, ite_false]
    cases hk : (kinds A tr)[j - (4 + nB A tr)]? with
    | none => exact ⟨rfl, fun k hk' => by
        simp only [List.length_singleton, Nat.lt_one_iff] at hk'; subst hk'
        exact ⟨_, rfl, rfl⟩⟩
    | some k =>
      simp only [Option.map_some, Option.getD_some]
      exact fits_kind A cb tr cs k

end ZkFormal.V2.PG
