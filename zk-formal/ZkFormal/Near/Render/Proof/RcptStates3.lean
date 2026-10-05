import ZkFormal.Near.Render.Proof.RcptStates2

/-!
# ZkFormal.Near.Render.Proof.RcptStates3 — `cStates` at a field's last row

Last indices (`sE`), successions (`sF`), boundaries (`sG`) on a field's last
row: next field, next receipt, or (last receipt) a padding row.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace RcptP

open RcptGen

theorem fe1 {c : Claim} {e : Ext} {r s i : Nat} (hfe : i + 1 = fLen (Df c e r) s) :
    cF c e (.seg r s i) Rcpt.fe = 1 := by
  simp only [cF, S_fe, hfe, decide_true, b2n_true]; rfl

/-- Last indices. -/
theorem sE_end {c : Claim} {e : Ext} {r s i : Nat} (hfe : i + 1 = fLen (Df c e r) s) {nx : Nat → Fp}
    {fst lst : Bool} {pub : List Fp} : ∀ x ∈ sE, evR (cF c e (.seg r s i)) nx fst lst pub x = 0 := by
  intro x hx
  simp only [sE, List.mem_map] at hx
  obtain ⟨⟨st, ex⟩, hmem, rfl⟩ := hx
  simp only [evR_mul3, evR_c, evR_sub, fe1 hfe]
  simp only [Rcpt.lastIdx, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals simp only [cF, rseg, evR_c, evR_k, evR_sub, evR_add, evR_smul]
  all_goals (try split)
  all_goals first
    | (simp only [ofNat0]; grind)
    | (rename_i h; subst h; simp only [fLen, ↓reduceIte, Nat.reduceEqDiff] at hfe
       first
       | (rw [show i = 0 by omega]; simp only [ofNat0, ofNat1, natCast_eq]; grind)
       | (rw [← hfe]; simp only [ofNat_add_e, ofNat1, natCast_eq]; grind)
       | (obtain ⟨k, hk⟩ : ∃ k, i = k := ⟨i, rfl⟩
          rw [show i = 31 + 32 * (Df c e r).kt by omega]
          simp only [ofNat_add_e, ofNat_mul_e, natCast_eq]; grind)
       | (rw [show i = fLen (Df c e r) _ - 1 by simp only [fLen, ↓reduceIte, Nat.reduceEqDiff]; omega]
          simp only [fLen, ↓reduceIte, Nat.reduceEqDiff, natCast_eq]; grind))

theorem Cc_four {c : Claim} {e : Ext} {r s i : Nat} : Cc c e (.seg r s i) 4 = 0 := S_sCL c e r s i

theorem Cc_hr55 {c : Claim} {e : Ext} {r s i : Nat} : Cc c e (.seg r s i) 55 = b2n (Df c e r).hr := S_hr c e r s i

/-- Successions on a field's last row, next row the next field's first row. -/
theorem sF_fe {c : Claim} {e : Ext} {r s i : Nat} (hfe : i + 1 = fLen (Df c e r) s) {nx : Nat → Fp}
    (hn : ∀ st, 5 ≤ st → st ≤ 26 → nx st = if st = nextF (Df c e r).hr s then 1 else 0)
    {fst lst : Bool} {pub : List Fp} : ∀ x ∈ sF, evR (cF c e (.seg r s i)) nx fst lst pub x = 0 := by
  intro x hx
  simp only [sF, List.mem_map] at hx
  obtain ⟨⟨st, st', g⟩, hmem, rfl⟩ := hx
  simp only [evR_mul, evR_mul3, evR_c, evR_not, evR_n, fe1 hfe]
  simp only [Rcpt.succ, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals simp only [rcols]
  all_goals rw [hn _ (by decide) (by decide)]
  all_goals simp (disch := decide) only [cF, Cc_state, Cc_four, Cc_hr55, evR_c, evR_k, evR_not, ofNat0]
  all_goals first
    | grind
    | (split
       · rename_i h; subst h
         cases (Df c e r).hr <;> simp [nextF, b2n, ofNat0, ofNat1] <;> grind
       · simp only [ofNat0]; grind)

/-- Successions on a receipt's last row. -/
theorem sF_rl {c : Claim} {e : Ext} {r s i : Nat} (hfe : i + 1 = fLen (Df c e r) s)
    (hrl : isRl (Df c e r) s i = true) {nx : Nat → Fp} {fst lst : Bool} {pub : List Fp} :
    ∀ x ∈ sF, evR (cF c e (.seg r s i)) nx fst lst pub x = 0 := by
  have h2 : s = 26 ∨ (s = 23 ∧ (Df c e r).hr = false) := by
    unfold isRl at hrl
    cases hh : (Df c e r).hr <;> simp [hh] at hrl ⊢ <;> omega
  intro x hx
  simp only [sF, List.mem_map] at hx
  obtain ⟨⟨st, st', g⟩, hmem, rfl⟩ := hx
  simp only [evR_mul, evR_mul3, evR_c, evR_not, evR_n, fe1 hfe]
  simp only [Rcpt.succ, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals simp only [cF, rseg, evR_c, evR_k, evR_not]
  all_goals first
    | (split
       · rename_i h; rcases h2 with h2 | ⟨h2, h3⟩
         · omega
         · first | omega | (simp only [h3, b2n_false, ofNat0]; grind)
       · simp only [ofNat0]; grind)
    | (simp only [ofNat0]; grind)

end RcptP

end ZkFormal.Near.Render
