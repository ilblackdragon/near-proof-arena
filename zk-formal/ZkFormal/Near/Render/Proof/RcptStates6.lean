import ZkFormal.Near.Render.Proof.RcptStates5

/-!
# ZkFormal.Near.Render.Proof.RcptStates6 — `cStates` on the claim rows, padding; `states_ok`
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace RcptP

open RcptGen

theorem Cc_cl_st {c : Claim} {e : Ext} {i st : Nat} (hi : i < 12) (h1 : 4 ≤ st) (h2 : st ≤ 26) :
    Cc c e (.cl i) st = if st = 4 then 1 else 0 := by
  obtain ⟨st1, st0, -, -⟩ := state_cells (c := c) (e := e) (ρ := .cl i) hi
  split
  · subst_vars; exact st1
  · exact st0 st h1 h2 (by simpa [stateOf, Rcpt.sCL])

/-- **`cStates` (without bits) on a claim row.** -/
theorem cl_rows {c : Claim} {e : Ext} (hg : Good c e) {i : Nat} (hi : i < 12) {pub : List Fp} :
    ∀ x ∈ sB ++ sC ++ sD ++ sE ++ sF ++ sG ++ sH,
      evR (cF c e (.cl i)) (cF c e (nextOf (Df c e) (.cl i))) (decide (i = 0)) false pub x = 0 := by
  have hN := NN_pos hg
  obtain ⟨d0o, d0o2, d0rc, -, d0r⟩ := d_zero (c := c) (e := e) (by omega)
  have hst : ∀ i', i' < 12 → ∀ st, 4 ≤ st → st ≤ 26 → cF c e (.cl i') st = if st = 4 then 1 else 0 := by
    intro i' hi' st h1 h2; simp only [cF, Cc_cl_st hi' h1 h2]; split <;> rfl
  have hst' : ∀ st, 4 ≤ st → st ≤ 26 → cF c e (.seg 0 5 0) st = if st = 5 then 1 else 0 := by
    intro st h1 h2
    by_cases h4 : st = 4
    · subst h4; simp only [cF, Cc_four]; rfl
    · simp only [cF, Cc_state (by omega) h2]; split <;> rfl
  rcases (show i < 11 ∨ i = 11 by omega) with h11 | rfl
  · have hn : nextOf (Df c e) (.cl i) = .cl (i + 1) := by simp [nextOf, h11]
    rw [hn]
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with (((((hB | hC) | hD) | hE) | hF) | hG) | hH
    · simp only [sB, List.mem_cons, List.not_mem_nil, or_false] at hB
      rcases hB with rfl | rfl | rfl
      · simp only [evR_sub, onehot_rec (show RecOk (NN e) (Df c e) (.cl i) from hi), evR_c, cF, L_act, ofNat1]; grind
      all_goals simp only [evR_mul3, evR_not, evR_sub, evR_add, evR_c, evR_n, evR_k, cF, rcl,
        show ¬ (i = 11) by omega, show ¬ (i + 1 = 0) by omega, decide_false, b2n_false, ofNat0, ofNat1,
        ofNat_add_e, natCast_eq]
      all_goals grind
    · simp only [sC, List.mem_map] at hC
      obtain ⟨st, hs, rfl⟩ := hC
      have := states_range hs
      simp only [evR_mul3, evR_not, evR_sub, evR_c, evR_n, hst i hi st this.1 this.2,
        hst (i + 1) (by omega) st this.1 this.2]; grind
    · simp only [sD, List.mem_cons, List.not_mem_nil, or_false] at hD
      rcases hD with rfl | rfl <;>
        simp only [evR_mul3, evR_c, cF, L_fe, show ¬ (i = 11) by omega, decide_false, b2n_false, ofNat0] <;> grind
    · simp only [sE, List.mem_map] at hE
      obtain ⟨⟨st, ex⟩, -, rfl⟩ := hE
      simp only [evR_mul3, evR_c, cF, L_fe, show ¬ (i = 11) by omega, decide_false, b2n_false, ofNat0]; grind
    · simp only [sF, List.mem_map] at hF
      obtain ⟨⟨st, st', g⟩, -, rfl⟩ := hF
      simp only [evR_mul, evR_mul3, evR_c, cF, L_fe, show ¬ (i = 11) by omega, decide_false, b2n_false, ofNat0]
      grind
    · simp only [sG, List.mem_cons, List.not_mem_nil, or_false] at hG
      rcases hG with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      all_goals subst h
      all_goals simp only [evR_mul, evR_mul3, evR_sub, evR_add, evR_not, evR_c, evR_n, evR_k, evR_smul,
        evR_sum_cons, evR_sum_nil, evR_isFirst, evR_isLast, evR_isTransition, Rcpt.rowE, Rcpt.varE, cF, rcl,
        Bool.false_eq_true, ↓reduceIte, ofNat0, ofNat1, show ¬ (i = 11) by omega, decide_false, b2n_false]
      all_goals rfin
    · simp only [sH, List.mem_map] at hH
      obtain ⟨y, -, rfl⟩ := hH
      simp only [evR_mul3, Rcpt.rowE, evR_sub, evR_c, cF, L_act, L_sCL]; grind
  · have hn : nextOf (Df c e) (.cl 11) = .seg 0 5 0 := by simp [nextOf]
    rw [hn]
    have hfe : cF c e (.cl 11) Rcpt.fe = 1 := by simp only [cF, L_fe, decide_true, b2n_true]; rfl
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with (((((hB | hC) | hD) | hE) | hF) | hG) | hH
    · simp only [sB, List.mem_cons, List.not_mem_nil, or_false] at hB
      rcases hB with rfl | rfl | rfl
      · simp only [evR_sub, onehot_rec (show RecOk (NN e) (Df c e) (.cl 11) from hi), evR_c, cF, L_act, ofNat1]
        grind
      all_goals simp only [evR_mul3, evR_not, evR_c, hfe]; grind
    · simp only [sC, List.mem_map] at hC
      obtain ⟨st, -, rfl⟩ := hC
      simp only [evR_mul3, evR_not, evR_c, hfe]; grind
    · simp only [sD, List.mem_cons, List.not_mem_nil, or_false] at hD
      rcases hD with rfl | rfl <;>
        simp only [evR_mul3, evR_c, evR_n, evR_not, hfe, cF, L_rl, S_idx, S_fs, decide_true, b2n_true, ofNat0,
          ofNat1] <;> grind
    · simp only [sE, List.mem_map] at hE
      obtain ⟨⟨st, ex⟩, hm, rfl⟩ := hE
      simp only [evR_mul3, evR_c, evR_sub, hfe]
      simp only [Rcpt.lastIdx, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | hm
      · simp only [evR_k, cF, L_sCL, L_idx, natCast_eq, ofNat1]; grind
      · have : 5 ≤ st ∧ st ≤ 26 := by
          simp only [rcols] at hm; rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
            h | h | h | h | h <;> omega
        rw [hst 11 hi st (by omega) this.2, if_neg (by omega)]; grind
    · simp only [sF, List.mem_map] at hF
      obtain ⟨⟨st, st', g⟩, hm, rfl⟩ := hF
      simp only [evR_mul, evR_mul3, evR_c, evR_not, evR_n, hfe]
      simp only [Rcpt.succ, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl, rfl⟩ | hm
      · simp only [evR_k, cF, L_sCL, S_sPL, ↓reduceIte, natCast_eq, ofNat1]; grind
      · have : 5 ≤ st ∧ st ≤ 26 := by
          simp only [rcols] at hm; rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
            h | h | h | h | h <;> omega
        rw [hst 11 hi st (by omega) this.2, if_neg (by omega)]; grind
    · have hr0 : (Df c e 0).r = 0 := d0r
      simp only [sG, List.mem_cons, List.not_mem_nil, or_false] at hG
      rcases hG with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      all_goals subst h
      all_goals simp only [evR_mul, evR_mul3, evR_sub, evR_add, evR_not, evR_c, evR_n, evR_k, evR_smul,
        evR_sum_cons, evR_sum_nil, evR_isFirst, evR_isLast, evR_isTransition, Rcpt.rowE, Rcpt.varE, cF, rcl, rseg,
        Bool.false_eq_true, ↓reduceIte, ofNat0, ofNat1, decide_true, b2n_true, d0o, d0o2, d0rc, d0r]
      all_goals rfin
    · simp only [sH, List.mem_map] at hH
      obtain ⟨y, -, rfl⟩ := hH
      simp only [evR_mul3, Rcpt.rowE, evR_sub, evR_c, cF, L_act, L_sCL]; grind

end RcptP

end ZkFormal.Near.Render
