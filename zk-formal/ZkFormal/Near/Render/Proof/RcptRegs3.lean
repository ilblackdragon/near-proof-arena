import ZkFormal.Near.Render.Proof.RcptRegs2

/-!
# ZkFormal.Near.Render.Proof.RcptRegs3 — `cRegs`: tokens kept (`rJ`), the claim rows

The tokens register is constant outside the `GP` rows (`tok_next`), and the
claim rows load / rotate their register blocks (`cl_regs`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

set_option linter.unusedSimpArgs false

namespace RcptP

open RcptGen

/-! ## Tokens kept -/

section
variable {c : WfClaim} {e : Ext} {r s i : Nat} {nx : Nat → Fp} {lst : Bool}

theorem rJ_keep (hn : ∀ j, j < 16 → nx (Rcpt.tok j) = cF c.1 e (.seg r s i) (Rcpt.tok j)) :
    ∀ x ∈ rJ, evR (cF c.1 e (.seg r s i)) nx false lst (publicOf c) x = 0 := by
  intro x hx
  simp only [rJ, List.mem_map, List.mem_range] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  simp only [evR_mul, evR_sub, evR_c, evR_n, hn j hj]; grind

theorem rJ_gp : ∀ x ∈ rJ, evR (cF c.1 e (.seg r 15 i)) nx false lst (publicOf c) x = 0 := by
  intro x hx
  simp only [rJ, List.mem_map, List.mem_range] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  have h0 : cF c.1 e (.seg r 15 i) Rcpt.lastR = 0 := by
    simp only [cF_lastR, isRl]; simp [b2n]; rfl
  simp only [evR_mul, evR_sub, evR_c, Rcpt.rowE, cF_act, cF_sCL, cF_sGP, h0, ↓reduceIte]; grind

theorem rJ_last (hrl : isRl (Df c.1 e r) s i = true) (hr : r + 1 = NN e) (hr0 : (Df c.1 e r).r = r)
    (hs : s ≠ 15) : ∀ x ∈ rJ, evR (cF c.1 e (.seg r s i)) nx false lst (publicOf c) x = 0 := by
  intro x hx
  simp only [rJ, List.mem_map, List.mem_range] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  have h1 : cF c.1 e (.seg r s i) Rcpt.lastR = 1 := by
    simp only [cF_lastR, hrl, hr0, hr, beq_self_eq_true, Bool.and_self, b2n_true]; rfl
  simp only [evR_mul, evR_sub, evR_c, Rcpt.rowE, cF_act, cF_sCL, cF_sGP, h1, hs, ↓reduceIte]; grind

end

/-- Outside `GP`, the tokens register does not depend on the row index. -/
theorem segTok_in {d : RD} {s i i' j : Nat} (hs : s ≠ 15) : segTok d s i j = segTok d s i' j := by
  simp only [segTok, hs, ↓reduceIte]

/-- Across a field boundary (not into or out of `GP`… or into it from `PK`). -/
theorem segTok_fe {d : RD} {s i j : Nat} (hs : s ∈ fields d.hr) (h15 : s ≠ 15) (h26 : s ≠ 26)
    (h23 : s = 23 → d.hr = true) (hj : j < 16) :
    segTok d (nextF d.hr s) 0 j = segTok d s i j := by
  have hs' : s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 ∨ s = 9 ∨ s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨
      s = 16 ∨ s = 17 ∨ s = 18 ∨ s = 19 ∨ s = 20 ∨ s = 21 ∨ s = 22 ∨ s = 23 ∨ s = 24 ∨ s = 25 := by
    cases hh : d.hr <;> simp only [fields, hh] at hs <;> simp at hs <;> omega
  rcases hs' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals (cases hh : d.hr <;> simp_all [segTok, nextF, beforeGP])

/-! ## Claim rows -/

section
variable {c : WfClaim} {e : Ext} {i : Nat}

theorem cl_A {j : Nat} (hj : j < 12) : cF c.1 e (.cl i) (Rcpt.reg j) = Fp.ofNat ((Cl.A (PA c.1 e)).getD ((i + j) % 12) 0) := by
  simp only [cF, L_reg c.1 e i (show j < 32 by omega), if_pos hj]
theorem cl_B {j : Nat} (hj : j < 4) : cF c.1 e (.cl i) (Rcpt.reg (12 + j)) = Fp.ofNat ((Cl.B (PA c.1 e)).getD ((i + j) % 4) 0) := by
  simp only [cF, L_reg c.1 e i (show 12 + j < 32 by omega)]
  simp (disch := omega) only [if_pos, if_neg, Nat.add_sub_cancel_left]
theorem cl_G {j : Nat} (hj : j < 8) : cF c.1 e (.cl i) (Rcpt.reg (16 + j)) = Fp.ofNat (Rcpt.G_LE.getD ((i + j) % 8) 0) := by
  simp only [cF, L_reg c.1 e i (show 16 + j < 32 by omega)]
  simp (disch := omega) only [if_pos, if_neg, Nat.add_sub_cancel_left]
theorem cl_D {j : Nat} (hj : j < 8) : cF c.1 e (.cl i) (Rcpt.reg (24 + j)) = Fp.ofNat ((Cl.D (PA c.1 e)).getD ((i + j) % 8) 0) := by
  simp only [cF, L_reg c.1 e i (show 24 + j < 32 by omega)]
  simp (disch := omega) only [if_pos, if_neg, Nat.add_sub_cancel_left]
theorem cl_T {j : Nat} (hj : j < 8) : cF c.1 e (.cl i) (Rcpt.tok j) = Fp.ofNat ((Cl.T (PA c.1 e)).getD ((i + j) % 8) 0) := by
  simp only [cF, L_tok c.1 e i (show j < 16 by omega), if_pos hj]

theorem rot_cl (hi : i < 12) {col : Nat → Nat} {len : Nat} {X : List Nat} (hlen : 0 < len)
    (hX : ∀ i' j, j < len → cF c.1 e (.cl i') (col j) = Fp.ofNat (X.getD ((i' + j) % len) 0)) {nx : Nat → Fp}
    (hn : i < 11 → nx = cF c.1 e (.cl (i + 1))) {fst : Bool} :
    ∀ x ∈ Rcpt.rot col len, evR (cF c.1 e (.cl i)) nx fst false (publicOf c) x = 0 := by
  intro x hx
  simp only [Rcpt.rot, List.mem_map, List.mem_range] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  simp only [evR_mul3, evR_not, evR_sub, evR_c, evR_n]
  rcases (show i < 11 ∨ i = 11 by omega) with h | rfl
  · rw [hn h, hX (i + 1) j hj, hX i _ (Nat.mod_lt _ hlen),
      Nat.add_mod_mod, show i + (j + 1) = i + 1 + j by omega]
    grind
  · simp only [cF, L_fe, decide_true, b2n_true, ofNat1]; grind

end

end RcptP

end ZkFormal.Near.Render
