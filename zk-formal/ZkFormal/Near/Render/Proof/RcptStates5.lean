import ZkFormal.Near.Render.Proof.RcptStates4

/-!
# ZkFormal.Near.Render.Proof.RcptStates5 — `cStates` on a field's last row (`seg_fe`, `seg_rl`, `seg_last`)
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace RcptP

open RcptGen

/-- Parts `sB`, `sC` vanish on a field's last row. -/
theorem sBC_fe {c : Claim} {e : Ext} {r s i : Nat} (hρ : RecOk (NN e) (Df c e) (.seg r s i))
    (hfe : i + 1 = fLen (Df c e r) s) {nx : Nat → Fp} {fst lst : Bool} {pub : List Fp} :
    ∀ x ∈ sB ++ sC, evR (cF c e (.seg r s i)) nx fst lst pub x = 0 := by
  have h1 := fe1 (c := c) (e := e) hfe
  intro x hx
  simp only [List.mem_append] at hx
  rcases hx with hB | hC
  · simp only [sB, List.mem_cons, List.not_mem_nil, or_false] at hB
    rcases hB with rfl | rfl | rfl
    · simp only [evR_sub, onehot_rec hρ, evR_c, cF, S_act, ofNat1]; grind
    all_goals simp only [evR_mul3, evR_not, evR_c, h1]; grind
  · simp only [sC, List.mem_map] at hC
    obtain ⟨st, -, rfl⟩ := hC
    simp only [evR_mul3, evR_not, evR_c, h1]; grind

theorem seg_fe {c : Claim} {e : Ext} {r s i : Nat} (hρ : RecOk (NN e) (Df c e) (.seg r s i))
    (hfe : i + 1 = fLen (Df c e r) s) (hrl : isRl (Df c e r) s i = false)
    (hge : (Df c e r).hr = true → (Df c e r).ge = true) {pub : List Fp} :
    ∀ x ∈ sB ++ sC ++ sD ++ sE ++ sF ++ sG ++ sH,
      evR (cF c e (.seg r s i)) (cF c e (.seg r (nextF (Df c e r).hr s) 0)) false false pub x = 0 := by
  have h1 := fe1 (c := c) (e := e) hfe
  have hrl0 : cF c e (.seg r s i) Rcpt.rl = 0 := by simp only [cF, S_rl, hrl, b2n_false]; rfl
  intro x hx
  simp only [List.mem_append] at hx
  rcases hx with (((((hB | hC) | hD) | hE) | hF) | hG) | hH
  · exact sBC_fe hρ hfe x (List.mem_append_left _ hB)
  · exact sBC_fe hρ hfe x (List.mem_append_right _ hC)
  · simp only [sD, List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl <;>
      simp only [evR_mul3, evR_not, evR_c, evR_n, h1, hrl0, cF, S_idx, S_fs, decide_true, b2n_true, ofNat0,
        ofNat1] <;> grind
  · exact sE_end hfe x hE
  · exact sF_fe hfe (fun st h5 h26 => by simp only [cF, Cc_state h5 h26]; split <;> rfl) x hF
  · exact sG_fe hfe hrl hge (by simp only [cF, S_act]; rfl) x hG
  · simp only [sH, List.mem_map] at hH
    obtain ⟨y, hy, rfl⟩ := hH
    simp only [evR_mul3, evR_not, evR_sub, evR_c, evR_n, hrl0, cF,
      rconst_indep (s := nextF (Df c e r).hr s) (i := 0) (s' := s) (i' := i) hy]
    grind

theorem seg_rl {c : Claim} {e : Ext} (hg : Good c e) {r s i : Nat} (hρ : RecOk (NN e) (Df c e) (.seg r s i))
    (hfe : i + 1 = fLen (Df c e r) s) (hrl : isRl (Df c e r) s i = true) (hr : r + 1 < NN e) {pub : List Fp} :
    ∀ x ∈ sB ++ sC ++ sD ++ sE ++ sF ++ sG ++ sH,
      evR (cF c e (.seg r s i)) (cF c e (.seg (r + 1) 5 0)) false false pub x = 0 := by
  have hrl1 : cF c e (.seg r s i) Rcpt.rl = 1 := by simp only [cF, S_rl, hrl, b2n_true]; rfl
  intro x hx
  simp only [List.mem_append] at hx
  rcases hx with (((((hB | hC) | hD) | hE) | hF) | hG) | hH
  · exact sBC_fe hρ hfe x (List.mem_append_left _ hB)
  · exact sBC_fe hρ hfe x (List.mem_append_right _ hC)
  · simp only [sD, List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl <;> simp only [evR_mul3, evR_not, evR_c, hrl1] <;> grind
  · exact sE_end hfe x hE
  · exact sF_rl hfe hrl x hF
  · exact sG_rl hg hfe hrl hr x hG
  · simp only [sH, List.mem_map] at hH
    obtain ⟨y, -, rfl⟩ := hH
    simp only [evR_mul3, evR_not, evR_c, hrl1]; grind

theorem seg_last {c : Claim} {e : Ext} {r s i : Nat} (hρ : RecOk (NN e) (Df c e) (.seg r s i))
    (hfe : i + 1 = fLen (Df c e r) s) (hrl : isRl (Df c e r) s i = true) (hr : r + 1 = NN e)
    (hr0 : (Df c e r).r = r) (hge : (Df c e r).hr = true → (Df c e r).ge = true) {pub : List Fp} :
    ∀ x ∈ sB ++ sC ++ sD ++ sE ++ sF ++ sG ++ sH,
      evR (cF c e (.seg r s i)) (fun _ => 0) false false pub x = 0 := by
  have hrl1 : cF c e (.seg r s i) Rcpt.rl = 1 := by simp only [cF, S_rl, hrl, b2n_true]; rfl
  intro x hx
  simp only [List.mem_append] at hx
  rcases hx with (((((hB | hC) | hD) | hE) | hF) | hG) | hH
  · exact sBC_fe hρ hfe x (List.mem_append_left _ hB)
  · exact sBC_fe hρ hfe x (List.mem_append_right _ hC)
  · simp only [sD, List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl <;> simp only [evR_mul3, evR_not, evR_c, hrl1] <;> grind
  · exact sE_end hfe x hE
  · exact sF_rl hfe hrl x hF
  · exact sG_last hfe hrl hr hr0 hge x hG
  · simp only [sH, List.mem_map] at hH
    obtain ⟨y, -, rfl⟩ := hH
    simp only [evR_mul3, evR_not, evR_c, hrl1]; grind

end RcptP

end ZkFormal.Near.Render
