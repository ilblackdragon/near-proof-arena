import ZkFormal.Near.Render.Proof.RcptStates1

/-!
# ZkFormal.Near.Render.Proof.RcptStates2 — `cStates` inside a field (next row: same field, next index)
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace RcptP

open RcptGen

theorem Cc_state {c : Claim} {e : Ext} {r s i st : Nat} (h1 : 5 ≤ st) (h2 : st ≤ 26) :
    Cc c e (.seg r s i) st = if st = s then 1 else 0 := by
  rw [Cc_seg _ _ _ _ _ _ (by omega)]
  simp only [segCell, show st < 31 by omega, if_true, show st ≠ 0 by omega, show st ≠ 1 by omega,
    show st ≠ 2 by omega, show st ≠ 3 by omega, show st ≠ 27 by omega, show st ≠ 28 by omega,
    show st ≠ 29 by omega, show st ≠ 30 by omega, show st ≠ 4 by omega, if_false]

/-- State cells do not depend on the row index. -/
theorem state_indep {c : Claim} {e : Ext} {r s i i' st : Nat} (hst : st ∈ Rcpt.states) :
    Cc c e (.seg r s i) st = Cc c e (.seg r s i') st := by
  have := states_range hst
  by_cases h4 : st = 4
  · subst h4; rw [show (4 : Nat) = Rcpt.sCL from rfl, S_sCL, S_sCL]
  · rw [Cc_state (by omega) this.2, Cc_state (by omega) this.2]

/-- Receipt constants do not depend on the field and index. -/
theorem rconst_indep {c : Claim} {e : Ext} {r s i s' i' x : Nat} (hx : x ∈ Rcpt.rconsts) :
    Cc c e (.seg r s i) x = Cc c e (.seg r s' i') x := by
  simp only [Rcpt.rconsts, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [rseg]

theorem fe0 {c : Claim} {e : Ext} {r s i : Nat} (hfe : i + 1 < fLen (Df c e r) s) :
    cF c e (.seg r s i) Rcpt.fe = 0 := by
  simp only [cF, S_fe, show ¬ (i + 1 = fLen (Df c e r) s) by omega, decide_false, b2n_false]; rfl

theorem isRl_false {d : RD} {s i : Nat} (h : i + 1 ≠ fLen d s) : isRl d s i = false := by
  simp [isRl, h]

theorem oEnd_eq (d : RD) : Fp.ofNat (oEndOf d) = Fp.ofNat d.o + ((123 : Nat) : Fp) +
    (Fp.ofNat d.pred.length + (Fp.ofNat d.recv.length + (Fp.ofNat d.signer.length + ((32 : Nat) : Fp) *
      Fp.ofNat d.kt + 0))) := by
  simp only [oEndOf, ofNat_add_e, ofNat_mul_e, natCast_eq]; grind

theorem o2End_eq (d : RD) : Fp.ofNat (o2EndOf d) = Fp.ofNat d.o2 + Fp.ofNat (b2n d.hr) *
    (((129 : Nat) : Fp) + (((2 : Nat) : Fp) * Fp.ofNat d.signer.length + (((32 : Nat) : Fp) * Fp.ofNat d.kt + 0))) := by
  simp only [o2EndOf]
  cases d.hr <;> simp only [b2n_true, b2n_false, if_true, if_false, Bool.false_eq_true, ofNat_add_e, ofNat_mul_e,
    natCast_eq, ofNat0, ofNat1] <;> grind

/-- The literal boundary constraints `sG` on a segment row (any next row with the
given `act`, `rf`, `r`, … cells is handled by the caller through `hnx`). -/
theorem sG_inner {c : Claim} {e : Ext} {r s i : Nat} (hfe : i + 1 < fLen (Df c e r) s)
    (hge : (Df c e r).hr = true → (Df c e r).ge = true) {nx : Nat → Fp} {pub : List Fp}
    (hnx : nx Rcpt.act = 1) :
    ∀ x ∈ sG, evR (cF c e (.seg r s i)) nx false false pub x = 0 := by
  have hrl := isRl_false (d := Df c e r) (s := s) (i := i) (by omega)
  have hfe' : decide (i + 1 = fLen (Df c e r) s) = false := by simp; omega
  simp only [sG, List.forall_mem_cons, List.forall_mem_nil, and_true]
  and_intros
  all_goals (try simp only [evR_mul, evR_mul3, evR_sub, evR_add, evR_not, evR_c, evR_n, evR_k, evR_smul, evR_sum_cons,
    evR_sum_nil, evR_isFirst, evR_isLast, evR_isTransition, Rcpt.rowE, Rcpt.varE, cF, rseg, hrl, hfe', hnx,
    Bool.false_and, Bool.and_false, b2n_false, Bool.false_eq_true, ↓reduceIte, ofNat0, ofNat1])
  all_goals first
    | grind
    | (simp only [oEnd_eq, o2End_eq]; grind)
    | (cases h : (Df c e r).hr
       · simp only [b2n_false, ofNat0]; grind
       · simp only [hge h, b2n_true, ofNat1]; grind)
    | rfin

/-- **`cStates` (without bits) inside a field.** -/
theorem seg_inner {c : Claim} {e : Ext} {r s i : Nat} (hρ : RecOk (NN e) (Df c e) (.seg r s i))
    (hfe : i + 1 < fLen (Df c e r) s) (hge : (Df c e r).hr = true → (Df c e r).ge = true) {pub : List Fp} :
    ∀ x ∈ sB ++ sC ++ sD ++ sE ++ sF ++ sG ++ sH,
      evR (cF c e (.seg r s i)) (cF c e (.seg r s (i + 1))) false false pub x = 0 := by
  have h0 := fe0 hfe
  intro x hx
  simp only [List.mem_append] at hx
  rcases hx with (((((hB | hC) | hD) | hE) | hF) | hG) | hH
  · simp only [sB, List.mem_cons, List.not_mem_nil, or_false] at hB
    rcases hB with rfl | rfl | rfl
    · simp only [evR_sub, onehot_rec hρ, evR_c, cF, S_act, ofNat1]; grind
    · simp only [evR_mul3, evR_not, evR_sub, evR_add, evR_c, evR_n, evR_k, h0]
      simp only [cF, S_act, S_idx, ofNat_add_e, ofNat1, natCast_eq]; grind
    · simp only [evR_mul3, evR_not, evR_n, h0]
      simp only [cF, S_fs, Nat.add_one_ne_zero, decide_false, b2n_false, ofNat0]; grind
  · simp only [sC, List.mem_map] at hC
    obtain ⟨st, hst, rfl⟩ := hC
    simp only [evR_mul3, evR_not, evR_sub, evR_c, evR_n, h0]
    simp only [cF, state_indep (i := i + 1) (i' := i) hst]; grind
  · simp only [sD, List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl <;> simp only [evR_mul3, evR_c, h0] <;> grind
  · simp only [sE, List.mem_map] at hE
    obtain ⟨⟨st, ex⟩, -, rfl⟩ := hE
    simp only [evR_mul3, evR_c, h0]; grind
  · simp only [sF, List.mem_map] at hF
    obtain ⟨⟨st, st', g⟩, -, rfl⟩ := hF
    simp only [evR_mul, evR_mul3, evR_c, h0]; grind
  · exact sG_inner hfe hge (by simp only [cF, S_act]; rfl) x hG
  · simp only [sH, List.mem_map] at hH
    obtain ⟨y, hy, rfl⟩ := hH
    simp only [evR_mul3, evR_not, evR_sub, evR_c, evR_n, cF, rconst_indep (s := s) (i := i + 1) (s' := s) (i' := i) hy]
    grind

end RcptP

end ZkFormal.Near.Render
