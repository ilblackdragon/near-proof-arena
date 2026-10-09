import ZkFormal.NearV3.Assembly.RcptDepositNativeData

/- Arithmetic proof adaptation from Near/Render/Proof/RcptDepF.lean.
Source SHA256: 49dd9da7e44cf86a3d19d5b4a8ee81ef9715deef50a231714493898c4b73284f
Change: require only DepositArithmeticOk; drop unused version/r<512 hypotheses.
Scalar Seg byte/carry definitions are reused unchanged, not native index metadata. -/
namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Algebra ZkFormal.Near.Render RcptGen RcptP
set_option linter.unusedSectionVars false

section
variable {d : RD} (h : DepositArithmeticOk d)
include h

theorem deposit_stor_hi {i : Nat} (hi : 8 ≤ i) : Seg.stB d i = 0 := by
  simp only [Seg.stB, leBytes_getD, show ¬ i < 8 by omega, ↓reduceIte]

theorem deposit_V_stB {k : Nat} (hk : 8 ≤ k) : V (Seg.stB d) k = d.stor := V_leBytes_of hk h.stor_lt

/-! ## `aft = bef + dep` -/

theorem deposit_V_y1 : V (Seg.y1 d) 16 = d.bef + d.dep := by
  rw [show Seg.y1 d = fun i => Seg.befB d i + Seg.depB d i from rfl, V_add]
  have e1 : V (Seg.befB d) 16 = d.bef := V_leBytes_of (Nat.le_refl _) (by have := h.aft_lt; omega)
  have e2 : V (Seg.depB d) 16 = d.dep := V_leBytes_of (Nat.le_refl _) (by have := h.aft_lt; omega)
  rw [e1, e2]

theorem deposit_sa_mod {i : Nat} (hi : i < 16) : Seg.sa d i % 256 = Seg.aftB d i := chain_byte _ hi (deposit_V_y1 h)

theorem deposit_y1_le (i : Nat) : Seg.y1 d i ≤ 510 := by
  simp only [Seg.y1, Seg.befB, Seg.depB]
  have := leBytes_getD_lt 16 d.bef i; have := leBytes_getD_lt 16 d.dep i; omega

theorem deposit_c1d_le (i : Nat) : chain (Seg.y1 d) i ≤ 1 := chain_le _ (fun j => by have := deposit_y1_le h j; omega) i
theorem deposit_sa_div (i : Nat) : Seg.sa d i / 256 = chain (Seg.y1 d) (i + 1) := by simp only [Seg.sa, chain]
theorem deposit_c1d_final : chain (Seg.y1 d) 16 = 0 := chain_zero_of _ (by rw [deposit_V_y1 h]; have := h.aft_lt; omega)

/-! ## `tot = aft + locked` -/

theorem deposit_V_y2 : V (Seg.y2 d) 16 = d.bef + d.dep + d.locked := by
  rw [show Seg.y2 d = fun i => Seg.aftB d i + Seg.lkB d i from rfl, V_add]
  have e1 : V (Seg.aftB d) 16 = d.bef + d.dep := V_leBytes_of (Nat.le_refl _) (by have := h.aft_lt; omega)
  have e2 : V (Seg.lkB d) 16 = d.locked := V_leBytes_of (Nat.le_refl _) (by have := h.tot_lt; omega)
  rw [e1, e2]

theorem deposit_stt_mod {i : Nat} (hi : i < 16) : Seg.stt d i % 256 = Seg.totB d i := chain_byte _ hi (deposit_V_y2 h)

theorem deposit_y2_le (i : Nat) : Seg.y2 d i ≤ 510 := by
  simp only [Seg.y2, Seg.aftB, Seg.lkB]
  have := leBytes_getD_lt 16 (d.bef + d.dep) i; have := leBytes_getD_lt 16 d.locked i; omega

theorem deposit_c2d_le (i : Nat) : chain (Seg.y2 d) i ≤ 1 := chain_le _ (fun j => by have := deposit_y2_le h j; omega) i
theorem deposit_stt_div (i : Nat) : Seg.stt d i / 256 = chain (Seg.y2 d) (i + 1) := by simp only [Seg.stt, chain]
theorem deposit_c2d_final : chain (Seg.y2 d) 16 = 0 := chain_zero_of _ (by rw [deposit_V_y2 h]; exact h.tot_lt)

/-! ## `q = 10^19 · storage` -/

theorem deposit_q_lt : 10000000000000000000 * d.stor < 256 ^ 16 := by
  have := h.stor_lt
  have e8 : (256 : Nat) ^ 8 = 18446744073709551616 := by decide
  have e16 : (256 : Nat) ^ 16 = 340282366920938463463374607431768211456 := by decide
  omega

theorem deposit_V_y3 : V (Seg.y3 d) 16 = 10000000000000000000 * d.stor := by
  simp only [Seg.y3]
  rw [V_convS, deposit_V_stB h (by omega), deposit_V_stB h (by omega), deposit_V_stB h (by omega), deposit_V_stB h (by omega), deposit_V_stB h (by omega),
    deposit_V_stB h (by omega)]
  omega

theorem deposit_sq_mod {i : Nat} (hi : i < 16) : Seg.sq d i % 256 = Seg.qB d i := chain_byte _ hi (deposit_V_y3 h)

theorem deposit_y3_le (i : Nat) : Seg.y3 d i ≤ 189975 :=
  convS_le _ (fun i => Nat.le_of_lt_succ (leBytes_getD_lt 8 d.stor i)) i

theorem deposit_c3d_le (i : Nat) : chain (Seg.y3 d) i ≤ 745 := chain_le _ (fun j => by have := deposit_y3_le h j; omega) i
theorem deposit_sq_div (i : Nat) : Seg.sq d i / 256 = chain (Seg.y3 d) (i + 1) := by simp only [Seg.sq, chain]
theorem deposit_c3d_final : chain (Seg.y3 d) 16 = 0 := chain_zero_of _ (by rw [deposit_V_y3 h]; exact deposit_q_lt h)

/-! ## `tot − q` -/

theorem deposit_totB_lt (i : Nat) : Seg.totB d i < 256 := leBytes_getD_lt _ _ _
theorem deposit_qB_lt (i : Nat) : Seg.qB d i < 256 := leBytes_getD_lt _ _ _
theorem deposit_dbr_le (i : Nat) : Seg.dbr d i ≤ 1 := bchain_le _ _ _ i (by decide)
theorem deposit_ddv_lt (i : Nat) : Seg.ddv d i < 256 := bdig_lt _ _ _ (deposit_totB_lt h) (deposit_qB_lt h) (by decide) i
theorem deposit_ddv_step (i : Nat) : Seg.totB d i + 256 * Seg.dbr d (i + 1) = Seg.qB d i + Seg.dbr d i + Seg.ddv d i :=
  (bdig_step _ _ _ (deposit_totB_lt h) (deposit_qB_lt h) (by decide) i).1
theorem deposit_dbr_zero : Seg.dbr d 0 = 0 := rfl

theorem deposit_dbr_final (hb : d.big = true) : Seg.dbr d 16 = 0 := by
  have := bchain_final (Seg.totB d) (Seg.qB d) 0 (deposit_totB_lt h) (deposit_qB_lt h) (by decide) 16
  have e1 : V (Seg.totB d) 16 = d.bef + d.dep + d.locked := V_leBytes_of (Nat.le_refl _) h.tot_lt
  have e2 : V (Seg.qB d) 16 = 10000000000000000000 * d.stor := V_leBytes_of (Nat.le_refl _) (deposit_q_lt h)
  rw [e1, e2] at this
  have hb' := h.big; rw [hb] at hb'
  simp only [true_eq_decide_iff] at hb'
  simp only [Seg.dbr, this]; rw [if_neg (by omega)]

/-! ## `aft ≠ u128::MAX` -/

theorem deposit_runA_succ (i : Nat) : Seg.runA d (i + 1) = Seg.runA d i + (255 - Seg.aftB d (i + 1)) := runSum_succ _ _
theorem deposit_runA_zero : Seg.runA d 0 = 255 - Seg.aftB d 0 := runSum_zero _

theorem deposit_runA_ne : Seg.runA d 15 ≠ 0 := by
  intro h0
  have hz := runSum_eq0 _ 15 h0
  have h255 : ∀ j, j < 16 → Seg.aftB d j = 255 := by
    intro j hj; have := hz j (by omega); have := leBytes_getD_lt 16 (d.bef + d.dep) j
    simp only [Seg.aftB] at *; omega
  have hV := V_congr (x := Seg.aftB d) (y := fun _ => 255) 16 h255
  rw [show Seg.aftB d = fun i => (leBytes 16 (d.bef + d.dep)).getD i 0 from rfl,
    V_leBytes_of (Nat.le_refl _) (by have := h.aft_lt; omega)] at hV
  have := V_const255 16
  have := h.aft_lt
  omega

theorem deposit_runA_lt (i : Nat) (hi : i < 16) : Seg.runA d i < 4096 := by
  have := runSum_le (fun j => 255 - Seg.aftB d j) 255 (fun j => by omega) i
  have : (i + 1) * 255 ≤ 16 * 255 := Nat.mul_le_mul_right _ (by omega)
  simp only [Seg.runA]; omega

/-! ## Storage without `big` -/

theorem deposit_stor_small (hb : d.big = false) : Seg.stB d 0 + 256 * Seg.stB d 1 = d.stor := by
  have := h.stake hb
  have h2 := V_leBytes 8 d.stor 2
  simp only [V, Nat.min_eq_left (show 2 ≤ 8 by decide)] at h2
  rw [Nat.mod_eq_of_lt (by omega)] at h2
  simp only [Seg.stB]; omega

theorem deposit_stB_small (hb : d.big = false) {i : Nat} (hi : 2 ≤ i) : Seg.stB d i = 0 := by
  have := h.stake hb
  simp only [Seg.stB, leBytes_getD]
  split
  · have : 256 ^ 2 ≤ 256 ^ i := Nat.pow_le_pow_right (by decide) hi
    rw [Nat.div_eq_of_lt (by omega)]
  · rfl

end


end ZkFormal.NearV3.Assembly.RcptSkeleton
