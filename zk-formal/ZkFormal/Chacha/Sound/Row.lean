import ZkFormal.Chacha.Sound.Kind

/-!
# ZkFormal.Chacha.Sound.Row — one quarter-round row

On a `Q` row at position `p` with all state limbs `< 2^16` (`Ranged`), the next row's
state is `qrStep p` of this row's state, and is again `Ranged` (`qr_row`).
-/

namespace ZkFormal.Chacha.Sound

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table NearSpecV3

variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

/-- State slot `i` as a word. -/
def sw (tr : Trace Fp) (t r i : Nat) : Nat := nv tr t r (colS i 0) + 65536 * nv tr t r (colS i 1)

/-- The state of row `r` as an array. -/
def stA (tr : Trace Fp) (t r : Nat) : Array Nat := ((List.range 16).map (sw tr t r)).toArray

theorem stA_size (r : Nat) : (stA tr t r).size = 16 := by simp [stA]

theorem stA_get {r i : Nat} (hi : i < 16) : (stA tr t r)[i]! = sw tr t r i := by
  simp [stA, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, hi]

def Ranged (tr : Trace Fp) (t r : Nat) : Prop := ∀ i, i < 16 → ∀ l, l < 2 → nv tr t r (colS i l) < 65536

/-- Bit-word `m` of row `r`. -/
def xw (tr : Trace Fp) (t r m : Nat) : Nat := nbits (fun b => nv tr t r (colX m b)) 32

theorem xw_lt (hL : ChLocal tr t pub) {r m : Nat} (hr : r < tr.height t) (hm : m < 6) :
    xw tr t r m < 2 ^ 32 := nbits_lt (fun b hb => bX hL hr hm hb)

theorem bitsX (hL : ChLocal tr t pub) {r m : Nat} (hr : r < tr.height t) (hm : m < 6) :
    BitsOf (tenv tr t r pub) (xb m) (xw tr t r m) :=
  bitsOf_cols (col := colX m) (fun b hb => bX hL hr hm hb)

theorem limb_lt (w l : Nat) : (w / 2 ^ (16 * l)) % 65536 < 65536 := Nat.mod_lt _ (by decide)

/-- `w` from its two limbs. -/
theorem word_limbs {w : Nat} (hw : w < 2 ^ 32) :
    w = (w / 2 ^ (16 * 0)) % 65536 + 65536 * ((w / 2 ^ (16 * 1)) % 65536) := by
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.mul_one]; omega

theorem grp_facts {p : Nat} (hp : p < 8) :
    (grp p).1 < 16 ∧ (grp p).2.1 < 16 ∧ (grp p).2.2.1 < 16 ∧ (grp p).2.2.2 < 16 ∧
    (grp p).1 ≠ (grp p).2.1 ∧ (grp p).1 ≠ (grp p).2.2.1 ∧ (grp p).1 ≠ (grp p).2.2.2 ∧
    (grp p).2.1 ≠ (grp p).2.2.1 ∧ (grp p).2.1 ≠ (grp p).2.2.2 ∧ (grp p).2.2.1 ≠ (grp p).2.2.2 := by
  rcases (show p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Limb `l` of `w`, as an integer. -/
def Lm (w l : Nat) : Int := (((w / 2 ^ (16 * l)) % 65536 : Nat) : Int)

/-- Carry-in of limb `l` of addition `q` on row `r`. -/
def ci (tr : Trace Fp) (t r q l : Nat) : Int := if l = 0 then 0 else (nv tr t r (colC q 0) : Int)

theorem zev_cin (Z : ZEnv) (q l : Nat) (hl : l < 2) :
    zev Z (cin q l) = if l = 0 then 0 else (Z.cur (colC q 0) : Int) := by
  unfold cin; split <;> simp

theorem mem_cQR' {q : Nat} (hq : q < 12) : E.sel colP 8 (fun p => qrC (grp p) q) ∈ constraints :=
  mem_cQR (List.mem_map.mpr ⟨q, List.mem_range.mpr hq, rfl⟩)

theorem Lm_lt (w l : Nat) : 0 ≤ Lm w l ∧ Lm w l < 65536 := by
  unfold Lm; have := limb_lt w l; omega

/-- 32-bit addition from two limb equations with carries. -/
theorem add_limbs {a b r c0 c1 : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (hrr : r < 2 ^ 32)
    (hc0 : c0 ≤ 1) (hc1 : c1 ≤ 1)
    (h0 : (Lm a 0 + Lm b 0 - (Lm r 0 + 65536 * c0) : Int) = 0)
    (h1 : (Lm a 1 + Lm b 1 + c0 - (Lm r 1 + 65536 * c1) : Int) = 0) : r = add32 a b := by
  unfold Lm at h0 h1; unfold add32 M32
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.mul_one] at h0 h1
  omega

/-- Same, with the first summand given by its limbs (a ranged state slot). -/
theorem add_limbs' {a0 a1 b r c0 c1 : Nat} (ha0 : a0 < 65536) (ha1 : a1 < 65536) (hb : b < 2 ^ 32)
    (hrr : r < 2 ^ 32) (hc0 : c0 ≤ 1) (hc1 : c1 ≤ 1)
    (h0 : ((a0 : Int) + Lm b 0 - (Lm r 0 + 65536 * c0) : Int) = 0)
    (h1 : ((a1 : Int) + Lm b 1 + c0 - (Lm r 1 + 65536 * c1) : Int) = 0) :
    r = add32 (a0 + 65536 * a1) b := by
  unfold Lm at h0 h1; unfold add32 M32
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.mul_one] at h0 h1
  omega

/-- A ranged slot equal limb-wise to a word. -/
theorem slot_word {s0 s1 w : Nat} (hw : w < 2 ^ 32)
    (h0 : (Lm w 0 - s0 : Int) = 0) (h1 : (Lm w 1 - s1 : Int) = 0) : s0 + 65536 * s1 = w := by
  unfold Lm at h0 h1
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.mul_one] at h0 h1
  omega

/-! ## The words of a quarter-round row -/

section
variable (hL : ChLocal tr t pub) {r : Nat} (hr : r + 1 < tr.height t)

/-- The rotated-xor words: `D1 = rotl(x1 ⊕ x2, 16)` etc. -/
def wD1 (tr : Trace Fp) (t r : Nat) : Nat := rotl32 (xw tr t r 1 ^^^ xw tr t r 2) 16
def wB1 (tr : Trace Fp) (t r : Nat) : Nat := rotl32 (xw tr t r 0 ^^^ xw tr t r 3) 12
def wD2 (tr : Trace Fp) (t r : Nat) : Nat := rotl32 (wD1 tr t r ^^^ xw tr t r 4) 8
def wB2 (tr : Trace Fp) (t r : Nat) : Nat := rotl32 (wB1 tr t r ^^^ xw tr t r 5) 7

include hL hr

theorem hr0' : r < tr.height t := by omega

theorem wD1_lt : wD1 tr t r < 2 ^ 32 :=
  rotl32_lt (xor_lt32 (xw_lt hL (hr0' hL hr) (by decide)) (xw_lt hL (hr0' hL hr) (by decide))) _ (by decide)
theorem wB1_lt : wB1 tr t r < 2 ^ 32 :=
  rotl32_lt (xor_lt32 (xw_lt hL (hr0' hL hr) (by decide)) (xw_lt hL (hr0' hL hr) (by decide))) _ (by decide)
theorem wD2_lt : wD2 tr t r < 2 ^ 32 :=
  rotl32_lt (xor_lt32 (wD1_lt hL hr) (xw_lt hL (hr0' hL hr) (by decide))) _ (by decide)
theorem wB2_lt : wB2 tr t r < 2 ^ 32 :=
  rotl32_lt (xor_lt32 (wB1_lt hL hr) (xw_lt hL (hr0' hL hr) (by decide))) _ (by decide)

theorem bitsD1 : BitsOf (tenv tr t r pub) d1 (wD1 tr t r) :=
  bitsOf_rot (f := fun b => E.xor2 (xb 1 b) (xb 2 b))
    (bitsOf_xor (bitsX hL (hr0' hL hr) (by decide)) (bitsX hL (hr0' hL hr) (by decide)))
    (xor_lt32 (xw_lt hL (hr0' hL hr) (by decide)) (xw_lt hL (hr0' hL hr) (by decide)))
    (by decide) (by decide)

theorem bitsB1 : BitsOf (tenv tr t r pub) b1 (wB1 tr t r) :=
  bitsOf_rot (f := fun b => E.xor2 (xb 0 b) (xb 3 b))
    (bitsOf_xor (bitsX hL (hr0' hL hr) (by decide)) (bitsX hL (hr0' hL hr) (by decide)))
    (xor_lt32 (xw_lt hL (hr0' hL hr) (by decide)) (xw_lt hL (hr0' hL hr) (by decide)))
    (by decide) (by decide)

theorem bitsD2 : BitsOf (tenv tr t r pub) d2 (wD2 tr t r) :=
  bitsOf_rot (f := fun b => E.xor2 (d1 b) (xb 4 b))
    (bitsOf_xor (bitsD1 hL hr) (bitsX hL (hr0' hL hr) (by decide)))
    (xor_lt32 (wD1_lt hL hr) (xw_lt hL (hr0' hL hr) (by decide)))
    (by decide) (by decide)

theorem bitsB2 : BitsOf (tenv tr t r pub) b2 (wB2 tr t r) :=
  bitsOf_rot (f := fun b => E.xor2 (b1 b) (xb 5 b))
    (bitsOf_xor (bitsB1 hL hr) (bitsX hL (hr0' hL hr) (by decide)))
    (xor_lt32 (wB1_lt hL hr) (xw_lt hL (hr0' hL hr) (by decide)))
    (by decide) (by decide)

/-! ## The inner constraints evaluate to small integers -/

/-- Integer value of inner quarter-round constraint `q` on row `r`. -/
theorem zev_qrC (g : Nat × Nat × Nat × Nat) (l : Nat) (hl : l < 2) :
    zev (tenv tr t r pub) (qrC g (2 * 0 + l)) = Lm (xw tr t r 0) l - nv tr t r (colS g.2.1 l) ∧
    zev (tenv tr t r pub) (qrC g (2 * 1 + l)) = Lm (xw tr t r 1) l - nv tr t r (colS g.2.2.2 l) ∧
    zev (tenv tr t r pub) (qrC g (2 * 2 + l)) = (nv tr t r (colS g.1 l) : Int) + Lm (xw tr t r 0) l +
        ci tr t r 0 l - (Lm (xw tr t r 2) l + 65536 * nv tr t r (colC 0 l)) ∧
    zev (tenv tr t r pub) (qrC g (2 * 3 + l)) = (nv tr t r (colS g.2.2.1 l) : Int) + Lm (wD1 tr t r) l +
        ci tr t r 1 l - (Lm (xw tr t r 3) l + 65536 * nv tr t r (colC 1 l)) ∧
    zev (tenv tr t r pub) (qrC g (2 * 4 + l)) = Lm (xw tr t r 2) l + Lm (wB1 tr t r) l + ci tr t r 2 l -
        (Lm (xw tr t r 4) l + 65536 * nv tr t r (colC 2 l)) ∧
    zev (tenv tr t r pub) (qrC g (2 * 5 + l)) = Lm (xw tr t r 3) l + Lm (wD2 tr t r) l + ci tr t r 3 l -
        (Lm (xw tr t r 5) l + 65536 * nv tr t r (colC 3 l)) := by
  have e2 : ∀ k, (2 * k + l) / 2 = k := fun k => by omega
  have e3 : ∀ k, (2 * k + l) % 2 = l := fun k => by omega
  have hX := fun m (hm : m < 6) => zev_limb (bitsX hL (hr0' hL hr) hm (pub := pub)) hl
  have hci : ∀ q, zev (tenv tr t r pub) (cin q l) = ci tr t r q l := fun q => by
    rw [zev_cin _ q l hl]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [qrC, e2, e3, zev_sub, zev_addE, sC, zev_c, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, hci, cur_eq, hX 0 (by decide), hX 1 (by decide),
      hX 2 (by decide), hX 3 (by decide), hX 4 (by decide), hX 5 (by decide),
      zev_limb (bitsD1 hL hr) hl, zev_limb (bitsB1 hL hr) hl, zev_limb (bitsD2 hL hr) hl, Lm]
    try omega

/-! ## Selection on a `Q` row -/

theorem P_others {p : Nat} (hp : p < 8) (hP : nv tr t r (colP p) = 1) :
    ∀ x, x < 8 → x ≠ p → nv tr t r (colP x) = 0 := fun x hx hxp =>
  flag_unique hL (hr0' hL hr) (mem_flag_P hp) (mem_flag_P hx) (fun h => hxp (by unfold colP at h; omega)) hP

theorem zev_selP {p : Nat} (hp : p < 8) (hP : nv tr t r (colP p) = 1) (f : Nat → Expr) :
    zev (tenv tr t r pub) (E.sel colP 8 f) = zev (tenv tr t r pub) (f p) :=
  zev_sel _ colP 8 f p hp hP (P_others hL hr hp hP)

theorem ci_le (q l : Nat) (hq : q < 4) : 0 ≤ ci tr t r q l ∧ ci tr t r q l ≤ 1 := by
  unfold ci; have := bC hL (hr0' hL hr) hq (show 0 < 2 by decide); split <;> omega

/-- The 12 inner constraints of a `Q` row vanish as integers. -/
theorem qr_zero {p : Nat} (hp : p < 8) (hP : nv tr t r (colP p) = 1) (hR : Ranged tr t r)
    {q : Nat} (hq : q < 12) : zev (tenv tr t r pub) (qrC (grp p) q) = 0 := by
  have hz := zc hL (hr0' hL hr) (mem_cQR' hq)
  rw [zev_selP hL hr hp hP] at hz
  obtain ⟨k, l, hl, rfl, hk⟩ : ∃ k l, l < 2 ∧ q = 2 * k + l ∧ k < 6 := ⟨q / 2, q % 2, by omega, by omega, by omega⟩
  have hf := grp_facts hp
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := zev_qrC hL hr (pub := pub) (grp p) l hl
  have hS : ∀ i, i < 16 → nv tr t r (colS i l) < 65536 := fun i hi => hR i hi l hl
  have hC : ∀ q, q < 4 → nv tr t r (colC q l) ≤ 1 := fun q hq => bC hL (hr0' hL hr) hq hl
  have L0 := Lm_lt (xw tr t r 0) l; have L1 := Lm_lt (xw tr t r 1) l
  have L2 := Lm_lt (xw tr t r 2) l; have L3 := Lm_lt (xw tr t r 3) l
  have L4 := Lm_lt (xw tr t r 4) l; have L5 := Lm_lt (xw tr t r 5) l
  have L6 := Lm_lt (wD1 tr t r) l; have L7 := Lm_lt (wB1 tr t r) l; have L8 := Lm_lt (wD2 tr t r) l
  have c0 := ci_le hL hr (r := r) 0 l (by decide); have c1 := ci_le hL hr (r := r) 1 l (by decide)
  have c2 := ci_le hL hr (r := r) 2 l (by decide); have c3 := ci_le hL hr (r := r) 3 l (by decide)
  have := hS _ hf.1; have := hS _ hf.2.1; have := hS _ hf.2.2.1; have := hS _ hf.2.2.2.1
  have := hC 0 (by decide); have := hC 1 (by decide); have := hC 2 (by decide); have := hC 3 (by decide)
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl
  · rw [e0] at hz ⊢; exact hz (by omega) (by omega)
  · rw [e1] at hz ⊢; exact hz (by omega) (by omega)
  · rw [e2] at hz ⊢; exact hz (by omega) (by omega)
  · rw [e3] at hz ⊢; exact hz (by omega) (by omega)
  · rw [e4] at hz ⊢; exact hz (by omega) (by omega)
  · rw [e5] at hz ⊢; exact hz (by omega) (by omega)

/-- **The words of a `Q` row.** -/
theorem qr_words {p : Nat} (hp : p < 8) (hP : nv tr t r (colP p) = 1) (hR : Ranged tr t r) :
    sw tr t r (grp p).2.1 = xw tr t r 0 ∧ sw tr t r (grp p).2.2.2 = xw tr t r 1 ∧
    xw tr t r 2 = add32 (sw tr t r (grp p).1) (xw tr t r 0) ∧
    xw tr t r 3 = add32 (sw tr t r (grp p).2.2.1) (wD1 tr t r) ∧
    xw tr t r 4 = add32 (xw tr t r 2) (wB1 tr t r) ∧
    xw tr t r 5 = add32 (xw tr t r 3) (wD2 tr t r) := by
  have z := fun q (hq : q < 12) => qr_zero hL hr hp hP hR (pub := pub) hq
  obtain ⟨a0, b0, c0, d0, e0, f0⟩ := zev_qrC hL hr (pub := pub) (grp p) 0 (by decide)
  obtain ⟨a1, b1, c1, d1, e1, f1⟩ := zev_qrC hL hr (pub := pub) (grp p) 1 (by decide)
  have hf := grp_facts hp
  have X := fun m (hm : m < 6) => xw_lt hL (hr0' hL hr) (m := m) hm
  have hC : ∀ q l, q < 4 → l < 2 → nv tr t r (colC q l) ≤ 1 := fun q l hq hl => bC hL (hr0' hL hr) hq hl
  have ci0 : ∀ q, ci tr t r q 0 = 0 := fun q => rfl
  have ci1 : ∀ q, ci tr t r q 1 = nv tr t r (colC q 0) := fun q => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact slot_word (X 0 (by decide)) (by rw [← a0]; exact z _ (by decide)) (by rw [← a1]; exact z _ (by decide))
  · exact slot_word (X 1 (by decide)) (by rw [← b0]; exact z _ (by decide)) (by rw [← b1]; exact z _ (by decide))
  · have h0 := z 4 (by decide); have h1 := z 5 (by decide)
    rw [show (4 : Nat) = 2 * 2 + 0 from rfl, c0, ci0] at h0
    rw [show (5 : Nat) = 2 * 2 + 1 from rfl, c1, ci1] at h1
    exact add_limbs' (hR _ hf.1 0 (by decide)) (hR _ hf.1 1 (by decide)) (X 0 (by decide)) (X 2 (by decide))
      (hC 0 0 (by decide) (by decide)) (hC 0 1 (by decide) (by decide)) (by omega) (by omega)
  · have h0 := z 6 (by decide); have h1 := z 7 (by decide)
    rw [show (6 : Nat) = 2 * 3 + 0 from rfl, d0, ci0] at h0
    rw [show (7 : Nat) = 2 * 3 + 1 from rfl, d1, ci1] at h1
    exact add_limbs' (hR _ hf.2.2.1 0 (by decide)) (hR _ hf.2.2.1 1 (by decide)) (wD1_lt hL hr) (X 3 (by decide))
      (hC 1 0 (by decide) (by decide)) (hC 1 1 (by decide) (by decide)) (by omega) (by omega)
  · have h0 := z 8 (by decide); have h1 := z 9 (by decide)
    rw [show (8 : Nat) = 2 * 4 + 0 from rfl, e0, ci0] at h0
    rw [show (9 : Nat) = 2 * 4 + 1 from rfl, e1, ci1] at h1
    exact add_limbs (X 2 (by decide)) (wB1_lt hL hr) (X 4 (by decide))
      (hC 2 0 (by decide) (by decide)) (hC 2 1 (by decide) (by decide)) (by omega) (by omega)
  · have h0 := z 10 (by decide); have h1 := z 11 (by decide)
    rw [show (10 : Nat) = 2 * 5 + 0 from rfl, f0, ci0] at h0
    rw [show (11 : Nat) = 2 * 5 + 1 from rfl, f1, ci1] at h1
    exact add_limbs (X 3 (by decide)) (wD2_lt hL hr) (X 5 (by decide))
      (hC 3 0 (by decide) (by decide)) (hC 3 1 (by decide) (by decide)) (by omega) (by omega)

/-! ## The next state -/

theorem gCopy_Q {p : Nat} (hp : p < 8) (hP : nv tr t r (colP p) = 1) :
    zev (tenv tr t r pub) gCopy = 0 := by
  have hu := fun y (hy : y ∈ flagCols) (hne : y ≠ colP p) =>
    flag_unique hL (hr0' hL hr) (mem_flag_P hp) hy hne hP
  have e1 := hu colI0 mem_flag_I0 (by unfold colI0 colP; omega)
  have e2 := hu colI1 mem_flag_I1 (by unfold colI1 colP; omega)
  have e3 := hu (colF 0) (mem_flag_F (by decide)) (by unfold colF colP; omega)
  have e4 := hu (colF 1) (mem_flag_F (by decide)) (by unfold colF colP; omega)
  have e5 := hu (colF 2) (mem_flag_F (by decide)) (by unfold colF colP; omega)
  simp [gCopy, zev_sum, cur_eq, e1, e2, e3, e4, e5]

theorem copy_zero {p : Nat} (hp : p < 8) (hP : nv tr t r (colP p) = 1) {i l : Nat} (hi : i < 16)
    (hl : l < 2) (hb : ∀ v : Int, zev (tenv tr t r pub) (newS (grp p) i l) = v → 0 ≤ v ∧ v < 65536) :
    (nv tr t (r + 1) (colS i l) : Int) = zev (tenv tr t r pub) (newS (grp p) i l) := by
  have hz := zc hL (hr0' hL hr) (mem_cCopy (List.mem_append_left _
    (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩⟩)))
  simp only [zev_add, zev_mul, gCopy_Q hL hr hp hP, Int.zero_mul, Int.zero_add,
    zev_selP hL hr hp hP, zev_sub, sN, zev_n, nxt_eq hr] at hz
  have := hb _ rfl
  have := nv_lt (tr := tr) (t := t) (r + 1) (colS i l)
  omega

/-- **One quarter-round row.** -/
theorem qr_row {p : Nat} (hp : p < 8) (hP : nv tr t r (colP p) = 1) (hR : Ranged tr t r) :
    Ranged tr t (r + 1) ∧ ∀ i, i < 16 → sw tr t (r + 1) i = (qrStep p (stA tr t r))[i]! := by
  obtain ⟨wb, wd, w2, w3, w4, w5⟩ := qr_words hL hr (pub := pub) hp hP hR
  have hf := grp_facts hp
  obtain ⟨ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩ := hf
  have hX := fun m (hm : m < 6) l (hl : l < 2) => zev_limb (bitsX hL (hr0' hL hr) hm (pub := pub)) hl
  -- the new limb of slot `i`
  have hn : ∀ i l, i < 16 → l < 2 → (nv tr t (r + 1) (colS i l) : Int) =
      if i = (grp p).1 then Lm (xw tr t r 4) l else if i = (grp p).2.1 then Lm (wB2 tr t r) l
      else if i = (grp p).2.2.1 then Lm (xw tr t r 5) l else if i = (grp p).2.2.2 then Lm (wD2 tr t r) l
      else (nv tr t r (colS i l) : Int) := by
    intro i l hi hl
    have e : zev (tenv tr t r pub) (newS (grp p) i l) =
        if i = (grp p).1 then Lm (xw tr t r 4) l else if i = (grp p).2.1 then Lm (wB2 tr t r) l
        else if i = (grp p).2.2.1 then Lm (xw tr t r 5) l else if i = (grp p).2.2.2 then Lm (wD2 tr t r) l
        else (nv tr t r (colS i l) : Int) := by
      unfold newS
      by_cases e1 : i = (grp p).1
      · rw [if_pos e1, if_pos e1]; exact hX 4 (by decide) l hl
      rw [if_neg e1, if_neg e1]
      by_cases e2 : i = (grp p).2.1
      · rw [if_pos e2, if_pos e2]; exact zev_limb (bitsB2 hL hr) hl
      rw [if_neg e2, if_neg e2]
      by_cases e3 : i = (grp p).2.2.1
      · rw [if_pos e3, if_pos e3]; exact hX 5 (by decide) l hl
      rw [if_neg e3, if_neg e3]
      by_cases e4 : i = (grp p).2.2.2
      · rw [if_pos e4, if_pos e4]; exact zev_limb (bitsD2 hL hr) hl
      rw [if_neg e4, if_neg e4]; rfl
    rw [copy_zero hL hr hp hP hi hl, e]
    intro v hv
    rw [e] at hv; subst hv
    have := hR i hi l hl
    have l4 := Lm_lt (xw tr t r 4) l; have l5 := Lm_lt (xw tr t r 5) l
    have l6 := Lm_lt (wB2 tr t r) l; have l7 := Lm_lt (wD2 tr t r) l
    split <;> (try split) <;> (try split) <;> (try split) <;> omega
  have hR' : Ranged tr t (r + 1) := by
    intro i hi l hl
    have hh := hn i l hi hl
    have l4 := Lm_lt (xw tr t r 4) l; have l5 := Lm_lt (xw tr t r 5) l
    have l6 := Lm_lt (wB2 tr t r) l; have l7 := Lm_lt (wD2 tr t r) l
    have := hR i hi l hl
    split at hh <;> (try split at hh) <;> (try split at hh) <;> (try split at hh) <;> omega
  refine ⟨hR', fun i hi => ?_⟩
  have h16 : (stA tr t r).size = 16 := stA_size r
  unfold qrStep
  rw [qr_get _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) hab hac had hbc hbd hcd i]
  rw [stA_get ha, stA_get hb, stA_get hc, stA_get hd, wb, wd]
  have q : qrf (sw tr t r (grp p).1) (xw tr t r 0) (sw tr t r (grp p).2.2.1) (xw tr t r 1) =
      (xw tr t r 4, wB2 tr t r, xw tr t r 5, wD2 tr t r) := by
    unfold qrf
    simp only [← w2]
    rw [show rotl32 (xw tr t r 1 ^^^ xw tr t r 2) 16 = wD1 tr t r from rfl, ← w3,
      show rotl32 (xw tr t r 0 ^^^ xw tr t r 3) 12 = wB1 tr t r from rfl, ← w4,
      show rotl32 (wD1 tr t r ^^^ xw tr t r 4) 8 = wD2 tr t r from rfl, ← w5]
    rfl
  rw [q]
  have h0 := hn i 0 hi (by decide); have h1 := hn i 1 hi (by decide)
  have W4 := word_limbs (xw_lt hL (hr0' hL hr) (m := 4) (by decide))
  have W5 := word_limbs (xw_lt hL (hr0' hL hr) (m := 5) (by decide))
  have WB := word_limbs (wB2_lt hL hr); have WD := word_limbs (wD2_lt hL hr)
  unfold Lm at h0 h1
  unfold sw
  by_cases e1 : i = (grp p).1
  · rw [if_pos e1] at h0 h1 ⊢; dsimp only; omega
  rw [if_neg e1] at h0 h1 ⊢
  by_cases e2 : i = (grp p).2.1
  · rw [if_pos e2] at h0 h1 ⊢; dsimp only; omega
  rw [if_neg e2] at h0 h1 ⊢
  by_cases e3 : i = (grp p).2.2.1
  · rw [if_pos e3] at h0 h1 ⊢; dsimp only; omega
  rw [if_neg e3] at h0 h1 ⊢
  by_cases e4 : i = (grp p).2.2.2
  · rw [if_pos e4] at h0 h1 ⊢; dsimp only; omega
  rw [if_neg e4] at h0 h1 ⊢
  rw [stA_get hi]; unfold sw; omega

end

end ZkFormal.Chacha.Sound
