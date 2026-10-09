import ZkFormal.Chacha.Sound.Basic

/-!
# ZkFormal.Chacha.Sound.Kind — block structure

`AtPos tr t r m`: row `r` is at position `m < 86` of a block
(`0: I0`, `1: I1`, `2 + 8·dr + p: Q(p, dr)`, `82 + j: F j`).  The kind transitions
are backward-deterministic (`atPos_back`), so every `F` row ends a full block
(`atPos_walk`).
-/

namespace ZkFormal.Chacha.Sound

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table

variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

def AtPos (tr : Trace Fp) (t r m : Nat) : Prop :=
  if m = 0 then nv tr t r colI0 = 1
  else if m = 1 then nv tr t r colI1 = 1
  else if m < 82 then nv tr t r (colP ((m - 2) % 8)) = 1 ∧ drv tr t r = (m - 2) / 8
  else if m < 86 then nv tr t r (colF (m - 82)) = 1
  else False

theorem bcases {x : Nat} (h : x ≤ 1) : x = 0 ∨ x = 1 := by omega

theorem memK_P {p : Nat} (hp : p < 7) :
    E.sub (E.n (colP (p + 1))) (E.c (colP p)) ∈ cKind := by
  unfold cKind
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨p, List.mem_range.mpr hp, rfl⟩

theorem memK_F {j : Nat} (hj : j < 3) :
    E.sub (E.n (colF (j + 1))) (E.c (colF j)) ∈ cKind := by
  unfold cKind
  apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩

theorem memK_DrP {p : Nat} (hp : p < 7) :
    Expr.mul (E.n (colP (p + 1))) (E.sub drN drC) ∈ cKind := by
  unfold cKind
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨p, List.mem_range.mpr hp, rfl⟩

section
variable (hL : ChLocal tr t pub) {r : Nat} (hr : r + 1 < tr.height t)
include hL hr

theorem hr0 : r < tr.height t := by omega

theorem fl (x : Nat) (h1 : 250 ≤ x) (h2 : x < 272) : nv tr t r x ≤ 1 := bHi hL (hr0 hL hr) h1 h2
theorem fln (x : Nat) (h1 : 250 ≤ x) (h2 : x < 272) : nv tr t (r + 1) x ≤ 1 := bHi hL hr h1 h2

theorem kI1 : nv tr t (r + 1) colI1 = nv tr t r colI0 := by
  have h := zc hL (hr0 hL hr) (mem_cKind (e := E.sub (E.n colI1) (E.c colI0)) (by simp [cKind]))
  simp only [zev_sub, zev_n, zev_c, nxt_eq hr, cur_eq] at h
  have := fl hL hr colI0 (by decide) (by decide); have := fln hL hr colI1 (by decide) (by decide)
  omega

theorem kP {p : Nat} (hp : p < 7) : nv tr t (r + 1) (colP (p + 1)) = nv tr t r (colP p) := by
  have h := zc hL (hr0 hL hr)
    (mem_cKind (memK_P hp))
  simp only [zev_sub, zev_n, zev_c, nxt_eq hr, cur_eq] at h
  have := fl hL hr (colP p) (by unfold colP; omega) (by unfold colP; omega)
  have := fln hL hr (colP (p + 1)) (by unfold colP; omega) (by unfold colP; omega)
  omega

theorem kF {j : Nat} (hj : j < 3) : nv tr t (r + 1) (colF (j + 1)) = nv tr t r (colF j) := by
  have h := zc hL (hr0 hL hr)
    (mem_cKind (memK_F hj))
  simp only [zev_sub, zev_n, zev_c, nxt_eq hr, cur_eq] at h
  have := fl hL hr (colF j) (by unfold colF; omega) (by unfold colF; omega)
  have := fln hL hr (colF (j + 1)) (by unfold colF; omega) (by unfold colF; omega)
  omega

/-- `n.P0 = c.I1 + c.P7·(1 − L)`, `n.F0 = c.P7·L`, `L = Dr0·Dr3`. -/
theorem kP0F0 :
    ((nv tr t (r + 1) (colP 0) : Int) = nv tr t r colI1 + nv tr t r (colP 7) -
        nv tr t r (colP 7) * (nv tr t r (colDr 0) * nv tr t r (colDr 3))) ∧
    ((nv tr t (r + 1) (colF 0) : Int) =
        nv tr t r (colP 7) * (nv tr t r (colDr 0) * nv tr t r (colDr 3))) := by
  have h1 := zc hL (hr0 hL hr) (mem_cKind (e := E.sub (E.n (colP 0))
    (E.sub (.add (E.c colI1) (E.c (colP 7))) (.mul (E.c (colP 7)) lastDr))) (by simp [cKind]))
  have h2 := zc hL (hr0 hL hr)
    (mem_cKind (e := E.sub (E.n (colF 0)) (.mul (E.c (colP 7)) lastDr)) (by simp [cKind]))
  simp only [lastDr, zev_sub, zev_n, zev_c, zev_add, zev_mul, nxt_eq hr, cur_eq] at h1 h2
  have a1 := fl hL hr colI1 (by decide) (by decide)
  have a2 := fl hL hr (colP 7) (by decide) (by decide)
  have a3 := fl hL hr (colDr 0) (by decide) (by decide)
  have a4 := fl hL hr (colDr 3) (by decide) (by decide)
  have a5 := fln hL hr (colP 0) (by decide) (by decide)
  have a6 := fln hL hr (colF 0) (by decide) (by decide)
  generalize nv tr t r colI1 = x1 at *; generalize nv tr t r (colP 7) = x2 at *
  generalize nv tr t r (colDr 0) = x3 at *; generalize nv tr t r (colDr 3) = x4 at *
  rcases bcases a2 with rfl | rfl <;> rcases bcases a3 with rfl | rfl <;>
    rcases bcases a4 with rfl | rfl <;> (simp at h1 h2 ⊢; omega)

theorem kDr0 (h : nv tr t (r + 1) (colP 0) = 1) :
    (drv tr t (r + 1) : Int) = nv tr t r (colP 7) * (drv tr t r + 1) := by
  have h1 := zc hL (hr0 hL hr) (mem_cKind (e := .mul (E.n (colP 0))
    (E.sub drN (.mul (E.c (colP 7)) (.add drC (E.k 1))))) (by simp [cKind]))
  simp only [zev_sub, zev_n, zev_c, zev_add, zev_mul, zev_k, nxt_eq hr, cur_eq, zev_drN hr,
    zev_drC, h] at h1
  have a2 := fl hL hr (colP 7) (by decide) (by decide)
  have d1 := drv_le hL (hr0 hL hr); have d2 := drv_le hL hr
  generalize nv tr t r (colP 7) = x2 at *
  rcases bcases a2 with rfl | rfl <;> (simp at h1 ⊢; omega)

theorem kDrP {p : Nat} (hp : p < 7) (h : nv tr t (r + 1) (colP (p + 1)) = 1) :
    drv tr t (r + 1) = drv tr t r := by
  have h1 := zc hL (hr0 hL hr) (mem_cKind (memK_DrP hp))
  simp only [zev_sub, zev_n, zev_mul, nxt_eq hr, zev_drN hr, zev_drC, h] at h1
  have d1 := drv_le hL (hr0 hL hr); have d2 := drv_le hL hr
  simp at h1; omega

/-- **Backward step.** -/
theorem atPos_back {m : Nat} (h : AtPos tr t (r + 1) (m + 1)) : AtPos tr t r m := by
  unfold AtPos at h ⊢
  have hP0F0 := kP0F0 hL hr
  have a1 := fl hL hr colI1 (by decide) (by decide)
  have a2 := fl hL hr (colP 7) (by decide) (by decide)
  have a3 := fl hL hr (colDr 0) (by decide) (by decide)
  have a4 := fl hL hr (colDr 3) (by decide) (by decide)
  have hd := drv_le hL (hr0 hL hr)
  by_cases m0 : m = 0
  · subst m0; simp at h; rw [kI1 hL hr] at h; simpa using h
  by_cases m1 : m = 1
  · subst m1
    simp at h ⊢
    obtain ⟨hp, hd0⟩ := h
    have hdr := kDr0 hL hr hp
    rw [hd0] at hdr
    have e1 := hP0F0.1; rw [hp] at e1
    rcases bcases a2 with h2 | h2
    · rw [h2] at e1; simp at e1; omega
    · rw [h2] at hdr; simp at hdr; omega
  by_cases m82 : m + 1 < 82
  · -- Q row at m + 1 ≥ 2
    simp only [show m + 1 ≠ 0 by omega, show m + 1 ≠ 1 by omega, m82, ite_false, ite_true] at h
    simp only [m0, m1, show m < 82 by omega, ite_false, ite_true]
    obtain ⟨hp, hdr⟩ := h
    by_cases hp0 : (m + 1 - 2) % 8 = 0
    · -- P0 at m+1, so previous is P7 with dr - 1
      rw [hp0] at hp
      have hdr' := kDr0 hL hr hp
      have hm8 : (m + 1 - 2) / 8 ≥ 1 := by
        rcases Nat.eq_zero_or_pos ((m + 1 - 2) / 8) with h0 | h0
        · omega
        · exact h0
      -- previous row is P7 (not I1, since then dr would be 0)
      have hP7 : nv tr t r (colP 7) = 1 := by
        rcases bcases a2 with h2 | h2
        · rw [h2] at hdr'; simp at hdr'; omega
        · exact h2
      rw [hP7] at hdr'
      refine ⟨by rw [show (m - 2) % 8 = 7 by omega]; exact hP7, ?_⟩
      omega
    · have hp' : (m + 1 - 2) % 8 = (m - 2) % 8 + 1 := by omega
      rw [hp'] at hp
      have hlt : (m - 2) % 8 < 7 := by omega
      refine ⟨by rw [← kP hL hr hlt]; exact hp, ?_⟩
      rw [← kDrP hL hr hlt hp]; omega
  by_cases m86 : m + 1 < 86
  · simp only [show m + 1 ≠ 0 by omega, show m + 1 ≠ 1 by omega, m82, m86, ite_false, ite_true] at h
    by_cases hm : m + 1 = 82
    · -- F0: previous is P7 with dr = 9
      rw [hm] at h
      have h' : nv tr t (r + 1) (colF 0) = 1 := by simpa using h
      simp only [m0, m1, show m < 82 by omega, ite_false, ite_true]
      have := hP0F0.2; rw [h'] at this
      rcases bcases a2 with h2 | h2 <;> rcases bcases a3 with h3 | h3 <;>
        rcases bcases a4 with h4 | h4 <;> rw [h2, h3, h4] at this <;> simp at this
      refine ⟨by rw [show (m - 2) % 8 = 7 by omega]; exact h2, ?_⟩
      unfold drv at hd ⊢; rw [h3, h4] at hd ⊢; omega
    · simp only [m0, m1, show ¬ m < 82 by omega, show m < 86 by omega, ite_false, ite_true]
      have hj : m - 82 < 3 := by omega
      rw [← kF hL hr hj, show m - 82 + 1 = m + 1 - 82 by omega]; exact h
  · simp [m0, show m + 1 ≠ 0 by omega, show m + 1 ≠ 1 by omega, m82, m86] at h

end

/-- Row `0` is `I0` or padding. -/
theorem atPos_pos (hL : ChLocal tr t pub) {m : Nat} (hm : 1 ≤ m) (h : AtPos tr t 0 m) : False := by
  have hb : ∀ x, 250 ≤ x → x < 272 → nv tr t 0 x ≤ 1 := fun x h1 h2 => bHi hL (height_pos tr t) h1 h2
  have h0 := zc hL (height_pos tr t)
    (mem_cKind (e := .mul .isFirst (.add (E.c colI1) (.add sumP sumF))) (by simp [cKind]))
  have e : zev (tenv tr t 0 pub) (.mul .isFirst (.add (E.c colI1) (.add sumP sumF))) =
      ((nv tr t 0 251 + (nv tr t 0 252 + nv tr t 0 253 + nv tr t 0 254 + nv tr t 0 255 +
        nv tr t 0 256 + nv tr t 0 257 + nv tr t 0 258 + nv tr t 0 259) +
        (nv tr t 0 260 + nv tr t 0 261 + nv tr t 0 262 + nv tr t 0 263) : Nat) : Int) := by
    simp [zev_sum, sumP, sumF, List.range_succ, tenv, colI1, colP, colF, nv]
    omega
  rw [e] at h0
  have := hb 251 (by decide) (by decide)
  have := hb 252 (by decide) (by decide); have := hb 253 (by decide) (by decide)
  have := hb 254 (by decide) (by decide); have := hb 255 (by decide) (by decide)
  have := hb 256 (by decide) (by decide); have := hb 257 (by decide) (by decide)
  have := hb 258 (by decide) (by decide); have := hb 259 (by decide) (by decide)
  have := hb 260 (by decide) (by decide); have := hb 261 (by decide) (by decide)
  have := hb 262 (by decide) (by decide); have := hb 263 (by decide) (by decide)
  have hs := h0 (by omega) (by omega)
  unfold AtPos at h
  simp only [show m ≠ 0 by omega, ite_false] at h
  unfold colI1 colP colF at h
  split at h
  · omega
  split at h
  · have h1 := h.1
    have : (m - 2) % 8 < 8 := Nat.mod_lt _ (by decide)
    generalize (m - 2) % 8 = p at *
    rcases (show p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at h1 <;> omega
  split at h
  · have : m - 82 < 4 := by omega
    generalize m - 82 = j at *
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp at h <;> omega
  · exact h

/-- **Walk back** from a row at position `m` to the block's `I0` row. -/
theorem atPos_walk (hL : ChLocal tr t pub) : ∀ (m r : Nat), r < tr.height t → AtPos tr t r m →
    m ≤ r ∧ ∀ m', m' ≤ m → AtPos tr t (r - m + m') m'
  | 0, r, _, h => ⟨Nat.zero_le _, fun m' hm' => by
      rw [show m' = 0 by omega, show r - 0 + 0 = r by omega]; exact h⟩
  | m + 1, r, hr, h => by
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · subst h0; exact absurd h (fun h => atPos_pos hL (by omega) h)
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have hb := atPos_back hL hr h
    obtain ⟨hle, hall⟩ := atPos_walk hL m r' (by omega) hb
    refine ⟨by omega, fun m' hm' => ?_⟩
    rcases Nat.lt_or_ge m' (m + 1) with hlt | hge
    · have := hall m' (by omega); rwa [show r' + 1 - (m + 1) + m' = r' - m + m' by omega]
    · rw [show m' = m + 1 by omega, show r' + 1 - (m + 1) + (m + 1) = r' + 1 by omega]; exact h

end ZkFormal.Chacha.Sound
