import ZkFormal.Near.Extract.Segments

/-!
# ZkFormal.Near.Extract.RcptChain — byte-serial carry chains (pure arithmetic)

`sumL f L = Σ_{k<L} 256^k · f k`; `chain`: if row `k` has
`s_k + 256·out_k = a_k + in_k`, `in_0 = 0` and `in_{k+1} = out_k`, then
`sumL s L + 256^L · out_{L−1} = sumL a L`.
-/

namespace ZkFormal.Near.RcptProof

/-- `Σ_{k<L} 256^k · f k` -/
def sumL (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | L + 1 => sumL f L + 256 ^ L * f L

theorem sumL_congr (f g : Nat → Nat) (L : Nat) (h : ∀ k, k < L → f k = g k) : sumL f L = sumL g L := by
  induction L with
  | zero => rfl
  | succ L ih => simp only [sumL]; rw [ih (fun k hk => h k (by omega)), h L (by omega)]

theorem sumL_lt (f : Nat → Nat) (L : Nat) (h : ∀ k, k < L → f k < 256) : sumL f L < 256 ^ L := by
  induction L with
  | zero => simp [sumL]
  | succ L ih =>
    have := ih (fun k hk => h k (by omega))
    have hL := h L (by omega)
    simp only [sumL, Nat.pow_succ]
    have : 256 ^ L * f L ≤ 256 ^ L * 255 := Nat.mul_le_mul_left _ (by omega)
    omega

theorem le256_map_range (f : Nat → Nat) (L : Nat) : le256 ((List.range L).map f) = sumL f L := by
  have gen : ∀ L off : Nat, le256 ((List.range' off L).map f) * 256 ^ off + sumL f off = sumL f (off + L) := by
    intro L
    induction L with
    | zero => intro off; simp [le256]
    | succ L ih =>
      intro off
      rw [List.range'_succ, List.map_cons, le256]
      have := ih (off + 1)
      rw [show off + 1 + L = off + (L + 1) by omega] at this
      rw [← this]
      simp only [sumL, Nat.pow_succ]
      rw [Nat.add_mul]
      have e : 256 * le256 (List.map f (List.range' (off + 1) L)) * 256 ^ off =
          le256 (List.map f (List.range' (off + 1) L)) * (256 ^ off * 256) := by
        rw [Nat.mul_comm 256, Nat.mul_assoc, Nat.mul_comm 256]
      rw [e, Nat.mul_comm (f off)]; omega
  have := gen L 0
  simpa [sumL, List.range_eq_range'] using this

/-- **Carry chain.** -/
theorem chain (L : Nat) (hL : 0 < L) (s a cin cout : Nat → Nat)
    (hrow : ∀ k, k < L → s k + 256 * cout k = a k + cin k) (h0 : cin 0 = 0)
    (hlink : ∀ k, k + 1 < L → cin (k + 1) = cout k) :
    sumL s L + 256 ^ L * cout (L - 1) = sumL a L := by
  have gen : ∀ M, M + 1 ≤ L → sumL s (M + 1) + 256 ^ (M + 1) * cout M = sumL a (M + 1) := by
    intro M
    induction M with
    | zero =>
      intro _
      have := hrow 0 hL; rw [h0] at this
      simp [sumL]; omega
    | succ M ih =>
      intro hM
      have i1 := ih (by omega)
      have r := hrow (M + 1) (by omega)
      rw [hlink M (by omega)] at r
      have e1 : sumL s (M + 1 + 1) = sumL s (M + 1) + 256 ^ (M + 1) * s (M + 1) := rfl
      have e2 : sumL a (M + 1 + 1) = sumL a (M + 1) + 256 ^ (M + 1) * a (M + 1) := rfl
      rw [e1, e2, ← i1, Nat.pow_succ (256) (M + 1)]
      have : 256 ^ (M + 1) * s (M + 1) + 256 ^ (M + 1) * 256 * cout (M + 1) =
          256 ^ (M + 1) * (a (M + 1) + cout M) := by
        rw [Nat.mul_assoc, ← Nat.mul_add, r]
      rw [Nat.mul_add] at this
      omega
  have := gen (L - 1) (by omega)
  rwa [show L - 1 + 1 = L by omega] at this

end ZkFormal.Near.RcptProof
