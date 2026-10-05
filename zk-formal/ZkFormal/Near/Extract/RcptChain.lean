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

namespace ZkFormal.Near.RcptProof

theorem sumL_add (f g : Nat → Nat) (L : Nat) : sumL (fun k => f k + g k) L = sumL f L + sumL g L := by
  induction L with
  | zero => rfl
  | succ L ih => simp only [sumL]; rw [ih, Nat.mul_add]; omega

end ZkFormal.Near.RcptProof

namespace ZkFormal.Near.RcptProof

def convS (f : Nat → Nat) (k : Nat) : Nat :=
  232 * (if 2 ≤ k then f (k - 2) else 0) + 137 * (if 3 ≤ k then f (k - 3) else 0) +
  4 * (if 4 ≤ k then f (k - 4) else 0) + 35 * (if 5 ≤ k then f (k - 5) else 0) +
  199 * (if 6 ≤ k then f (k - 6) else 0) + 138 * (if 7 ≤ k then f (k - 7) else 0)
def convR (f : Nat → Nat) : Nat := 232 * f 14 + 59392 * f 15 + 137 * f 13 + 35072 * f 14 + 8978432 * f 15 + 4 * f 12 + 1024 * f 13 + 262144 * f 14 + 67108864 * f 15 + 35 * f 11 + 8960 * f 12 + 2293760 * f 13 + 587202560 * f 14 + 150323855360 * f 15 + 199 * f 10 + 50944 * f 11 + 13041664 * f 12 + 3338665984 * f 13 + 854698491904 * f 14 + 218802813927424 * f 15 + 138 * f 9 + 35328 * f 10 + 9043968 * f 11 + 2315255808 * f 12 + 592705486848 * f 13 + 151732604633088 * f 14 + 38843546786070528 * f 15
theorem convS_id (f : Nat → Nat) :
    NearSpec.Params.storageAmountPerByte * sumL f 16 = sumL (convS f) 16 + NearSpec.Params.two128 * convR f := by
  simp only [sumL, convS, convR, NearSpec.Params.storageAmountPerByte, NearSpec.Params.two128]
  simp (config := {decide := true}) only [ite_true, ite_false, Nat.reduceSub, Nat.reducePow]
  omega

end ZkFormal.Near.RcptProof

namespace ZkFormal.Near.RcptProof

/-- Carry chain with an arbitrary carry-in. -/
theorem chainC (L : Nat) (hL : 0 < L) (s a cin cout : Nat → Nat)
    (hrow : ∀ k, k < L → s k + 256 * cout k = a k + cin k)
    (hlink : ∀ k, k + 1 < L → cin (k + 1) = cout k) :
    sumL s L + 256 ^ L * cout (L - 1) = sumL a L + cin 0 := by
  have := chain L hL s (fun k => a k + if k = 0 then cin 0 else 0) (fun k => if k = 0 then 0 else cin k) cout
    (fun k hk => by
      have := hrow k hk
      by_cases h0 : k = 0
      · subst h0; simp; omega
      · simp [h0]; omega) (by simp) (fun k hk => by simp [hlink k hk])
  rw [this]
  have gen : ∀ M, 0 < M → sumL (fun k => a k + if k = 0 then cin 0 else 0) M = sumL a M + cin 0 := by
    intro M hM
    induction M with
    | zero => omega
    | succ M ih =>
      rcases Nat.eq_zero_or_pos M with h0 | h0
      · subst h0; simp [sumL]
      · simp only [sumL]; rw [ih h0, if_neg (by omega), Nat.add_zero]; omega
  exact gen L hL

end ZkFormal.Near.RcptProof
