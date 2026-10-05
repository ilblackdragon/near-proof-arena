import ZkFormal.Bcs.Statements

/-!
# ZkFormal.Bcs.Budget — the profile arithmetic (`BudgetStmt`)

`bcsNum = A·N + G·Q` with `N = 2^64 + 2^40·NPu + NVu ≤ 2^71`,
`Q = 2^64 + 2^40·NPq + NVq` and `A = R^(K-2)·(R·(B+1024) + 2N) ≤ R^(K-1)·2^51`
(`R = roRange = 2^256`).  Hence `A·N·2^128 ≤ R^(K-1)·2^250 ≤ R^K / 2`, and the
hypothesis gives `G·Q·2^128 ≤ R^K / 2`.  `K` stays symbolic throughout.
-/

namespace ZkFormal.Bcs

open ArenaCore ArenaCore.Security

/-- `bcsNum` regrouped as `A·N + G·Q`. -/
theorem bcsNum_regroup (a g qH qP NPu NVu NPq NVq : Nat) :
    qH * (a + g) + qP * (a * NPu + g * NPq) + (a * NVu + g * NVq) =
      a * (qH + qP * NPu + NVu) + g * (qH + qP * NPq + NVq) := by
  simp only [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
  omega

theorem roRange_eq_two_pow : roRange = 2 ^ 256 := by
  rw [roRange_eq, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]

/-- The per-round `A` factor: `R·(B+1024) + 2N ≤ R·2^51`. -/
theorem budget_a_le (R B N : Nat) (hR : 2 ^ 72 ≤ R) (hB : B ≤ 2 ^ 50) (hN : N ≤ 2 ^ 71) :
    R * (B + 1024) + 2 * N ≤ R * 2 ^ 51 := by
  have h1 : R * (B + 1024) ≤ R * (2 ^ 50 + 1024) := Nat.mul_le_mul_left _ (by omega)
  have h2 : R * 2 ^ 51 = R * (2 ^ 50 + 1024) + R * (2 ^ 50 - 1024) := by
    rw [← Nat.mul_add]
  have h3 : R ≤ R * (2 ^ 50 - 1024) := Nat.le_mul_of_pos_right _ (by omega)
  have h4 : 2 * N ≤ 2 * 2 ^ 71 := Nat.mul_le_mul_left _ hN
  have e : (2 : Nat) * 2 ^ 71 = 2 ^ 72 := by rw [Nat.mul_comm, ← Nat.pow_succ]
  rw [e] at h4
  rw [h2]
  exact Nat.add_le_add h1 (Nat.le_trans h4 (Nat.le_trans hR h3))

theorem half_add_le {a d c : Nat} (h1 : a * 2 ≤ c) (h2 : d * 2 ≤ c) : a + d ≤ c := by
  omega

theorem budget : BudgetStmt := by
  intro K B G NPu NVu NPq NVq hK hB hPu hVu hG
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 2 := ⟨K - 2, by omega⟩
  have hR72 : 2 ^ 72 ≤ roRange := by
    rw [roRange_eq_two_pow]; exact Nat.pow_le_pow_right (by decide) (by decide)
  have hR251 : 2 ^ 251 ≤ roRange := by
    rw [roRange_eq_two_pow]; exact Nat.pow_le_pow_right (by decide) (by decide)
  simp only [bcsNum]
  rw [show K' + 2 - 1 = K' + 1 by omega, show K' + 2 - 2 = K' by omega, bcsNum_regroup]
  generalize roRange = R at hR72 hR251 hG ⊢
  have hNle : 2 ^ 64 + 2 ^ 40 * NPu + NVu ≤ 2 ^ 71 := by
    have : 2 ^ 40 * NPu ≤ 2 ^ 40 * 2 ^ 30 := Nat.mul_le_mul_left _ hPu
    have e : (2 : Nat) ^ 40 * 2 ^ 30 = 2 ^ 70 := by rw [← Nat.pow_add]
    have : (2 : Nat) ^ 64 + 2 ^ 70 + 2 ^ 30 ≤ 2 ^ 71 := by decide
    omega
  generalize 2 ^ 64 + 2 ^ 40 * NPu + NVu = N at hNle ⊢
  generalize 2 ^ 64 + 2 ^ 40 * NPq + NVq = Q at hG ⊢
  have hRK : R ^ (K' + 2) = R ^ K' * R * R := by rw [Nat.pow_succ, Nat.pow_succ]
  rw [hRK] at hG ⊢
  have hA : R ^ (K' + 1) * (B + 1024) + R ^ K' * (2 * N) =
      R ^ K' * (R * (B + 1024) + 2 * N) := by
    rw [Nat.pow_succ, Nat.mul_assoc, ← Nat.mul_add]
  rw [hA]
  have ha := budget_a_le R B N hR72 hB hNle
  have h1 : R ^ K' * (R * (B + 1024) + 2 * N) * N * 2 ^ 128 ≤
      R ^ K' * (R * 2 ^ 51) * 2 ^ 71 * 2 ^ 128 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ ha) hNle)
  have e1 : R ^ K' * (R * 2 ^ 51) * 2 ^ 71 * 2 ^ 128 * 2 = R ^ K' * R * 2 ^ 251 := by
    have e : (2 : Nat) ^ 51 * (2 ^ 71 * (2 ^ 128 * 2)) = 2 ^ 251 := by
        rw [← Nat.pow_succ, ← Nat.pow_add, ← Nat.pow_add]
    simp only [Nat.mul_assoc, e]
  have h2 : R ^ K' * R * 2 ^ 251 ≤ R ^ K' * R * R := Nat.mul_le_mul_left _ hR251
  have h3 : G * Q * 2 ^ 128 * 2 = G * Q * 2 ^ 129 := by
    rw [Nat.mul_assoc _ (2 ^ 128), ← Nat.pow_succ]
  have := Nat.mul_le_mul_right 2 h1
  rw [Nat.add_mul]
  apply half_add_le
  · exact Nat.le_trans this (by rw [e1]; exact h2)
  · rw [h3]; exact hG

/-- The profile instance `K = 24`. -/
theorem budget_K24 (B G NPu NVu NPq NVq : Nat) (hB : B ≤ 2 ^ 50) (hPu : NPu ≤ 2 ^ 30)
    (hVu : NVu ≤ 2 ^ 30) (hG : G * (2 ^ 64 + 2 ^ 40 * NPq + NVq) * 2 ^ 129 ≤ roRange ^ 24) :
    bcsNum 24 B G (2 ^ 64) (2 ^ 40) NPu NVu NPq NVq * 2 ^ 128 ≤ roRange ^ 24 :=
  budget 24 B G NPu NVu NPq NVq (by decide) hB hPu hVu hG

end ZkFormal.Bcs
