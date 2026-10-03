/-!
# ZkFormal.Sha.Stub.Fp — local stand-in for lane L1's BabyBear field

Lane L5 (SHA-256 AIR) is drafted against this stub until L1 publishes
`Fp`.  Everything downstream uses only the small interface proved at the
end of this file (`val_add`, `val_mul`, `val_neg`, `val_ofNat`, `ext`,
`mul_eq_zero`), so porting to L1's type means re-proving those lemmas.

`P = 15·2^27 + 1` (BabyBear).  Primality is checked by kernel trial division
up to `44869 = ⌊√P⌋` (`decide +kernel`, ~45k `Nat.mod` steps).
-/

namespace ZkFormal.Sha

/-- The BabyBear prime. -/
abbrev P : Nat := 2013265921

theorem P_eq : P = 15 * 2 ^ 27 + 1 := rfl

/-- Base field (stub). -/
abbrev Fp := Fin P

namespace Fp

/-- No divisor of `P` in `[d, d + n)`. -/
def noDiv : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, d => P % d != 0 && noDiv n (d + 1)

theorem noDiv_spec : ∀ n d, noDiv n d = true → ∀ x, d ≤ x → x < d + n → P % x ≠ 0 := by
  intro n
  induction n with
  | zero => intro d _ x h1 h2; omega
  | succ n ih =>
    intro d h x h1 h2
    simp only [noDiv, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    by_cases hx : x = d
    · subst hx; exact h.1
    · exact ih (d + 1) h.2 x (by omega) (by omega)

theorem trial : noDiv 44868 2 = true := by decide +kernel

/-- `P` has no nontrivial divisor. -/
theorem P_prime (a : Nat) (ha : a ∣ P) : a = 1 ∨ a = P := by
  obtain ⟨b, hb⟩ := ha
  have hP : 2013265921 = a * b := hb
  rcases Nat.lt_or_ge a 2 with h | h
  · rcases Nat.lt_or_ge a 1 with h' | h'
    · have : a = 0 := by omega
      subst this; simp at hP
    · left; omega
  rcases Nat.lt_or_ge b 2 with hb2 | hb2
  · rcases Nat.lt_or_ge b 1 with h' | h'
    · have : b = 0 := by omega
      subst this; simp at hP
    · right; have : b = 1 := by omega
      subst this; omega
  exfalso
  -- the smaller factor is ≤ 44869
  have hsmall : a ≤ 44869 ∨ b ≤ 44869 := by
    rcases Nat.lt_or_ge a 44870 with h1 | h1
    · left; omega
    rcases Nat.lt_or_ge b 44870 with h2 | h2
    · right; omega
    have : 44870 * 44870 ≤ a * b := Nat.mul_le_mul h1 h2
    omega
  rcases hsmall with hs | hs
  · exact noDiv_spec _ _ trial a h (by omega) (by show 2013265921 % a = 0; rw [hP]; exact Nat.mul_mod_right a b)
  · exact noDiv_spec _ _ trial b hb2 (by omega) (by show 2013265921 % b = 0; rw [hP, Nat.mul_comm]; exact Nat.mul_mod_right b a)

theorem coprime_of_lt (x : Nat) (h0 : 0 < x) (h1 : x < P) : Nat.Coprime P x := by
  unfold Nat.Coprime
  rcases P_prime _ (Nat.gcd_dvd_left P x) with h | h
  · exact h
  · exfalso
    have : P ∣ x := h ▸ Nat.gcd_dvd_right P x
    have := Nat.le_of_dvd h0 this
    omega

theorem dvd_mul (x y : Nat) (hx : x < P) (hy : y < P) (h : P ∣ x * y) : x = 0 ∨ y = 0 := by
  rcases Nat.eq_zero_or_pos x with h0 | h0
  · exact Or.inl h0
  · right
    have hc := coprime_of_lt x h0 hx
    have : P ∣ y := hc.dvd_of_dvd_mul_left h
    rcases Nat.eq_zero_or_pos y with h0' | h0'
    · exact h0'
    · have := Nat.le_of_dvd h0' this; omega

/-! ## The interface used by the SHA AIR proofs -/

theorem ext {a b : Fp} (h : a.val = b.val) : a = b := Fin.ext h

theorem val_lt (a : Fp) : a.val < P := a.isLt

theorem val_add (a b : Fp) : (a + b).val = (a.val + b.val) % P := Fin.val_add a b

theorem val_mul (a b : Fp) : (a * b).val = (a.val * b.val) % P := Fin.val_mul a b

theorem val_neg (a : Fp) : (-a).val = (P - a.val) % P := by
  exact Fin.val_neg' a

/-- Embedding of naturals. -/
def ofNat (n : Nat) : Fp := ⟨n % P, Nat.mod_lt _ (by decide)⟩

theorem val_ofNat (n : Nat) : (ofNat n).val = n % P := rfl

theorem val_zero : (0 : Fp).val = 0 := rfl
theorem val_one : (1 : Fp).val = 1 := rfl

theorem mul_eq_zero {a b : Fp} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  have h' : (a.val * b.val) % P = 0 := by rw [← val_mul, h]; rfl
  rcases dvd_mul a.val b.val a.isLt b.isLt (Nat.dvd_of_mod_eq_zero h') with h1 | h1
  · left; exact ext (by rw [h1]; rfl)
  · right; exact ext (by rw [h1]; rfl)

end Fp
end ZkFormal.Sha
