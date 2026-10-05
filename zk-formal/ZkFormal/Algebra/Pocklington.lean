import ZkFormal.Algebra.NatPrime
import ZkFormal.Algebra.Transport

/-!
# ZkFormal.Algebra.Pocklington — cheap primality certificates for `n = 2^k·m + 1`

`isPrime_of_pocklington2`: if `n − 1 = 2^k·m`, `n < (2^k + 1)^2` and some `a`
has `a^(2^(k−1)·m) ≡ −1 (mod n)`, then `n` is prime.  (Pocklington's
criterion with the fully factored part `F = 2^k ≥ √n`; the only prime of `F`
is `2`, so the Pratt-style certificate is a single modular power.)

Proof: for a prime `r ∣ n`, `b = a^m` has `b^(2^(k−1)) ≡ −1 (mod r)`, so its
order mod `r` is exactly `2^k`; Fermat gives `b^(r−1) ≡ 1`, hence
`2^k ∣ r − 1` and `r > √n`.  A composite `n` has a prime factor `≤ √n`.

The kernel check is `powMod a e n = n − 1` by square-and-multiply on `Nat`
(31 squarings for BabyBear), replacing trial division (too slow for some
rechecker kernels).
-/

namespace ZkFormal.Algebra

open Lean.Grind

/-- Square-and-multiply modular exponentiation; `powModAux fuel n b acc e =
acc · b^e mod n` when `e ≤ fuel` (`powModAux_eq`). -/
def powModAux (n : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, acc, _ => acc % n
  | fuel + 1, b, acc, e =>
    if e = 0 then acc % n
    else powModAux n fuel (b * b % n) (if e % 2 = 1 then acc * b % n else acc) (e / 2)

/-- `b^e mod n` (fuel 64: exponents below `2^64`). -/
def powMod (b e n : Nat) : Nat := powModAux n 64 (b % n) 1 e

theorem powModAux_eq (n : Nat) : ∀ fuel b acc e, e < 2 ^ fuel →
    powModAux n fuel b acc e = acc * b ^ e % n
  | 0, b, acc, e, h => by
    have : e = 0 := by simp at h; omega
    subst this; simp [powModAux]
  | fuel + 1, b, acc, e, h => by
    simp only [powModAux]
    split
    · next he => subst he; simp
    · rw [powModAux_eq n fuel _ _ _ (by rw [Nat.pow_succ] at h; omega)]
      have hsplit : b ^ e = (b * b) ^ (e / 2) * b ^ (e % 2) := by
        conv => lhs; rw [show e = 2 * (e / 2) + e % 2 by omega]
        rw [Nat.pow_add, Nat.pow_mul, Nat.pow_two]
      rw [hsplit]
      split
      · next h1 =>
        rw [h1, Nat.pow_one, Nat.mul_mod, Nat.mod_mod, ← Nat.pow_mod, ← Nat.mul_mod]
        congr 1; ac_rfl
      · next h1 =>
        rw [show e % 2 = 0 by omega, Nat.pow_zero, Nat.mul_one, Nat.mul_mod, ← Nat.pow_mod,
          ← Nat.mul_mod]

theorem powMod_eq {b e n : Nat} (he : e < 2 ^ 64) : powMod b e n = b ^ e % n := by
  rw [powMod, powModAux_eq n 64 _ _ _ he, Nat.one_mul, ← Nat.pow_mod]

/-- Every `d ≥ 2` has a prime divisor. -/
theorem exists_prime_dvd : ∀ d : Nat, 2 ≤ d → ∃ r, IsPrime r ∧ r ∣ d
  | d, hd => by
    by_cases hp : IsPrime d
    · exact ⟨d, hp, Nat.dvd_refl d⟩
    · have : ∃ e, e ∣ d ∧ e ≠ 1 ∧ e ≠ d := by
        refine Classical.byContradiction fun hne => hp ⟨hd, fun e he => ?_⟩
        refine Classical.byContradiction fun h => hne ⟨e, he, ?_⟩
        exact ⟨fun h1 => h (Or.inl h1), fun h2 => h (Or.inr h2)⟩
      obtain ⟨e, he, he1, hed⟩ := this
      have hepos : 0 < e := Nat.pos_of_dvd_of_pos he (by omega)
      have hle : e ≤ d := Nat.le_of_dvd (by omega) he
      have : e < d := by omega
      obtain ⟨r, hr, hre⟩ := exists_prime_dvd e (by omega)
      exact ⟨r, hr, Nat.dvd_trans hre he⟩

theorem fin_one_val {r : Nat} [NeZero r] : (1 : Fin r).val = 1 % r := rfl

theorem fin_pow_val {r : Nat} [NeZero r] (x : Fin r) : ∀ e : Nat, (x ^ e).val = x.val ^ e % r
  | 0 => by
    exact fin_one_val
  | e + 1 => by
    rw [Semiring.pow_succ, Fin.val_mul, fin_pow_val x e, Nat.pow_succ, Nat.mod_mul_mod]

theorem fin_ofNat_val {r : Nat} [NeZero r] (x : Nat) : (Fin.ofNat r x).val = x % r := rfl

/-- **Pocklington's criterion for `n = 2^k·m + 1`.** -/
theorem isPrime_of_pocklington2 {n k m a : Nat} (hk : 1 ≤ k) (hn : n - 1 = 2 ^ k * m)
    (hn3 : 3 ≤ n) (hsq : n < (2 ^ k + 1) * (2 ^ k + 1))
    (ha : a ^ (2 ^ (k - 1) * m) % n = n - 1) : IsPrime n := by
  -- every prime factor `r` of `n` satisfies `2^k + 1 ≤ r`
  have big : ∀ r, IsPrime r → r ∣ n → 2 ^ k + 1 ≤ r := by
    intro r hr hrn
    have hr2 := hr.two_le
    obtain ⟨c, hc⟩ := hrn
    -- `b^(2^(k-1)) ≡ -1 (mod r)`
    have hmodr : a ^ (2 ^ (k - 1) * m) % r = r - 1 := by
      have h1 : a ^ (2 ^ (k - 1) * m) % r = (n - 1) % r := by
        rw [← ha, hc, Nat.mod_mul_right_mod]
      rw [h1]
      have : n - 1 = r * (c - 1) + (r - 1) := by
        have hc1 : 1 ≤ c := by
          rcases c with _ | c
          · simp at hc; omega
          · omega
        rw [hc, Nat.mul_sub, Nat.mul_one]
        have : r ≤ r * c := Nat.le_mul_of_pos_right r (by omega)
        omega
      rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    have hr3 : 3 ≤ r := by
      -- `n` is odd, so `r ≠ 2`
      refine Classical.byContradiction fun h => ?_
      have : r = 2 := by omega
      subst this
      have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        simp [Nat.pow_succ, Nat.mul_comm]
      rw [h2k, Nat.mul_assoc] at hn
      omega
    haveI : NeZero r := ⟨by omega⟩
    let B : Fin r := Fin.ofNat r (a ^ m)
    have hB : B ^ (2 ^ (k - 1)) = -1 := by
      apply Fin.ext
      rw [fin_pow_val, fin_ofNat_val, ← Nat.pow_mod, ← Nat.pow_mul, Nat.mul_comm, hmodr]
      show r - 1 = ((-1 : Fin r)).val
      simp [Fin.neg_def, fin_one_val, Nat.mod_eq_of_lt (show 1 < r by omega)]
    have hne : (-1 : Fin r) ≠ 1 := by
      intro h
      have := congrArg Fin.val h
      simp [Fin.neg_def, fin_one_val, Nat.mod_eq_of_lt (show 1 < r by omega)] at this
      omega
    -- `r ∤ a^m`
    have hnd : (a ^ m) % r ≠ 0 := by
      intro h0
      have : a ^ (2 ^ (k - 1) * m) % r = 0 := by
        rw [Nat.mul_comm, Nat.pow_mul, Nat.pow_mod, h0, Nat.zero_pow (Nat.pow_pos (by decide))]
        simp
      omega
    -- Fermat
    have hF : B ^ (r - 1) = 1 := by
      apply Fin.ext
      rw [fin_pow_val, fin_ofNat_val, ← Nat.pow_mod, fermat hr hnd]
      simp [fin_one_val, Nat.mod_eq_of_lt (show 1 < r by omega)]
    have hfull : B ^ (2 ^ k) = 1 := by
      rw [show 2 ^ k = 2 ^ (k - 1) * 2 by rw [← Nat.pow_succ]; congr 1; omega, pow_mul_eq, hB]
      show (-1 : Fin r) ^ 2 = 1
      rw [Semiring.pow_two]; grind
    -- `2^k ∣ r − 1`
    have hs : (r - 1) % 2 ^ k = 0 := by
      refine Classical.byContradiction fun hs => ?_
      have hpos : 0 < 2 ^ k := Nat.pow_pos (by decide)
      apply pow_ne_one_of_half hne B k hB ((r - 1) % 2 ^ k) (by omega) (Nat.mod_lt _ hpos)
      have e : r - 1 = 2 ^ k * ((r - 1) / 2 ^ k) + (r - 1) % 2 ^ k := (Nat.div_add_mod _ _).symm
      have := hF
      rw [e, Semiring.pow_add, pow_mul_eq, hfull, Semiring.one_pow, Semiring.one_mul] at this
      exact this
    have hpos : 0 < (r - 1) / 2 ^ k := by
      refine Nat.div_pos ?_ (Nat.pow_pos (by decide))
      exact Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero hs)
    have := Nat.div_add_mod (r - 1) (2 ^ k)
    rw [hs, Nat.add_zero] at this
    have : 2 ^ k * 1 ≤ 2 ^ k * ((r - 1) / 2 ^ k) := Nat.mul_le_mul_left _ hpos
    omega
  refine ⟨by omega, fun d hd => ?_⟩
  refine Classical.byContradiction fun hne => ?_
  have hne' : d ≠ 1 ∧ d ≠ n := ⟨fun h => hne (Or.inl h), fun h => hne (Or.inr h)⟩
  obtain ⟨e, he⟩ := hd
  have hdpos : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at he; omega)
  have hepos : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; simp at he; omega)
  have he1 : e ≠ 1 := by rintro rfl; simp at he; exact hne'.2 he.symm
  -- the smaller of `d, e` is at least 2 and its square is at most `n`
  have key : ∀ x y, n = x * y → 2 ≤ x → 2 ≤ y → x ≤ y → False := by
    intro x y hxy hx hy hle
    obtain ⟨r, hr, hrx⟩ := exists_prime_dvd x hx
    have hrn : r ∣ n := hxy ▸ Nat.dvd_mul_right_of_dvd hrx y
    have h1 := big r hr hrn
    have hrle : r ≤ x := Nat.le_of_dvd (by omega) hrx
    have : (2 ^ k + 1) * (2 ^ k + 1) ≤ x * y :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  rcases Nat.le_total d e with h | h
  · exact key d e he (by omega) (by omega) h
  · exact key e d (by rw [he, Nat.mul_comm]) (by omega) (by omega) h

end ZkFormal.Algebra
