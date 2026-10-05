import ZkFormal.Udr.Np.Stage

/-!
# ZkFormal.Udr.Np.Domain — the FRI domains of np-udr-stark as a `Fri.Setup`

* bit reversal: `bitrev (n+1) x = (x % 2)·2^n + bitrev n (x / 2)`, bounds, injectivity;
* domain points `pt n0 m p` (bit-reversed position `p` of the size-`2^m` LDE
  domain): squaring halves the domain (`pt m (2q)² = pt (m-1) q`), sibling
  positions are negatives (`pt m (2q+1) = - pt m (2q)`), distinct, nonzero;
* the natural-to-verifier maps `permK` are injective into the right range;
* `mkSetup`: the `Fri.Setup Fp8` with the fields of `setupData`.
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

/-! ## Bit reversal -/

theorem bitrev_go (n : Nat) : ∀ x acc, bitrev.go n x acc = acc * 2 ^ n + bitrev.go n x 0 := by
  induction n with
  | zero => intro x acc; simp [bitrev.go]
  | succ k ih =>
    intro x acc
    simp only [bitrev.go]
    rw [ih (x / 2) (2 * acc + x % 2), ih (x / 2) (2 * 0 + x % 2), Nat.pow_succ]
    grind

theorem bitrev_succ (n x : Nat) : bitrev (n + 1) x = (x % 2) * 2 ^ n + bitrev n (x / 2) := by
  simp only [bitrev, bitrev.go]
  rw [bitrev_go n (x / 2) (2 * 0 + x % 2)]
  simp

theorem bitrev_lt : ∀ n x, bitrev n x < 2 ^ n
  | 0, _ => by simp [bitrev, bitrev.go]
  | n + 1, x => by
    rw [bitrev_succ, Nat.pow_succ]
    have := bitrev_lt n (x / 2)
    have : x % 2 ≤ 1 := by omega
    have : x % 2 * 2 ^ n ≤ 2 ^ n := by
      calc x % 2 * 2 ^ n ≤ 1 * 2 ^ n := Nat.mul_le_mul_right _ this
        _ = 2 ^ n := Nat.one_mul _
    omega

theorem bitrev_inj : ∀ n x y, x < 2 ^ n → y < 2 ^ n → bitrev n x = bitrev n y → x = y
  | 0, x, y, hx, hy, _ => by simp at hx hy; omega
  | n + 1, x, y, hx, hy, h => by
    rw [bitrev_succ, bitrev_succ] at h
    have b1 := bitrev_lt n (x / 2)
    have b2 := bitrev_lt n (y / 2)
    have hp : 0 < 2 ^ n := Nat.pow_pos (by omega)
    have hm : x % 2 = y % 2 := by
      rcases Nat.mod_two_eq_zero_or_one x with h1 | h1 <;>
      rcases Nat.mod_two_eq_zero_or_one y with h2 | h2 <;> rw [h1, h2] at h ⊢ <;> omega
    rw [hm] at h
    have hq := bitrev_inj n (x / 2) (y / 2) (by rw [Nat.pow_succ] at hx; omega)
      (by rw [Nat.pow_succ] at hy; omega) (by omega)
    omega

theorem bitrev_two_mul (n q : Nat) : bitrev (n + 1) (2 * q) = bitrev n q := by
  rw [bitrev_succ]; simp [Nat.mul_mod_right, Nat.mul_div_cancel_left q (by omega : 0 < 2)]

theorem bitrev_two_mul_add_one (n q : Nat) :
    bitrev (n + 1) (2 * q + 1) = 2 ^ n + bitrev n q := by
  rw [bitrev_succ]
  rw [show (2 * q + 1) % 2 = 1 by omega, show (2 * q + 1) / 2 = q by omega, Nat.one_mul]

/-! ## Domain points -/

theorem pt_eq (n0 m p : Nat) :
    pt n0 m p = Fp8.ofBase ((31 : Fp) ^ (2 ^ (n0 - m)) * Fp.twoAdicGen m ^ bitrev m p) := rfl

theorem fp31_ne_zero : (31 : Fp) ≠ 0 := by decide +kernel

theorem fp_mul_ne_zero {a b : Fp} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro h
  apply hb
  have i1 := Field.inv_mul_cancel ha
  calc b = a⁻¹ * (a * b) := by rw [← Semiring.mul_assoc, i1, Semiring.one_mul]
    _ = 0 := by rw [h, Semiring.mul_zero]

theorem fp_pow_ne_zero {a : Fp} (ha : a ≠ 0) : ∀ n : Nat, a ^ n ≠ 0
  | 0 => by rw [Semiring.pow_zero]; decide +kernel
  | n + 1 => by
    rw [Semiring.pow_succ]
    exact fp_mul_ne_zero (fp_pow_ne_zero ha n) ha

theorem twoAdicGen_sq {m : Nat} (hm : m + 1 ≤ 27) :
    Fp.twoAdicGen (m + 1) * Fp.twoAdicGen (m + 1) = Fp.twoAdicGen m := by
  simp only [Fp.twoAdicGen]
  rw [← Semiring.pow_add, show 2 ^ (27 - (m + 1)) + 2 ^ (27 - (m + 1)) = 2 ^ (27 - m) by
    rw [show 27 - m = 27 - (m + 1) + 1 by omega, Nat.pow_succ]; omega]

theorem pt_ne_zero {n0 m : Nat} (hm : m ≤ 27) (p : Nat) : pt n0 m p ≠ 0 := by
  rw [pt_eq]
  intro h
  have h' : (31 : Fp) ^ (2 ^ (n0 - m)) * Fp.twoAdicGen m ^ bitrev m p = 0 := Fp8.ofBase_inj h
  exact fp_mul_ne_zero (fp_pow_ne_zero fp31_ne_zero _) (fp_pow_ne_zero (Fp.twoAdicGen_ne_zero m hm) _) h'

theorem pt_inj {n0 m : Nat} (hm : m ≤ 27) {p p' : Nat} (hp : p < 2 ^ m) (hp' : p' < 2 ^ m)
    (h : pt n0 m p = pt n0 m p') : p = p' := by
  rw [pt_eq, pt_eq] at h
  have h' := Fp8.ofBase_inj h
  have hs := fp_pow_ne_zero fp31_ne_zero (2 ^ (n0 - m))
  have hg : Fp.twoAdicGen m ^ bitrev m p = Fp.twoAdicGen m ^ bitrev m p' := by
    have i1 := Field.inv_mul_cancel hs
    have : ((31 : Fp) ^ 2 ^ (n0 - m))⁻¹ * ((31 : Fp) ^ 2 ^ (n0 - m) * Fp.twoAdicGen m ^ bitrev m p) =
        ((31 : Fp) ^ 2 ^ (n0 - m))⁻¹ * ((31 : Fp) ^ 2 ^ (n0 - m) * Fp.twoAdicGen m ^ bitrev m p') := by
      rw [h']
    rw [← Semiring.mul_assoc, ← Semiring.mul_assoc, i1, Semiring.one_mul, Semiring.one_mul] at this
    exact this
  exact bitrev_inj m p p' hp hp' (Fp.twoAdicGen_pow_inj hm (bitrev_lt m p) (bitrev_lt m p') hg)

/-- Sibling positions `2q, 2q + 1` are negatives of each other. -/
theorem pt_sibling {n0 m : Nat} (hm : m + 1 ≤ 27) (q : Nat) :
    pt n0 (m + 1) (2 * q + 1) = - pt n0 (m + 1) (2 * q) := by
  have hh := Fp.twoAdicGen_pow_half (k := m + 1) (by omega) hm
  rw [show m + 1 - 1 = m from rfl] at hh
  rw [pt_eq, pt_eq, bitrev_two_mul_add_one, bitrev_two_mul, Semiring.pow_add, hh, ← Fp8.ofBase_neg]
  congr 1
  grind

/-- Squaring maps position `2q` of the size-`2^(m+1)` domain to position `q`
of the size-`2^m` domain. -/
theorem pt_sq {n0 m : Nat} (hm : m + 1 ≤ 27) (hn : m + 1 ≤ n0) (q : Nat) :
    pt n0 (m + 1) (2 * q) * pt n0 (m + 1) (2 * q) = pt n0 m q := by
  rw [pt_eq, pt_eq, bitrev_two_mul, ← Fp8.ofBase_mul]
  congr 1
  have h2 : (31 : Fp) ^ (2 ^ (n0 - m)) = (31 : Fp) ^ (2 ^ (n0 - (m + 1))) * (31 : Fp) ^ (2 ^ (n0 - (m + 1))) := by
    rw [← Semiring.pow_add]; congr 1
    rw [show n0 - m = n0 - (m + 1) + 1 by omega, Nat.pow_succ]; omega
  have h3 : Fp.twoAdicGen m ^ bitrev m q =
      Fp.twoAdicGen (m + 1) ^ bitrev m q * Fp.twoAdicGen (m + 1) ^ bitrev m q := by
    rw [← twoAdicGen_sq hm]
    generalize bitrev m q = b
    induction b with
    | zero => simp [Semiring.pow_zero]; grind
    | succ b ih => simp only [Semiring.pow_succ, ih]; grind
  rw [h2, h3]; grind

/-! ## The natural-to-verifier maps -/

theorem permK_succ (n0 ℓ k j : Nat) :
    permK n0 ℓ (k + 1) j = 2 * permK n0 ℓ k (j % 2 ^ (n0 - ℓ + k)) + j / 2 ^ (n0 - ℓ + k) := rfl

theorem permK_lt (n0 ℓ : Nat) : ∀ k j, j < 2 ^ (n0 - ℓ + k) → permK n0 ℓ k j < 2 ^ (n0 - ℓ + k)
  | 0, j, hj => by simpa [permK] using hj
  | k + 1, j, hj => by
    rw [permK_succ]
    have hp : 0 < 2 ^ (n0 - ℓ + k) := Nat.pow_pos (by omega)
    have := permK_lt n0 ℓ k (j % 2 ^ (n0 - ℓ + k)) (Nat.mod_lt _ hp)
    rw [show n0 - ℓ + (k + 1) = n0 - ℓ + k + 1 by omega, Nat.pow_succ] at hj ⊢
    have : j / 2 ^ (n0 - ℓ + k) < 2 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
    omega

theorem permK_inj (n0 ℓ : Nat) : ∀ k j j', j < 2 ^ (n0 - ℓ + k) → j' < 2 ^ (n0 - ℓ + k) →
    permK n0 ℓ k j = permK n0 ℓ k j' → j = j'
  | 0, j, j', _, _, h => by simpa [permK] using h
  | k + 1, j, j', hj, hj', h => by
    rw [permK_succ, permK_succ] at h
    have hp : 0 < 2 ^ (n0 - ℓ + k) := Nat.pow_pos (by omega)
    rw [show n0 - ℓ + (k + 1) = n0 - ℓ + k + 1 by omega, Nat.pow_succ] at hj hj'
    have d1 : j / 2 ^ (n0 - ℓ + k) < 2 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
    have d2 : j' / 2 ^ (n0 - ℓ + k) < 2 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
    generalize hu : permK n0 ℓ k (j % 2 ^ (n0 - ℓ + k)) = u at h
    generalize hu' : permK n0 ℓ k (j' % 2 ^ (n0 - ℓ + k)) = u' at h
    generalize ha : j / 2 ^ (n0 - ℓ + k) = a at h d1
    generalize ha' : j' / 2 ^ (n0 - ℓ + k) = a' at h d2
    have hd : a = a' := by omega
    have huu : u = u' := by omega
    rw [← hu, ← hu'] at huu
    have hm := permK_inj n0 ℓ k _ _ (Nat.mod_lt _ hp) (Nat.mod_lt _ hp) huu
    rw [← Nat.div_add_mod j (2 ^ (n0 - ℓ + k)), ← Nat.div_add_mod j' (2 ^ (n0 - ℓ + k)), ha, ha', hd, hm]

/-- Lower half of layer `i`: `permK (k+1) j = 2·permK k j`. -/
theorem permK_lo (n0 ℓ k j : Nat) (hj : j < 2 ^ (n0 - ℓ + k)) :
    permK n0 ℓ (k + 1) j = 2 * permK n0 ℓ k j := by
  rw [permK_succ, Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj]; rfl

/-- Upper half: `permK (k+1) (j + 2^(n0-ℓ+k)) = 2·permK k j + 1`. -/
theorem permK_hi (n0 ℓ k j : Nat) (hj : j < 2 ^ (n0 - ℓ + k)) :
    permK n0 ℓ (k + 1) (j + 2 ^ (n0 - ℓ + k)) = 2 * permK n0 ℓ k j + 1 := by
  have hp : 0 < 2 ^ (n0 - ℓ + k) := Nat.pow_pos (by omega)
  rw [permK_succ, Nat.add_mod_right, Nat.mod_eq_of_lt hj,
    Nat.add_div_right _ hp, Nat.div_eq_of_lt hj]

/-! ## The setup -/

section
variable (A : Air) (prm : Params)

theorem ellOf_le (τ : PTn) : ellOf A prm τ + prm.logBlowup ≤ n0Of A prm τ ∨ ellOf A prm τ = 0 := by
  simp only [ellOf, finalLayer, n0Of]; omega

/-- The FRI setup of a transcript (domains `≤ 2^27`). -/
def mkSetup (τ : PTn) (hn0 : n0Of A prm τ ≤ 27) : Fri.Setup Fp8 where
  r := (setupData A prm τ).r
  nn := (setupData A prm τ).nn
  DD := (setupData A prm τ).DD
  xs := (setupData A prm τ).xs
  hnn i hi := by
    simp only [setupData] at hi ⊢
    have := ellOf_le A prm τ
    rw [show n0Of A prm τ - i = n0Of A prm τ - (i + 1) + 1 by omega, Nat.pow_succ]; omega
  hDD i hi := by
    simp only [setupData] at hi ⊢
    have := ellOf_le A prm τ
    have : ellOf A prm τ ≤ n0Of A prm τ - prm.logBlowup := by
      simp only [ellOf, finalLayer, n0Of]; omega
    rw [show n0Of A prm τ - prm.logBlowup - i = n0Of A prm τ - prm.logBlowup - (i + 1) + 1 by omega,
      Nat.pow_succ]; omega
  hDn i _ := by
    simp only [setupData]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  hdist i hi := by
    intro j j' hj hj' h
    simp only [setupData, permAt] at h hi hj hj'
    have hl : ellOf A prm τ ≤ n0Of A prm τ := by simp only [ellOf, finalLayer, n0Of]; omega
    have e : n0Of A prm τ - ellOf A prm τ + (ellOf A prm τ - i) = n0Of A prm τ - i := by omega
    have b1 := permK_lt (n0Of A prm τ) (ellOf A prm τ) (ellOf A prm τ - i) j (by rw [e]; exact hj)
    have b2 := permK_lt (n0Of A prm τ) (ellOf A prm τ) (ellOf A prm τ - i) j' (by rw [e]; exact hj')
    rw [e] at b1 b2
    exact permK_inj _ _ _ j j' (by rw [e]; exact hj) (by rw [e]; exact hj')
      (pt_inj (by omega) b1 b2 h)
  hneg i j hi hj := by
    simp only [setupData, permAt] at hi hj ⊢
    have hl : ellOf A prm τ ≤ n0Of A prm τ := by simp only [ellOf, finalLayer, n0Of]; omega
    obtain ⟨k, hk⟩ : ∃ k, ellOf A prm τ - i = k + 1 := ⟨ellOf A prm τ - i - 1, by omega⟩
    have hk' : ellOf A prm τ - (i + 1) = k := by omega
    have e : n0Of A prm τ - (i + 1) = n0Of A prm τ - ellOf A prm τ + k := by omega
    rw [hk, e, permK_hi _ _ _ _ (by rw [← e]; exact hj), permK_lo _ _ _ _ (by rw [← e]; exact hj),
      show n0Of A prm τ - i = (n0Of A prm τ - (i + 1)) + 1 by omega]
    exact pt_sibling (by omega) _
  hsq i j hi hj := by
    simp only [setupData, permAt] at hi hj ⊢
    have hl : ellOf A prm τ ≤ n0Of A prm τ := by simp only [ellOf, finalLayer, n0Of]; omega
    obtain ⟨k, hk⟩ : ∃ k, ellOf A prm τ - i = k + 1 := ⟨ellOf A prm τ - i - 1, by omega⟩
    have hk' : ellOf A prm τ - (i + 1) = k := by omega
    have e : n0Of A prm τ - (i + 1) = n0Of A prm τ - ellOf A prm τ + k := by omega
    rw [hk, hk', permK_lo _ _ _ _ (by rw [← e]; exact hj),
      show n0Of A prm τ - i = (n0Of A prm τ - (i + 1)) + 1 by omega]
    exact (pt_sq (by omega) (by omega) _).symm
  hnz i j hi _ := pt_ne_zero (by omega) _
  htwo := by decide +kernel

end
end ZkFormal.Udr.Np
