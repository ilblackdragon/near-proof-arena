import ZkFormal.Udr.Deep

/-!
# ZkFormal.Udr.SumR — finite sums over a field, and batching as an `eq`-weighted sum

* `sumR n f = f 0 + … + f (n-1)` with the usual algebra;
* `eqF rs j = ∏ₖ rs[k]^{bit k of j}` and `(eqTable rs)[j] = eqF rs j` (L4's
  batching coefficients);
* `batchAll_col`: the multilinear batch is the `eqF`-weighted sum of columns.
-/

namespace ZkFormal.Udr

open Lean.Grind

variable {K : Type} [Field K]

def sumR : Nat → (Nat → K) → K
  | 0, _ => 0
  | n + 1, f => sumR n f + f n

@[simp] theorem sumR_zero (f : Nat → K) : sumR 0 f = 0 := rfl
theorem sumR_succ (n : Nat) (f : Nat → K) : sumR (n + 1) f = sumR n f + f n := rfl

theorem sumR_congr {n : Nat} {f g : Nat → K} (h : ∀ i, i < n → f i = g i) : sumR n f = sumR n g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumR_succ, sumR_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem sumR_add (n : Nat) (f g : Nat → K) : sumR n (fun i => f i + g i) = sumR n f + sumR n g := by
  induction n with
  | zero => simp only [sumR_zero]; grind
  | succ n ih => rw [sumR_succ, sumR_succ, sumR_succ, ih]; grind

theorem sumR_sub (n : Nat) (f g : Nat → K) : sumR n (fun i => f i - g i) = sumR n f - sumR n g := by
  induction n with
  | zero => simp only [sumR_zero]; grind
  | succ n ih => rw [sumR_succ, sumR_succ, sumR_succ, ih]; grind

theorem sumR_mul_left (n : Nat) (a : K) (f : Nat → K) : sumR n (fun i => a * f i) = a * sumR n f := by
  induction n with
  | zero => simp only [sumR_zero]; grind
  | succ n ih => rw [sumR_succ, sumR_succ, ih]; grind

theorem sumR_mul_right (n : Nat) (a : K) (f : Nat → K) : sumR n (fun i => f i * a) = sumR n f * a := by
  induction n with
  | zero => simp only [sumR_zero]; grind
  | succ n ih => rw [sumR_succ, sumR_succ, ih]; grind

theorem sumR_eq_zero {n : Nat} {f : Nat → K} (h : ∀ i, i < n → f i = 0) : sumR n f = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumR_succ, ih (fun i hi => h i (by omega)), h n (by omega)]; grind

theorem sumR_append (a b : Nat) (f : Nat → K) : sumR (a + b) f = sumR a f + sumR b (fun i => f (a + i)) := by
  induction b with
  | zero => simp only [Nat.add_zero, sumR_zero]; grind
  | succ b ih => rw [← Nat.add_assoc, sumR_succ, ih, sumR_succ]; grind

/-- Truncate a sum whose terms vanish beyond `m`. -/
theorem sumR_trunc {m n : Nat} (hmn : m ≤ n) {f : Nat → K} (h : ∀ i, m ≤ i → i < n → f i = 0) :
    sumR n f = sumR m f := by
  obtain ⟨b, rfl⟩ : ∃ b, n = m + b := ⟨n - m, by omega⟩
  rw [sumR_append, sumR_eq_zero (fun i hi => h (m + i) (by omega) (by omega))]; grind

theorem sumR_double (n : Nat) (f : Nat → K) :
    sumR (2 * n) f = sumR n (fun j => f (2 * j) + f (2 * j + 1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, sumR_succ, sumR_succ, ih, sumR_succ]
    rw [show 2 * n + 1 = 2 * n + 1 by rfl]; grind

/-! ## Batching coefficients -/

/-- `∏ₖ rs[k]^{bit k of j}` (bit 0 ↔ the first challenge). -/
def eqF : List K → Nat → K
  | [], _ => 1
  | r :: rs, j => (if j % 2 = 1 then r else 1) * eqF rs (j / 2)

/-- One step of L4's `eqTable` fold. -/
def eqStep (eqs : List K) (r : K) : List K := eqs ++ eqs.map (· * r)

theorem eqStep_length (eqs : List K) (r : K) : (eqStep eqs r).length = 2 * eqs.length := by
  simp [eqStep]; omega

theorem foldl_eqStep_length : ∀ (rs : List K) (L : List K),
    (rs.foldl eqStep L).length = 2 ^ rs.length * L.length
  | [], L => by simp
  | r :: rs, L => by
    rw [List.foldl_cons, foldl_eqStep_length rs, eqStep_length, List.length_cons, Nat.pow_succ,
      Nat.mul_comm (2 ^ rs.length) 2, Nat.mul_assoc, Nat.mul_left_comm]

theorem eqStep_getD (eqs : List K) (r : K) (i b : Nat) (hi : i < eqs.length) (hb : b < 2) :
    (eqStep eqs r).getD (i + eqs.length * b) 0 = eqs.getD i 0 * (if b = 1 then r else 1) := by
  simp only [eqStep, List.getD_eq_getElem?_getD]
  cases b with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero, List.getElem?_append_left hi]
    simp only [Nat.zero_ne_one, ite_false]; grind
  | succ b =>
    have : b = 0 := by omega
    subst this
    rw [List.getElem?_append_right (by omega)]
    simp only [List.getElem?_map, ite_true]
    rw [List.getElem?_eq_getElem hi]; simp [List.getElem?_eq_getElem hi]

theorem foldl_eqStep_getD : ∀ (rs : List K) (L : List K) (i j : Nat), i < L.length → j < 2 ^ rs.length →
    (rs.foldl eqStep L).getD (i + L.length * j) 0 = L.getD i 0 * eqF rs j
  | [], L, i, j, hi, hj => by
    have : j = 0 := by simp at hj; omega
    subst this; simp [eqF]; grind
  | r :: rs, L, i, j, hi, hj => by
    rw [List.foldl_cons]
    have hL : (eqStep L r).length = 2 * L.length := eqStep_length L r
    have hidx : i + L.length * j = (i + L.length * (j % 2)) + (eqStep L r).length * (j / 2) := by
      rw [hL]
      have := Nat.mod_add_div j 2
      calc i + L.length * j = i + L.length * (j % 2 + 2 * (j / 2)) := by rw [this]
        _ = _ := by rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm L.length 2]; omega
    rw [hidx, foldl_eqStep_getD rs (eqStep L r) _ _ (by
        have := Nat.mod_lt j (show 0 < 2 by omega)
        rw [hL]
        have : L.length * (j % 2) ≤ L.length * 1 := Nat.mul_le_mul_left _ (by omega)
        omega)
      (by simp [List.length_cons, Nat.pow_succ] at hj; omega)]
    rw [eqStep_getD L r i (j % 2) hi (Nat.mod_lt _ (by omega))]
    simp only [eqF]
    by_cases h : j % 2 = 1 <;> simp [h] <;> grind

/-- **L4's batching coefficients**: `(eqTable rs)[j] = eqF rs j`. -/
theorem eqTable_getD (rs : List K) (j : Nat) (hj : j < 2 ^ rs.length) :
    (rs.foldl eqStep [1]).getD j 0 = eqF rs j := by
  have := foldl_eqStep_getD rs [1] 0 j (by simp) hj
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul] at this
  rw [this]; simp; grind

/-- **Batching is the `eqF`-weighted sum of columns.** -/
theorem batchAll_col : ∀ (rs : List K) (W : Word Nat K) (p c : Nat),
    batchAll rs W p c = sumR (2 ^ rs.length) (fun j => eqF rs j * W p (c * 2 ^ rs.length + j))
  | [], W, p, c => by simp [batchAll, sumR, eqF]; grind
  | r :: rs, W, p, c => by
    simp only [batchAll]
    rw [batchAll_col rs (batchStep W r) p c, List.length_cons, Nat.pow_succ, Nat.mul_comm _ 2,
      sumR_double]
    apply sumR_congr
    intro j _
    simp only [batchStep, line, evenCols, oddCols, eqF]
    have h0 : (2 * j) % 2 = 0 := by omega
    have h1 : (2 * j + 1) % 2 = 1 := by omega
    have d0 : 2 * j / 2 = j := by omega
    have d1 : (2 * j + 1) / 2 = j := by omega
    rw [ite_eq_right (by omega), ite_eq_left h1, d0, d1,
      show c * (2 * 2 ^ rs.length) + 2 * j = 2 * (c * 2 ^ rs.length + j) by
        rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm c 2, Nat.mul_assoc],
      show c * (2 * 2 ^ rs.length) + (2 * j + 1) = 2 * (c * 2 ^ rs.length + j) + 1 by
        rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm c 2, Nat.mul_assoc]; omega]
    grind

end ZkFormal.Udr
