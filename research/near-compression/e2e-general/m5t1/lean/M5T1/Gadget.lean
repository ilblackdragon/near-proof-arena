import M5T1.Ize
import M5T1.Rx

/-!
# M5T1.Gadget — the `RX` gadgets (`Rx.lin`, `Rx.mulT`) as natural-number equations

* `lin_val`: the `N` limb constraints of `Rx.lin N terms r cy top`, vanishing in the field, with the
  terms / results / carries evaluating (as integers) to naturals small enough not to wrap, give
  `val T N = val R N + 256^N · top`.
* `ize_mulT` / `conv_le` / `val_pad`: the schoolbook product's limbs and bounds.
-/

namespace M5T1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound

variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

theorem lin_mem {N : Nat} {terms rr cy : Nat → Expr} {top : Expr} {k : Nat} (hk : k < N) :
    (terms k + (if k = 0 then K 0 else cy (k - 1)) - rr k - K 256 * (if k + 1 = N then top else cy k))
      ∈ Rx.lin N terms rr cy top := by
  unfold Rx.lin
  exact List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩

/-- **The carry-chain gadget is exact.** -/
theorem lin_val {N : Nat} {terms rr cy : Nat → Expr} {top : Expr} (hN : 0 < N)
    (hz : ∀ e ∈ Rx.lin N terms rr cy top, ev tr t r pub e = 0)
    (T R C : Nat → Nat) (tp : Nat)
    (hT : ∀ k < N, ize tr t r pub (terms k) = T k) (hR : ∀ k < N, ize tr t r pub (rr k) = R k)
    (hC : ∀ k, k + 1 < N → ize tr t r pub (cy k) = C k) (htop : ize tr t r pub top = tp)
    (hb1 : ∀ k < N, T k + (if k = 0 then 0 else C (k - 1)) < PP)
    (hb2 : ∀ k < N, R k + 256 * (if k + 1 = N then tp else C k) < PP) :
    val T N = val R N + 256 ^ N * tp := by
  apply chain_val N T R C tp hN
  intro k hk
  have hm := lin_mem (terms := terms) (rr := rr) (cy := cy) (top := top) hk
  have h0 := hz _ hm
  have hb1k := hb1 k hk
  have hb2k := hb2 k hk
  have hcin : ize tr t r pub (if k = 0 then K 0 else cy (k - 1)) = ((if k = 0 then 0 else C (k - 1) : Nat) : Int) := by
    split
    · rfl
    · rename_i h; rw [hC (k - 1) (by omega)]
  have hcout : ize tr t r pub (if k + 1 = N then top else cy k) = ((if k + 1 = N then tp else C k : Nat) : Int) := by
    split
    · rw [htop]
    · rename_i h; rw [hC k (by omega)]
  have hz' := ize_eq_zero (tr := tr) (t := t) (r := r) (pub := pub) h0
  simp only [ize_hsub, ize_hadd, ize_hmul, ize_K, hT k hk, hR k hk, hcin, hcout] at hz'
  have := hz' (by unfold PP at *; omega) (by unfold PP at *; omega)
  omega

/-! ## Products -/

/-- The limbs of a schoolbook product, as naturals. -/
def conv (A B : Nat → Nat) (na nb k : Nat) : Nat :=
  ((List.range na).map fun i => if i ≤ k ∧ k - i < nb then A i * B (k - i) else 0).sum

theorem sum_filterMap_ize (l : List Nat) (f : Nat → Option Expr) :
    ((l.filterMap f).map (ize tr t r pub)).sum =
      (l.map fun i => match f i with | some e => ize tr t r pub e | none => 0).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.filterMap_cons, List.map_cons, List.sum_cons]
    cases f x <;> simp [ih]

theorem ize_mulT (a b : Nat → Expr) (na nb k : Nat) (A B : Nat → Nat)
    (hA : ∀ i < na, ize tr t r pub (a i) = A i) (hB : ∀ j < nb, ize tr t r pub (b j) = B j) :
    ize tr t r pub (Rx.mulT a na b nb k) = conv A B na nb k := by
  unfold Rx.mulT conv
  rw [ize_sumE, sum_filterMap_ize]
  have : ∀ (l : List Nat), (∀ i ∈ l, i < na) →
      (l.map fun i => match (if i ≤ k ∧ k - i < nb then some (a i * b (k - i)) else none) with
        | some e => ize tr t r pub e | none => 0).sum =
      (((l.map fun i => if i ≤ k ∧ k - i < nb then A i * B (k - i) else 0).sum : Nat) : Int) := by
    intro l hl
    induction l with
    | nil => rfl
    | cons x l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih (fun i hi => hl i (List.mem_cons_of_mem _ hi))]
      have hx := hl x (List.mem_cons_self ..)
      by_cases hc : x ≤ k ∧ k - x < nb
      · simp only [hc, and_self, ite_true, ize_hmul, hA x hx, hB (k - x) hc.2]
        push_cast; rfl
      · simp only [hc, ite_false]
        push_cast; omega
  exact this _ (fun i hi => List.mem_range.1 hi)

theorem conv_le (A B : Nat → Nat) (na nb k : Nat) (hA : ∀ i < na, A i < 256) (hB : ∀ j < nb, B j < 256) :
    conv A B na nb k ≤ na * 65025 := by
  unfold conv
  have : ∀ (l : List Nat), (∀ i ∈ l, i < na) →
      (l.map fun i => if i ≤ k ∧ k - i < nb then A i * B (k - i) else 0).sum ≤ l.length * 65025 := by
    intro l hl
    induction l with
    | nil => simp
    | cons x l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have ih' := ih (fun i hi => hl i (List.mem_cons_of_mem _ hi))
      have hx := hl x (List.mem_cons_self ..)
      split
      · rename_i hc
        have h1 := hA x hx
        have h2 := hB (k - x) hc.2
        have : A x * B (k - x) ≤ 255 * 255 := Nat.mul_le_mul (by omega) (by omega)
        rw [Nat.add_mul]; omega
      · rw [Nat.add_mul]; omega
  have h := this (List.range na) (fun i hi => List.mem_range.1 hi)
  simpa using h

theorem val_pad (f : Nat → Nat) (m n : Nat) (h : m ≤ n) :
    val (fun k => if k < m then f k else 0) n = val f m := by
  induction n with
  | zero => have : m = 0 := by omega
            subst this; rfl
  | succ n ih =>
    rcases Nat.lt_or_ge n m with h1 | h1
    · have : m = n + 1 := by omega
      subst this
      simp only [val]
      rw [val_congr _ f n (fun k hk => by simp [show k < n + 1 by omega])]
      simp
    · simp only [val, ih h1, show ¬ n < m by omega, ite_false, Nat.mul_zero, Nat.add_zero]

end M5T1
