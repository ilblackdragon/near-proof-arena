import ZkFormal.Udr.Count

/-!
# ZkFormal.Udr.Poly — minimal polynomial toolkit over a `Lean.Grind.Field`

Polynomials are coefficient functions `c : Nat → K` read with an explicit
length `m` (coefficients `c 0, …, c (m-1)`), evaluated by Horner's rule.
This is all the coding-theory lemmas of L3 need: linearity, padding,
products (`IsPoly`), synthetic division by `X - r`, the **root bound in
coefficient form** (a length-`m` polynomial with `m` distinct roots has all
coefficients zero), and bivariate evaluation with the Fubini swap.

(L1 provides the protocol's `Poly`; this file is the self-contained
algebra used inside the L3 proofs and is generic in the field.)
-/

namespace ZkFormal.Udr

open ArenaCore.Security
open Lean.Grind

set_option linter.unusedSectionVars false

variable {K : Type} [Field K]

/-- Horner evaluation of the length-`m` polynomial with coefficients `c`. -/
def ev : Nat → (Nat → K) → K → K
  | 0, _, _ => 0
  | m + 1, c, x => c 0 + x * ev m (fun k => c (k + 1)) x

@[simp] theorem ev_zero (c : Nat → K) (x : K) : ev 0 c x = 0 := rfl

theorem ev_succ (m : Nat) (c : Nat → K) (x : K) :
    ev (m + 1) c x = c 0 + x * ev m (fun k => c (k + 1)) x := rfl

theorem ev_lin (m : Nat) (a b : K) (c c' : Nat → K) (x : K) :
    ev m (fun k => a * c k + b * c' k) x = a * ev m c x + b * ev m c' x := by
  induction m generalizing c c' with
  | zero => simp only [ev_zero]; grind
  | succ m ih =>
    simp only [ev_succ]
    rw [ih (fun k => c (k + 1)) (fun k => c' (k + 1))]
    grind

theorem ev_congr {m : Nat} {c c' : Nat → K} (h : ∀ k, k < m → c k = c' k) (x : K) :
    ev m c x = ev m c' x := by
  induction m generalizing c c' with
  | zero => rfl
  | succ m ih =>
    simp only [ev_succ]
    rw [h 0 (by omega), ih (fun k hk => h (k + 1) (by omega))]

theorem ev_eq_zero {m : Nat} {c : Nat → K} (h : ∀ k, k < m → c k = 0) (x : K) : ev m c x = 0 := by
  rw [ev_congr (c' := fun _ => 0) h]
  have := ev_lin m 0 0 (fun _ => (0 : K)) (fun _ => 0) x
  simp only at this
  rw [show (fun (_ : Nat) => (0 : K) * 0 + 0 * 0) = fun _ => (0 : K) by funext; grind] at this
  rw [this]; grind

theorem ev_add (m : Nat) (c c' : Nat → K) (x : K) :
    ev m (fun k => c k + c' k) x = ev m c x + ev m c' x := by
  have := ev_lin m 1 1 c c' x
  rw [show (fun k => (1 : K) * c k + 1 * c' k) = fun k => c k + c' k by funext; grind] at this
  rw [this]; grind

theorem ev_smul (m : Nat) (a : K) (c : Nat → K) (x : K) :
    ev m (fun k => a * c k) x = a * ev m c x := by
  have := ev_lin m a 0 c c x
  rw [show (fun k => a * c k + 0 * c k) = fun k => a * c k by funext; grind] at this
  rw [this]; grind

theorem ev_neg (m : Nat) (c : Nat → K) (x : K) :
    ev m (fun k => - c k) x = - ev m c x := by
  have := ev_smul m (-1) c x
  rw [show (fun k => (-1 : K) * c k) = fun k => - c k by funext; grind] at this
  rw [this]; grind

theorem ev_sub (m : Nat) (c c' : Nat → K) (x : K) :
    ev m (fun k => c k - c' k) x = ev m c x - ev m c' x := by
  have := ev_lin m 1 (-1) c c' x
  rw [show (fun k => (1 : K) * c k + -1 * c' k) = fun k => c k - c' k by funext; grind] at this
  rw [this]; grind

theorem ev_succ_last (m : Nat) (c : Nat → K) (x : K) :
    ev (m + 1) c x = ev m c x + c m * x ^ m := by
  induction m generalizing c with
  | zero => simp only [ev_succ, ev_zero]; grind
  | succ m ih =>
    rw [ev_succ (m + 1) c, ih, ev_succ m c]
    simp only [Nat.add_comm m 1]
    rw [show (1 + m) = m + 1 by omega]
    grind

/-- Padding with zero coefficients does not change the value. -/
theorem ev_pad {m m' : Nat} (hm : m ≤ m') {c : Nat → K} (h : ∀ k, m ≤ k → k < m' → c k = 0)
    (x : K) : ev m' c x = ev m c x := by
  induction m' with
  | zero => have : m = 0 := by omega
            subst this; rfl
  | succ m' ih =>
    by_cases hmm : m = m' + 1
    · subst hmm; rfl
    · rw [ev_succ_last, ih (by omega) (fun k h1 h2 => h k h1 (by omega)), h m' (by omega) (by omega)]
      grind

/-! ## Polynomial functions -/

/-- `φ` is a polynomial function of length `≤ m` (degree `< m`). -/
def IsPoly (m : Nat) (φ : K → K) : Prop := ∃ c : Nat → K, ∀ x, φ x = ev m c x

theorem IsPoly.of_ev (m : Nat) (c : Nat → K) : IsPoly m (ev m c) := ⟨c, fun _ => rfl⟩

theorem IsPoly.mono {m m' : Nat} (hm : m ≤ m') {φ : K → K} (h : IsPoly m φ) : IsPoly m' φ := by
  classical
  obtain ⟨c, hc⟩ := h
  refine ⟨fun k => if k < m then c k else 0, fun x => ?_⟩
  rw [ev_pad hm (fun k h1 _ => by simp only [show ¬ k < m by omega, ite_false]), hc x]
  exact ev_congr (fun k hk => by simp only [hk, ite_true]) x

theorem IsPoly.const (a : K) : IsPoly 1 (fun _ => a) :=
  ⟨fun _ => a, fun x => by simp only [ev_succ, ev_zero]; grind⟩

theorem IsPoly.add {m : Nat} {φ ψ : K → K} (h1 : IsPoly m φ) (h2 : IsPoly m ψ) :
    IsPoly m (fun x => φ x + ψ x) := by
  obtain ⟨c, hc⟩ := h1; obtain ⟨c', hc'⟩ := h2
  exact ⟨fun k => c k + c' k, fun x => by show φ x + ψ x = _; rw [ev_add, hc, hc']⟩

theorem IsPoly.smul {m : Nat} (a : K) {φ : K → K} (h : IsPoly m φ) : IsPoly m (fun x => a * φ x) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨fun k => a * c k, fun x => by show a * φ x = _; rw [ev_smul, hc]⟩

theorem IsPoly.neg {m : Nat} {φ : K → K} (h : IsPoly m φ) : IsPoly m (fun x => - φ x) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨fun k => - c k, fun x => by show - φ x = _; rw [ev_neg, hc]⟩

theorem IsPoly.sub {m : Nat} {φ ψ : K → K} (h1 : IsPoly m φ) (h2 : IsPoly m ψ) :
    IsPoly m (fun x => φ x - ψ x) := by
  obtain ⟨c, hc⟩ := h1; obtain ⟨c', hc'⟩ := h2
  exact ⟨fun k => c k - c' k, fun x => by show φ x - ψ x = _; rw [ev_sub, hc, hc']⟩

theorem IsPoly.mulX {m : Nat} {φ : K → K} (h : IsPoly m φ) : IsPoly (m + 1) (fun x => x * φ x) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨fun k => if k = 0 then 0 else c (k - 1), fun x => by
    show x * φ x = _
    rw [ev_succ, hc]; simp only [Nat.add_sub_cancel, Nat.add_one_ne_zero, ite_false, ite_true]
    grind⟩

theorem IsPoly.mul {a b : Nat} {φ ψ : K → K} (h1 : IsPoly (a + 1) φ) (h2 : IsPoly (b + 1) ψ) :
    IsPoly (a + b + 1) (fun x => φ x * ψ x) := by
  induction a generalizing φ with
  | zero =>
    obtain ⟨c, hc⟩ := h1
    obtain ⟨d, hd⟩ := h2.smul (c 0)
    rw [Nat.zero_add]
    exact ⟨d, fun x => by rw [← hd]; show φ x * ψ x = _; rw [hc]; simp only [ev_succ, ev_zero]; grind⟩
  | succ a ih =>
    obtain ⟨c, hc⟩ := h1
    have hq : IsPoly (a + b + 1) (fun x => ev (a + 1) (fun k => c (k + 1)) x * ψ x) :=
      ih (IsPoly.of_ev _ _)
    have h3 := (hq.mulX).add ((h2.smul (c 0)).mono (m' := a + b + 2) (by omega))
    have e : (a + 1 + b + 1) = a + b + 1 + 1 := by omega
    rw [e]
    obtain ⟨d, hd⟩ := h3
    exact ⟨d, fun x => by rw [← hd]; show φ x * ψ x = _; rw [hc, ev_succ]; grind⟩

/-! ## Synthetic division and the root bound -/

/-- Quotient of the length-`m` polynomial `c` by `X - r` (length `m - 1`). -/
def quot : Nat → (Nat → K) → K → (Nat → K)
  | 0, _, _ => fun _ => 0
  | m + 1, c, r => fun k => if k = 0 then ev m (fun j => c (j + 1)) r
      else quot m (fun j => c (j + 1)) r (k - 1)

theorem quot_idx_zero (m : Nat) (c : Nat → K) (r : K) :
    quot (m + 1) c r 0 = ev m (fun j => c (j + 1)) r := by simp only [quot, ite_true]

theorem quot_idx_succ (m : Nat) (c : Nat → K) (r : K) (k : Nat) :
    quot (m + 1) c r (k + 1) = quot m (fun j => c (j + 1)) r k := by
  simp only [quot, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]

theorem quot_div (m : Nat) (c : Nat → K) (r x : K) :
    ev (m + 1) c x = (x - r) * ev m (quot (m + 1) c r) x + ev (m + 1) c r := by
  induction m generalizing c with
  | zero => simp only [ev_succ, ev_zero]; grind
  | succ m ih =>
    rw [ev_succ (m + 1) c x, ih (fun k => c (k + 1)), ev_succ m (quot (m + 1 + 1) c r) x,
      quot_idx_zero]
    simp only [quot_idx_succ]
    rw [ev_succ (m + 1) c r]
    grind

theorem quot_top (m : Nat) (c : Nat → K) (r : K) : quot (m + 1) c r m = 0 := by
  induction m generalizing c with
  | zero => rw [quot_idx_zero]; rfl
  | succ m ih => rw [quot_idx_succ]; exact ih _

theorem quot_coeff (m : Nat) (c : Nat → K) (r : K) (k : Nat) (hk : k < m) :
    c (k + 1) = quot (m + 1) c r k - r * quot (m + 1) c r (k + 1) := by
  induction m generalizing c k with
  | zero => omega
  | succ m ih =>
    cases k with
    | zero =>
      rw [quot_idx_zero, quot_idx_succ, ev_succ]
      cases m with
      | zero => simp only [ev_zero, quot]; grind
      | succ m => rw [quot_idx_zero]; grind
    | succ k =>
      have := ih (fun j => c (j + 1)) k (by omega)
      rw [quot_idx_succ, quot_idx_succ]
      exact this

theorem coeff0_eq (m : Nat) (c : Nat → K) (r : K) :
    c 0 = ev (m + 1) c r - r * quot (m + 1) c r 0 := by
  rw [quot_idx_zero, ev_succ]; grind

/-- **Root bound, coefficient form.** A length-`m` polynomial vanishing at
`m` distinct points has all coefficients zero. -/
theorem coeffs_zero_of_roots : ∀ (m : Nat) (c : Nat → K) (l : List K), l.Nodup → m ≤ l.length →
    (∀ r ∈ l, ev m c r = 0) → ∀ k, k < m → c k = 0
  | 0, _, _, _, _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | m + 1, c, [], _, hlen, _, _, _ => absurd hlen (by simp)
  | m + 1, c, r :: l, hl, hlen, hr, k, hk => by
    rw [List.nodup_cons] at hl
    have hr0 : ev (m + 1) c r = 0 := hr r (List.mem_cons_self ..)
    -- the quotient vanishes on `l`
    have hq : ∀ s ∈ l, ev m (quot (m + 1) c r) s = 0 := by
      intro s hs
      have hsr : s - r ≠ 0 := by
        intro h
        have : s = r := by grind
        exact hl.1 (this ▸ hs)
      have e := quot_div m c r s
      rw [hr s (List.mem_cons_of_mem _ hs), hr0] at e
      have hinv := Field.mul_inv_cancel hsr
      have : (s - r)⁻¹ * ((s - r) * ev m (quot (m + 1) c r) s) = 0 := by grind
      grind
    have hq0 := coeffs_zero_of_roots m (quot (m + 1) c r) l hl.2 (by simp at hlen; omega) hq
    have hqall : ∀ j, j ≤ m → quot (m + 1) c r j = 0 := fun j hj => by
      by_cases hjm : j = m
      · subst hjm; exact quot_top _ _ _
      · exact hq0 j (by omega)
    cases k with
    | zero => rw [coeff0_eq m c r, hr0, hqall 0 (Nat.zero_le _)]; grind
    | succ k =>
      rw [quot_coeff m c r k (by omega), hqall k (by omega), hqall (k + 1) (by omega)]; grind

/-- Root bound, function form. -/
theorem IsPoly.eq_zero_of_roots {m : Nat} {φ : K → K} (hφ : IsPoly m φ) (l : List K)
    (hl : l.Nodup) (hlen : m ≤ l.length) (hr : ∀ r ∈ l, φ r = 0) : ∀ x, φ x = 0 := by
  obtain ⟨c, hc⟩ := hφ
  have := coeffs_zero_of_roots m c l hl hlen (fun r hr' => (hc r) ▸ hr r hr')
  intro x; rw [hc x]; exact ev_eq_zero this x

/-- Root bound, counting form: a polynomial with a nonzero coefficient below
`m` has fewer than `m` roots in any duplicate-free list. -/
theorem count_roots_lt {m : Nat} {c : Nat → K} (hc : ∃ k, k < m ∧ c k ≠ 0) (l : List K)
    (hl : l.Nodup) : count l (fun r => ev m c r = 0) < m := by
  classical
  refine Nat.lt_of_not_le fun hm => ?_
  obtain ⟨k, hk, hck⟩ := hc
  rw [count_eq_length_filter] at hm
  exact hck (coeffs_zero_of_roots m c _ (hl.filter _) hm
    (fun r hr => by simpa using (List.mem_filter.mp hr).2) k hk)

/-! ## Bivariate evaluation -/

/-- Fubini for Horner evaluation: `B k j` is the coefficient of `X^k Z^j`. -/
theorem ev_swap (mx mz : Nat) (B : Nat → Nat → K) (x z : K) :
    ev mx (fun k => ev mz (B k) z) x = ev mz (fun j => ev mx (fun k => B k j) x) z := by
  induction mx generalizing B with
  | zero => simp only [ev_zero]; exact (ev_eq_zero (fun _ _ => rfl) z).symm
  | succ mx ih =>
    rw [ev_succ, ih (fun k => B (k + 1))]
    have := ev_lin mz 1 x (B 0) (fun j => ev mx (fun k => B (k + 1) j) x) z
    rw [show (fun j => (1 : K) * B 0 j + x * ev mx (fun k => B (k + 1) j) x) =
      fun j => ev (mx + 1) (fun k => B k j) x by funext j; rw [ev_succ]; grind] at this
    rw [this]; grind

end ZkFormal.Udr
