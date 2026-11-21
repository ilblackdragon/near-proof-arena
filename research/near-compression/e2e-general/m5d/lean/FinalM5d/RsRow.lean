import FinalM5d.RsCoeff
import FinalM5d.FinRow

/-!
# FinalM5d.RsRow — an `RS` row's parity bits from its constraints

On any row of any trace where the exported `Rs.table`'s constraints vanish over BabyBear with
`act = 1` and the `q` cells below 256 (`R8` lookups, a premise here), every data bit and parity
bit is boolean and **parity bit `k` of parity part `i` is the parity of the data bits `Rs.paritySum`
selects** (`rs_parity_bit`): `r_ik = (Σ_{(j,m) : mulBit M[d+i][j] k m = 1} x_j[m]) mod 2` — with
`RsCoeff.coeff_linear`, that is bit `k` of `⊕_j gfMul M[d+i][j] d_j`, the spec's `parityPart` byte.
-/

namespace FinalM5d.RsRow

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound FinalM5d FinalM5d.FinRow

variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

local notation "PR" => 2013265921

theorem ev_sumE (l : List Expr) : ev tr t r pub (sumE l) = (l.map (ev tr t r pub)).sum % PR := by
  induction l using sumE.induct with
  | case1 => simp [sumE]
  | case2 a => simp [sumE, Nat.mod_eq_of_lt (ev_lt a)]
  | case3 a b rest h ih1 ih2 =>
    rw [sumE, ev_add, ih1, ih2, Nat.add_mod_mod, Nat.mod_add_mod, ← List.sum_append, ← List.map_append,
      List.take_append_drop]

/-- The data cells `Rs.paritySum i k` adds. -/
def sel (i k : Nat) : List Expr :=
  (List.range RSD).flatMap fun j => (List.range 8).filterMap fun m =>
    if Rs.mulBit (Rs.matrix.get (RSD + i) j) k m == 1 then some (Rs.T.c "x" (8 * j + m)) else none

theorem sel_sub (i k : Nat) : ∀ e ∈ sel i k, ∃ c, c < 8 * RSD ∧ e = Rs.T.c "x" c := by
  intro e he
  simp only [sel, List.mem_flatMap, List.mem_range, List.mem_filterMap] at he
  obtain ⟨j, hj, m, hm, h⟩ := he
  split at h
  · cases h; exact ⟨8 * j + m, by simp only [RSD] at hj ⊢; omega, rfl⟩
  · cases h

theorem sel_length : ∀ i, i < NPAR → ∀ k, k < 8 → (sel i k).length ≤ 8 * RSD := by
  decide +kernel

theorem sum_le_length : ∀ (l : List Nat), (∀ x ∈ l, x ≤ 1) → l.sum ≤ l.length
  | [], _ => by simp
  | a :: l, h => by
    have := sum_le_length l (fun x hx => h x (List.mem_cons_of_mem a hx))
    have ha := h a List.mem_cons_self
    simp only [List.sum_cons, List.length_cons]; omega

section
variable (hc : ∀ e ∈ Rs.constraints, e.eval tr t r pub = 0) (hact : ev tr t r pub Rs.act = 1)
include hc hact

theorem x_bool (c : Nat) (hc' : c < 8 * RSD) : ev tr t r pub (Rs.T.c "x" c) ≤ 1 := by
  have hm : bool (Rs.T.c "x" c) ∈ Rs.constraints := by
    unfold Rs.constraints
    simp only [List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨c, hc', rfl⟩)))
  have h0 := ev_of_eval (hc _ hm)
  change ev tr t r pub (Expr.mul _ (Expr.add _ (Expr.neg (Expr.const 1)))) = 0 at h0
  rcases ev_mul_eq_zero h0 with h | h
  · omega
  · simp only [ev_add, ev_neg, ev_const] at h
    have := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) (Rs.T.c "x" c)
    omega

theorem r_bool (c : Nat) (hc' : c < 8 * NPAR) : ev tr t r pub (Rs.T.c "r" c) ≤ 1 := by
  have hm : bool (Rs.T.c "r" c) ∈ Rs.constraints := by
    unfold Rs.constraints
    simp only [List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl (Or.inl (Or.inr ⟨c, hc', rfl⟩))
  have h0 := ev_of_eval (hc _ hm)
  change ev tr t r pub (Expr.mul _ (Expr.add _ (Expr.neg (Expr.const 1)))) = 0 at h0
  rcases ev_mul_eq_zero h0 with h | h
  · omega
  · simp only [ev_add, ev_neg, ev_const] at h
    have := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) (Rs.T.c "r" c)
    omega

/-- **Parity bit `k` of parity part `i`** is the parity of its selected data bits. -/
theorem rs_parity_bit (hq : ∀ c, c < 8 * NPAR → ev tr t r pub (Rs.T.c "q" c) < 256)
    {i k : Nat} (hi : i < NPAR) (hk : k < 8) :
    ev tr t r pub (Rs.T.c "r" (8 * i + k)) = ((sel i k).map (ev tr t r pub)).sum % 2 := by
  have hm : Rs.act * (Rs.paritySum i k - Rs.T.c "r" (8 * i + k) - K 2 * Rs.T.c "q" (8 * i + k)) ∈
      Rs.constraints := by
    unfold Rs.constraints
    simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
    exact Or.inr ⟨i, hi, k, hk, rfl⟩
  have h0 := ev_of_eval (hc _ hm)
  rcases ev_mul_eq_zero h0 with h | h
  · rw [hact] at h; omega
  have hps : ev tr t r pub (Rs.paritySum i k) = ((sel i k).map (ev tr t r pub)).sum := by
    have e : Rs.paritySum i k = sumE (sel i k) := rfl
    rw [e, ev_sumE]
    apply Nat.mod_eq_of_lt
    have hb : ∀ x ∈ (sel i k).map (ev tr t r pub), x ≤ 1 := by
      intro x hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
      obtain ⟨c, hc', rfl⟩ := sel_sub i k e he
      exact x_bool hc hact c hc'
    have := sum_le_length _ hb
    have hl := sel_length i hi k hk
    simp only [List.length_map] at this
    simp only [RSD] at hl
    omega
  have hr := r_bool hc hact (8 * i + k) (by simp only [NPAR, RST, RSD] at hi ⊢; omega)
  have hqq := hq (8 * i + k) (by simp only [NPAR, RST, RSD] at hi ⊢; omega)
  have hlt := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) (Rs.paritySum i k)
  have hs := (hps ▸ (show ev tr t r pub (Rs.paritySum i k) ≤ 8 * RSD from by
    rw [hps]
    have hb : ∀ x ∈ (sel i k).map (ev tr t r pub), x ≤ 1 := by
      intro x hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
      obtain ⟨c, hc', rfl⟩ := sel_sub i k e he
      exact x_bool hc hact c hc'
    have := sum_le_length _ hb
    have hl := sel_length i hi k hk
    simp only [List.length_map] at this
    omega))
  rw [← hps]
  simp only [RSD] at hs
  change ev tr t r pub (Expr.add (Expr.add (Rs.paritySum i k) (Expr.neg (Rs.T.c "r" (8 * i + k))))
    (Expr.neg (Expr.mul (Expr.const 2) (Rs.T.c "q" (8 * i + k))))) = 0 at h
  simp only [ev_add, ev_neg, ev_mul, ev_const] at h
  omega

end

end FinalM5d.RsRow
