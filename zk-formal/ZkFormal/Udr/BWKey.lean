import ZkFormal.Udr.BWLin
import ZkFormal.Udr.RS

/-!
# ZkFormal.Udr.BWKey — the Berlekamp–Welch key equation for a line

For words `a, b` on `n` distinct points and `e ≤ n`, there are a nonzero
bivariate `E(X, Z)` (degrees `≤ e` in both) and `N(X, Z)` (`X`-length
`n - e`, `Z`-length `e + 2`) with `N(xᵢ, z) = (aᵢ + z·bᵢ)·E(xᵢ, z)` for
every position `i` and every `z`.  Proof: `(e+1)² + (n-e)(e+2)` unknowns,
`n(e+2)` homogeneous linear equations (coefficients of `Zʲ`).
-/

namespace ZkFormal.Udr

open ArenaCore.Security
open Lean.Grind

set_option linter.unusedSectionVars false

/-! ## Grids of indices -/

section grid
variable {β : Type}

/-- `[g k j | k < p, j < q]`. -/
def grid (p q : Nat) (g : Nat → Nat → β) : List β :=
  (List.range p).flatMap fun k => (List.range q).map (g k)

theorem length_grid (p q : Nat) (g : Nat → Nat → β) : (grid p q g).length = p * q := by
  simp only [grid, List.length_flatMap, List.length_map, List.length_range]
  rw [sum_map_const, List.length_range]

theorem mem_grid {p q : Nat} {g : Nat → Nat → β} {x : β} :
    x ∈ grid p q g ↔ ∃ k j, k < p ∧ j < q ∧ g k j = x := by
  simp only [grid, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, j, hj, rfl⟩; exact ⟨k, j, hk, hj, rfl⟩
  · rintro ⟨k, j, hk, hj, rfl⟩; exact ⟨k, hk, j, hj, rfl⟩

theorem nodup_map_range {q : Nat} {f : Nat → β} (hf : ∀ j j', f j = f j' → j = j') :
    ((List.range q).map f).Nodup := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [List.range_succ, List.map_append, List.nodup_append]
    refine ⟨ih, by simp, fun a ha b hb hab => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
    subst hb
    have := hf _ _ hab
    simp only [List.mem_range] at hj; omega

theorem nodup_grid {p q : Nat} {g : Nat → Nat → β}
    (hg : ∀ k j k' j', g k j = g k' j' → k = k' ∧ j = j') : (grid p q g).Nodup := by
  induction p with
  | zero => simp [grid]
  | succ p ih =>
    simp only [grid] at ih ⊢
    rw [List.range_succ, List.flatMap_append, List.nodup_append]
    refine ⟨ih, by simpa using nodup_map_range fun j j' h => (hg _ _ _ _ h).2, fun a ha b hb hab => ?_⟩
    obtain ⟨k, hk, j, _, rfl⟩ := by simpa only [List.mem_flatMap, List.mem_map] using ha
    obtain ⟨j', _, rfl⟩ := by simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_map] using hb
    have := (hg _ _ _ _ hab).1
    simp only [List.mem_range] at hk; omega

end grid

variable {K : Type} [Field K]

theorem ev_add_smul (m : Nat) (c c' : Nat → K) (t x : K) :
    ev m (fun k => c k + t * c' k) x = ev m c x + t * ev m c' x := by
  have := ev_lin m 1 t c c' x
  rw [show (fun k => (1 : K) * c k + t * c' k) = fun k => c k + t * c' k by funext; grind] at this
  rw [this]; grind

/-! ## The linear system -/

/-- Unknowns: `(false, k, j)` is the `XᵏZʲ` coefficient of `E`, `(true, k, j)` that of `N`. -/
abbrev BWIdx := Bool × Nat × Nat

/-- `Σₖ y(false, k, j) xᵏ` (the `Zʲ`-coefficient of `E` at `x`). -/
def eCol (e : Nat) (y : BWIdx → K) (j : Nat) (x : K) : K := ev (e + 1) (fun k => y (false, k, j)) x

/-- Coefficient `j - 1` of `E` (zero for `j = 0`). -/
def eColPrev (e : Nat) (y : BWIdx → K) : Nat → K → K
  | 0, _ => 0
  | j + 1, x => eCol e y j x

/-- The `Zʲ`-coefficient of `N(xᵢ, Z) - (aᵢ + Z bᵢ) E(xᵢ, Z)`. -/
def bwEq (xs : Nat → K) (n e : Nat) (a b : Nat → K) (i j : Nat) (y : BWIdx → K) : K :=
  ev (n - e) (fun k => y (true, k, j)) (xs i) - a i * eCol e y j (xs i) - b i * eColPrev e y j (xs i)

theorem bwEq_lin (xs : Nat → K) (n e : Nat) (a b : Nat → K) (i j : Nat) :
    LinF (bwEq xs n e a b i j) := by
  intro y y' c
  have h1 : ∀ j x, eCol e (fun t => y t + c * y' t) j x = eCol e y j x + c * eCol e y' j x :=
    fun j x => ev_add_smul _ _ _ _ _
  have h2 : ∀ j x, eColPrev e (fun t => y t + c * y' t) j x =
      eColPrev e y j x + c * eColPrev e y' j x := by
    intro j x; cases j with
    | zero => simp only [eColPrev]; grind
    | succ j => exact h1 j x
  simp only [bwEq]
  rw [h1, h2, ev_add_smul]; grind

/-- **Key equation.** -/
theorem bw_key (xs : Nat → K) (n e : Nat) (he : e ≤ n) (hxs : Distinct xs n) (a b : Nat → K) :
    ∃ E N : Nat → Nat → K, (∃ k j, k ≤ e ∧ j ≤ e ∧ E k j ≠ 0) ∧
      ∀ i, i < n → ∀ z : K,
        ev (n - e) (fun k => ev (e + 2) (N k) z) (xs i) =
          (a i + z * b i) * ev (e + 1) (fun k => ev (e + 1) (E k) z) (xs i) := by
  classical
  let LE : List BWIdx := grid (e + 1) (e + 1) fun k j => (false, k, j)
  let LN : List BWIdx := grid (n - e) (e + 2) fun k j => (true, k, j)
  let fs := grid n (e + 2) fun i j => bwEq xs n e a b i j
  have hnd : (LE ++ LN).Nodup := by
    rw [List.nodup_append]
    refine ⟨nodup_grid fun _ _ _ _ h => by simp_all, nodup_grid fun _ _ _ _ h => by simp_all,
      fun x hx x' hx' h => ?_⟩
    obtain ⟨_, _, _, _, rfl⟩ := mem_grid.mp hx
    obtain ⟨_, _, _, _, rfl⟩ := mem_grid.mp hx'
    simp at h
  have hlen : fs.length < (LE ++ LN).length := by
    rw [List.length_append, length_grid, length_grid, length_grid]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + e := ⟨n - e, by omega⟩
    rw [Nat.add_sub_cancel]
    grind
  have hlin : ∀ f ∈ fs, LinF f := by
    intro f hf
    obtain ⟨i, j, _, _, rfl⟩ := mem_grid.mp hf
    exact bwEq_lin _ _ _ _ _ _ _
  obtain ⟨y, hsupp, ⟨a0, ha0, hya0⟩, hsol⟩ := exists_nonzero_sol _ hnd fs hlin hlen
  have heq : ∀ i j, i < n → j < e + 2 → bwEq xs n e a b i j y = 0 :=
    fun i j hi hj => hsol _ (mem_grid.mpr ⟨i, j, hi, hj, rfl⟩)
  have hEz : ∀ k j, e < j → y (false, k, j) = 0 := by
    intro k j hj
    refine hsupp _ fun hm => ?_
    rcases List.mem_append.mp hm with h | h
    · obtain ⟨_, _, _, _, h⟩ := mem_grid.mp h; simp at h; omega
    · obtain ⟨_, _, _, _, h⟩ := mem_grid.mp h; simp at h
  refine ⟨fun k j => y (false, k, j), fun k j => y (true, k, j), ?_, ?_⟩
  · -- `E ≠ 0`
    refine Classical.byContradiction fun hE0 => ?_
    have hE : ∀ k j, y (false, k, j) = 0 := by
      intro k j
      by_cases hj : j ≤ e
      · by_cases hk : k ≤ e
        · exact Classical.byContradiction fun h => hE0 ⟨k, j, hk, hj, h⟩
        · refine hsupp _ fun hm => ?_
          rcases List.mem_append.mp hm with h | h
          · obtain ⟨_, _, _, _, h⟩ := mem_grid.mp h; simp at h; omega
          · obtain ⟨_, _, _, _, h⟩ := mem_grid.mp h; simp at h
      · exact hEz k j (by omega)
    have hcol : ∀ j x, eCol e y j x = 0 := fun j x => ev_eq_zero (fun k _ => hE k j) x
    have hprev : ∀ j x, eColPrev e y j x = 0 := fun j x => by
      cases j with
      | zero => rfl
      | succ j => exact hcol j x
    rcases List.mem_append.mp ha0 with h | h
    · obtain ⟨k, j, _, _, rfl⟩ := mem_grid.mp h
      exact hya0 (hE k j)
    · obtain ⟨k, j, hk, hj, rfl⟩ := mem_grid.mp h
      refine hya0 (coeffs_zero_of_roots (n - e) (fun k => y (true, k, j)) ((List.range n).map xs)
        (hxs.map_nodup List.nodup_range fun i hi => List.mem_range.mp hi)
        (by rw [List.length_map, List.length_range]; omega) (fun r hr => ?_) k hk)
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
      have := heq i j (List.mem_range.mp hi) hj
      simp only [bwEq, hcol, hprev] at this
      grind
  · intro i hi z
    rw [ev_swap, ev_swap (e + 1) (e + 1)]
    have hN : ∀ j, j < e + 2 → ev (n - e) (fun k => y (true, k, j)) (xs i) =
        a i * eCol e y j (xs i) + b i * eColPrev e y j (xs i) := by
      intro j hj
      have := heq i j hi hj
      simp only [bwEq] at this
      grind
    rw [ev_congr hN, ev_lin, ev_succ (e + 1) (fun j => eColPrev e y j (xs i))]
    rw [ev_pad (m := e + 1) (by omega) (fun k h1 h2 => by
      rw [show k = e + 1 by omega]; exact ev_eq_zero (fun k _ => hEz k (e + 1) (by omega)) _)]
    simp only [eColPrev, eCol]
    grind

end ZkFormal.Udr
