import StateM5a.FieldRows
import StateM5a.Layout

/-!
# StateM5a.FieldRows2 — the `SN` key / `hexPrefix` layout from the table's constraints

`sn_key_layout`: on a short-key `SN` row (`act = 1`, `cont = 0`) whose key nibbles are `< 16`
(from the `NIB` / `RNG` lookups), the constraints over BabyBear force

* the prefix flags `a_j = [j < klen]` (`klen ≤ 64`), the key cells past `klen` are `0`;
* `odd = klen mod 2`, `ha_m = [m < 1 + klen/2]`, `hplen = 1 + klen/2`;
* every `hp_m` (`m < 33`) is `Layout.hpAt key leaf m`, `key = [k_0 … k_{klen−1}]`, `leaf = isL`.

`br_sel`: on a descending `BR` row (`act = 1`, `oFV = 0`, `gdn = 1`) exactly one selector
`sel_i` is set, slot `i` is present (`f_i = 1`) and the looked-up nibble `nib = Σ i·sel_i` is `i`.

With `Layout.hexPrefix_eq` this is `sn_hexPrefix`: the bytes the row sends at serialization
offsets `5 … 4 + hplen` are exactly `hexPrefix key leaf` (`PTrie.hashOf`'s key bytes) and
`hplen` is its length.  Membership of each constraint is found by `mem_search` (robust to
constraints being added to the table).
-/

namespace StateM5a.FieldRows2

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.FieldRows

variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

local notation "P" => 2013265921

/-- Find `e ∈ L` in a constraint list built from `++`, `flatMap` over `List.range` and literals. -/
syntax "mem_search" term:max term:max : tactic
macro_rules
  | `(tactic| mem_search $j $hj) => `(tactic| first
      | exact Or.inl rfl
      | exact rfl
      | (refine ⟨$j, $hj, ?_⟩; simp [*]; done)
      | (apply Or.inr; mem_search $j $hj)
      | (apply Or.inl; mem_search $j $hj))

/-! ## Nat combinatorics -/

/-- A monotone 0/1 sequence (`f (j+1) = 1 → f j = 1`) is the indicator of `[0, Σ f)`. -/
theorem prefix_flags (f : Nat → Nat) : ∀ n, (∀ j, j < n → f j ≤ 1) →
    (∀ j, j + 1 < n → f (j + 1) = 1 → f j = 1) →
    ((List.range n).map f).sum ≤ n ∧ ∀ j, j < n → f j = if j < ((List.range n).map f).sum then 1 else 0
  | 0, _, _ => by simp
  | n + 1, hb, hm => by
    obtain ⟨hS, hf⟩ := prefix_flags f n (fun j hj => hb j (by omega)) (fun j hj => hm j (by omega))
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    generalize hSd : ((List.range n).map f).sum = S at hS hf
    have hn := hb n (by omega)
    rcases Nat.lt_or_ge (f n) 1 with h0 | h1
    · have : f n = 0 := by omega
      rw [this]
      refine ⟨by omega, fun j hj => ?_⟩
      rcases Nat.lt_or_ge j n with hj' | hj'
      · rw [hf j hj']; simp
      · have : j = n := by omega
        subst this; simp [‹f j = 0›]; omega
    · have h1' : f n = 1 := by omega
      have hSn : S = n := by
        rcases Nat.eq_zero_or_pos n with hz | hz
        · omega
        · have := hf (n - 1) (by omega)
          rw [hm (n - 1) (by omega) (by rw [show n - 1 + 1 = n by omega]; exact h1')] at this
          split at this <;> omega
      subst hSn
      rw [h1']
      refine ⟨by omega, fun j hj => ?_⟩
      rcases Nat.lt_or_ge j S with hj' | hj'
      · rw [hf j hj']; simp [hj']; omega
      · have : j = S := by omega
        subst this; simp [h1']

theorem sum_ind (c : Nat) : ∀ n, ((List.range n).map fun m => if m < c then 1 else 0).sum = min c n
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_ind c n]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    split <;> omega

theorem sum_ind_le (c n : Nat) (h : c ≤ n) :
    ((List.range n).map fun m => if m < c then 1 else 0).sum = c := by
  rw [sum_ind]; exact Nat.min_eq_left h

/-- `2·H ≡ 2·S (mod P)` with `P` odd, `H < P`, `2S < P`: `H = S`.  (Stated for a variable `P` so
that no tactic evaluates `% 2013265921`.) -/
theorem half_eq (Q H S : Nat) (hP : Q % 2 = 1) (hP3 : 2 < Q) (hh : H < Q) (hs : 2 * S < Q)
    (h2 : 2 % Q * H % Q = 2 % Q * (S % Q) % Q) : H = S := by
  rw [Nat.mod_eq_of_lt hP3, Nat.mod_eq_of_lt (show S < Q by omega), Nat.mod_eq_of_lt hs] at h2
  rcases Nat.lt_or_ge (2 * H) Q with hl | hl
  · rw [Nat.mod_eq_of_lt hl] at h2; omega
  · rw [Nat.mod_eq_sub_mod hl] at h2
    have hlt : 2 * H - Q < Q := by omega
    rw [Nat.mod_eq_of_lt hlt] at h2
    have : Q = 2 * (Q / 2) + 1 := by omega
    omega

theorem sum_odd : ∀ L, L < 65 →
    ((List.range 32).map fun m => if L = 2 * m + 1 then 1 else 0).sum = L % 2 := by
  decide

/-! ## Field helpers -/

theorem ev_one_sub0 {x : Expr} (h : ev tr t r pub x = 0) : ev tr t r pub (1 - x) = 1 := by
  rw [ev_sub, h]; simp

theorem ev_bool {x : Expr} (h : ev tr t r pub (bool x) = 0) :
    ev tr t r pub x = 0 ∨ ev tr t r pub x = 1 := by
  have := bool_le h; omega

theorem sn_a_lt (j : Nat) (hj : j < 64) : Sn.a j = Sn.c "a" j := by simp [Sn.a, KMAX, hj]
theorem sn_k_lt (j : Nat) (hj : j < 64) : Sn.k j = Sn.c "k" j := by simp [Sn.k, KMAX, hj]
theorem sn_a_ge (j : Nat) (hj : 64 ≤ j) : Sn.a j = Expr.const 0 := by
  simp [Sn.a, KMAX, Nat.not_lt.2 hj]; rfl
theorem sn_k_ge (j : Nat) (hj : 64 ≤ j) : Sn.k j = Expr.const 0 := by
  simp [Sn.k, KMAX, Nat.not_lt.2 hj]; rfl

@[simp] theorem ev_ofNat (n : Nat) : ev tr t r pub (no_index (OfNat.ofNat n : Expr)) = n % P := ev_const n

/-! ## `SN` key layout -/

section
variable (hc : ∀ e ∈ Sn.table.constraints, e.eval tr t r pub = 0)
include hc

theorem sn_hold {e : Expr} (he : e ∈ Sn.constraints) : ev tr t r pub e = 0 := hold rfl hc he

theorem sn_a_bool (j : Nat) (hj : j < 64) : ev tr t r pub (Sn.c "a" j) ≤ 1 := by
  have := sn_hold hc (e := bool (Sn.a j)) (by
    unfold Sn.constraints
    simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
    mem_search j hj)
  rw [sn_a_lt j hj] at this
  exact bool_le this

theorem sn_a_mono (j : Nat) (hj : j + 1 < 64) (h1 : ev tr t r pub (Sn.c "a" (j + 1)) = 1) :
    ev tr t r pub (Sn.c "a" j) = 1 := by
  have := sn_hold hc (e := Sn.a (j + 1) * (1 - Sn.a j)) (by
    have hj' : j < 64 := by omega
    unfold Sn.constraints
    simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
    mem_search j hj')
  rw [sn_a_lt j (by omega), sn_a_lt (j + 1) hj] at this
  change ev tr t r pub (Expr.mul _ _) = 0 at this
  rw [ev_mul_gate _ h1, ev_sub] at this
  have hb := sn_a_bool hc j (by omega)
  simp at this; omega

theorem sn_k_zero (j : Nat) (hj : j < 64) (h0 : ev tr t r pub (Sn.c "a" j) = 0) :
    ev tr t r pub (Sn.c "k" j) = 0 := by
  have := sn_hold hc (e := (1 - Sn.a j) * Sn.k j) (by
    unfold Sn.constraints
    simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
    mem_search j hj)
  rw [sn_a_lt j hj, sn_k_lt j hj] at this
  change ev tr t r pub (Expr.mul _ _) = 0 at this
  rwa [ev_mul_gate _ (ev_one_sub0 h0)] at this

theorem sn_rl (hcont : ev tr t r pub (Sn.c "cont") = 0) : ev tr t r pub (Sn.c "rl") = 0 := by
  have := sn_hold hc (e := (1 - Sn.c "cont") * Sn.c "rl") (by
    unfold Sn.constraints; simp)
  change ev tr t r pub (Expr.mul _ _) = 0 at this
  rwa [ev_mul_gate _ (ev_one_sub0 hcont)] at this

omit hc in
/-- `Σ_{j<n} ev (Sn.a j)` without wrap. -/
theorem sum_a_eq (n : Nat) (hn : n ≤ 64) :
    ((List.range n).map fun j => ev tr t r pub (Sn.a j)).sum =
      ((List.range n).map fun j => ev tr t r pub (Sn.c "a" j)).sum := by
  congr 1
  apply List.map_congr_left
  intro j hj
  rw [sn_a_lt j (by simp at hj; omega)]

theorem sn_klen (hcont : ev tr t r pub (Sn.c "cont") = 0) :
    ev tr t r pub (Sn.c "klen") = ((List.range 64).map fun j => ev tr t r pub (Sn.c "a" j)).sum := by
  have h := sn_hold hc (e := Sn.c "klen" - sumE ((List.range KMAX).map Sn.a) - Sn.c "rl") (by
    unfold Sn.constraints; simp)
  have h1 := eq_of_sub h
  rw [sn_rl hc hcont] at h1
  have h2 := eq_of_sub h1
  rw [h2, ev_sumE, List.map_map]
  have hs : ((List.range 64).map fun j => ev tr t r pub (Sn.c "a" j)).sum ≤ 64 := by
    have := sum_le_length ((List.range 64).map fun j => ev tr t r pub (Sn.c "a" j))
      (by intro x hx; simp only [List.mem_map, List.mem_range] at hx
          obtain ⟨j, hj, rfl⟩ := hx; exact sn_a_bool hc j hj)
    simpa using this
  have := sum_a_eq (tr := tr) (t := t) (r := r) (pub := pub) 64 (Nat.le_refl _)
  simp only [Function.comp_def, KMAX] at this ⊢
  rw [this]
  exact Nat.mod_eq_of_lt (by omega)

/-- **Prefix flags**: `a_j = [j < klen]`, `klen ≤ 64`. -/
theorem sn_flags (hcont : ev tr t r pub (Sn.c "cont") = 0) :
    ev tr t r pub (Sn.c "klen") ≤ 64 ∧ ∀ j, j < 64 →
      ev tr t r pub (Sn.c "a" j) = if j < ev tr t r pub (Sn.c "klen") then 1 else 0 := by
  rw [sn_klen hc hcont]
  exact prefix_flags (fun j => ev tr t r pub (Sn.c "a" j)) 64 (fun j hj => sn_a_bool hc j hj)
    (fun j hj h1 => sn_a_mono hc j hj h1)

/-- `odd = klen mod 2`. -/
theorem sn_odd (hcont : ev tr t r pub (Sn.c "cont") = 0) :
    ev tr t r pub (Sn.c "odd") = ev tr t r pub (Sn.c "klen") % 2 := by
  obtain ⟨hL, hf⟩ := sn_flags hc hcont
  have h := sn_hold hc (e := Sn.c "odd" -
      sumE ((List.range (KMAX / 2)).map fun m => Sn.a (2 * m) - Sn.a (2 * m + 1))) (by
    unfold Sn.constraints; simp)
  rw [eq_of_sub h, ev_sumE, List.map_map]
  generalize hLd : ev tr t r pub (Sn.c "klen") = L at hL hf
  have e : ((List.range (KMAX / 2)).map
      (ev tr t r pub ∘ fun m => Sn.a (2 * m) - Sn.a (2 * m + 1))) =
      (List.range 32).map fun m => if L = 2 * m + 1 then 1 else 0 := by
    simp only [KMAX, Nat.reduceDiv]
    apply List.map_congr_left
    intro m hm
    simp only [List.mem_range] at hm
    simp only [Function.comp, sn_a_lt (2 * m) (by omega), sn_a_lt (2 * m + 1) (by omega), ev_sub,
      hf (2 * m) (by omega), hf (2 * m + 1) (by omega)]
    by_cases h1 : 2 * m < L <;> by_cases h2 : 2 * m + 1 < L <;> simp [h1, h2] <;> omega
  rw [e, sum_odd L (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

theorem sn_bool (s : String) (hs : s ∈ ["isL", "odd", "cont"]) :
    ev tr t r pub (Sn.c s) ≤ 1 := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl <;>
  · apply bool_le
    apply sn_hold hc
    unfold Sn.constraints; simp [Sn.ops]

/-- `ha_m = [m < 1 + klen/2]`. -/
theorem sn_ha (hA : ev tr t r pub (Sn.c "act") = 1) (hcont : ev tr t r pub (Sn.c "cont") = 0)
    (m : Nat) (hm : m < 33) :
    ev tr t r pub (Sn.c "ha" m) = if m < 1 + ev tr t r pub (Sn.c "klen") / 2 then 1 else 0 := by
  obtain ⟨hL, hf⟩ := sn_flags hc hcont
  have ho := sn_odd hc hcont
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · have h := sn_hold hc (e := Sn.c "ha" 0 - Sn.c "act") (by unfold Sn.constraints; simp)
    rw [eq_of_sub h, hA]; simp
  · have h0 : m ≠ 0 := by omega
    have h := sn_hold hc (e := Sn.c "ha" m - Sn.c "odd" * Sn.a (2 * m) -
        (1 - Sn.c "odd") * Sn.a (2 * m - 1)) (by
      unfold Sn.constraints
      simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
      mem_search m hm)
    have h' := eq_of_sub h
    have ea : ev tr t r pub (Sn.a (2 * m)) = if 2 * m < ev tr t r pub (Sn.c "klen") then 1 else 0 := by
      rcases Nat.lt_or_ge (2 * m) 64 with hl | hl
      · rw [sn_a_lt _ hl, hf _ hl]
      · rw [sn_a_ge _ hl]; simp; omega
    have eb : ev tr t r pub (Sn.a (2 * m - 1)) =
        if 2 * m - 1 < ev tr t r pub (Sn.c "klen") then 1 else 0 := by
      rw [sn_a_lt _ (by omega), hf _ (by omega)]
    simp only [ev_sub, ev_hmul, ev_one, ea, eb, ho] at h'
    have hha := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) (Sn.c "ha" m)
    generalize ev tr t r pub (Sn.c "ha" m) = H at h' hha ⊢
    generalize ev tr t r pub (Sn.c "klen") = L at h' hL ⊢
    rcases Nat.mod_two_eq_zero_or_one L with hp | hp <;> rw [hp] at h' <;>
      by_cases h1 : 2 * m < L <;> by_cases h2 : 2 * m - 1 < L <;> simp [h1, h2] at h' <;>
      split <;> omega

/-- `hplen = 1 + klen/2`. -/
theorem sn_hplen (hA : ev tr t r pub (Sn.c "act") = 1) (hcont : ev tr t r pub (Sn.c "cont") = 0) :
    ev tr t r pub (Sn.c "hplen") = 1 + ev tr t r pub (Sn.c "klen") / 2 := by
  obtain ⟨hL, -⟩ := sn_flags hc hcont
  have h := sn_hold hc (e := sm 2 (Sn.c "hplen") -
      sm 2 (sumE ((List.range HPMAX).map fun m => Sn.c "ha" m)) - Sn.c "rl") (by
    unfold Sn.constraints; simp)
  have h1 := eq_of_sub h
  rw [sn_rl hc hcont] at h1
  have h2 := eq_of_sub h1
  have hs : ((List.range HPMAX).map fun m => ev tr t r pub (Sn.c "ha" m)) =
      (List.range 33).map fun m => if m < 1 + ev tr t r pub (Sn.c "klen") / 2 then 1 else 0 := by
    simp only [HPMAX]
    apply List.map_congr_left
    intro m hm; simp only [List.mem_range] at hm
    exact sn_ha hc hA hcont m hm
  have hc2 : 2 * (1 + ev tr t r pub (Sn.c "klen") / 2) < P := by omega
  have hc3 : 1 + ev tr t r pub (Sn.c "klen") / 2 ≤ 33 := by omega
  simp only [sm, ev_mul, ev_const, ev_sumE, List.map_map, Function.comp_def] at h2
  rw [hs, sum_ind_le _ _ hc3] at h2
  exact half_eq P _ _ (by decide) (by decide) (ev_lt _) hc2 h2

/-- The row's key as a nibble list. -/
def keyOf (tr : Trace Fp) (t r : Nat) (pub : List Fp) : List Nat :=
  (List.range (ev tr t r pub (Sn.c "klen"))).map fun j => ev tr t r pub (Sn.c "k" j)

theorem keyOf_getD (hcont : ev tr t r pub (Sn.c "cont") = 0) (j : Nat) :
    (keyOf tr t r pub).getD j 0 = ev tr t r pub (Sn.k j) := by
  obtain ⟨hL, hf⟩ := sn_flags hc hcont
  unfold keyOf
  rcases Nat.lt_or_ge j (ev tr t r pub (Sn.c "klen")) with h1 | h1
  · rw [sn_k_lt j (by omega)]
    simp [List.getD_eq_getElem?_getD, h1]
  · have hg : ((List.range (ev tr t r pub (Sn.c "klen"))).map fun j => ev tr t r pub (Sn.c "k" j)).getD j 0
        = 0 := by
      simp [List.getD_eq_getElem?_getD, Nat.not_lt.2 h1]
    rw [hg]
    rcases Nat.lt_or_ge j 64 with h2 | h2
    · rw [sn_k_lt j h2]
      exact (sn_k_zero hc j h2 (by rw [hf j h2]; simp; omega)).symm
    · rw [sn_k_ge j h2]; simp

/-- **`hp` bytes**: `hp_m = hpAt key isL m` for every `m < 33`. -/
theorem sn_hp (hcont : ev tr t r pub (Sn.c "cont") = 0)
    (hk : ∀ j, j < 64 → ev tr t r pub (Sn.c "k" j) < 16) (m : Nat) (hm : m < 33) :
    ev tr t r pub (Sn.c "hp" m) =
      Layout.hpAt (keyOf tr t r pub) (decide (ev tr t r pub (Sn.c "isL") = 1)) m := by
  obtain ⟨hL, -⟩ := sn_flags hc hcont
  have ho := sn_odd hc hcont
  have hisL := sn_bool hc "isL" (by simp)
  have kb : ∀ j, ev tr t r pub (Sn.k j) < 16 := by
    intro j
    rcases Nat.lt_or_ge j 64 with h | h
    · rw [sn_k_lt j h]; exact hk j h
    · rw [sn_k_ge j h]; simp
  have hlen : (keyOf tr t r pub).length = ev tr t r pub (Sn.c "klen") := by simp [keyOf]
  simp only [Layout.hpAt, hlen, keyOf_getD hc hcont]
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · have h := sn_hold hc (e := Sn.c "hp" 0 - (sm 32 (Sn.c "isL") + Sn.c "odd" * (16 + Sn.k 0))) (by
      unfold Sn.constraints; simp)
    rw [eq_of_sub h]
    simp only [sm, ev_hadd, ev_hmul, ev_mul, ev_const, ev_ofNat, ho, ite_true]
    have k0 := kb 0
    generalize ev tr t r pub (Sn.k 0) = x at k0 ⊢
    generalize ev tr t r pub (Sn.c "klen") = L
    rcases Nat.mod_two_eq_zero_or_one L with hp | hp <;> rw [hp] <;>
      by_cases hi : ev tr t r pub (Sn.c "isL") = 1 <;> simp [hi] <;> omega
  · have h0 : m ≠ 0 := by omega
    have h := sn_hold hc (e := Sn.c "hp" m - Sn.c "odd" * (sm 16 (Sn.k (2 * m - 1)) + Sn.k (2 * m)) -
        (1 - Sn.c "odd") * (sm 16 (Sn.k (2 * m - 2)) + Sn.k (2 * m - 1))) (by
      unfold Sn.constraints
      simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
      mem_search m hm)
    have h' := eq_of_sub h
    simp only [h0, ite_false]
    simp only [sm, ev_sub, ev_hadd, ev_hmul, ev_mul, ev_const, ev_one, ho] at h'
    have k1 := kb (2 * m - 1); have k2 := kb (2 * m); have k3 := kb (2 * m - 2)
    have hh := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) (Sn.c "hp" m)
    generalize ev tr t r pub (Sn.k (2 * m - 1)) = x1 at k1 h' ⊢
    generalize ev tr t r pub (Sn.k (2 * m)) = x2 at k2 h' ⊢
    generalize ev tr t r pub (Sn.k (2 * m - 2)) = x3 at k3 h' ⊢
    generalize ev tr t r pub (Sn.c "hp" m) = H at h' hh ⊢
    generalize ev tr t r pub (Sn.c "klen") = L at h' ⊢
    rcases Nat.mod_two_eq_zero_or_one L with hp | hp <;> rw [hp] at h' ⊢ <;> simp at h' ⊢ <;> omega

/-- **The row's key bytes are `hexPrefix`**: on a short-key `SN` row with nibbles `< 16`, the bytes
`hp_0 … hp_{hplen−1}` the row sends are `hexPrefix key leaf` (`leaf = isL`), `key` the row's
`klen` nibbles. -/
theorem sn_hexPrefix (hA : ev tr t r pub (Sn.c "act") = 1) (hcont : ev tr t r pub (Sn.c "cont") = 0)
    (hk : ∀ j, j < 64 → ev tr t r pub (Sn.c "k" j) < 16) :
    (NearSpec.hexPrefix (keyOf tr t r pub) (decide (ev tr t r pub (Sn.c "isL") = 1))).map UInt8.toNat =
      (List.range (ev tr t r pub (Sn.c "hplen"))).map fun m => ev tr t r pub (Sn.c "hp" m) := by
  obtain ⟨hL, -⟩ := sn_flags hc hcont
  have hn : ∀ x ∈ keyOf tr t r pub, x < 16 := by
    intro x hx
    simp only [keyOf, List.mem_map, List.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    exact hk j (by omega)
  have hlen : (keyOf tr t r pub).length = ev tr t r pub (Sn.c "klen") := by simp [keyOf]
  rw [Layout.hexPrefix_eq _ _ hn, hlen, sn_hplen hc hA hcont]
  apply List.map_congr_left
  intro m hm; simp only [List.mem_range] at hm
  exact (sn_hp hc hcont hk m (by omega)).symm

end

/-! ## `BR`: the selected slot -/

/-- 0/1 values summing to 1 on `[0, n)`: a unique index carries the 1. -/
theorem sum_one (g : Nat → Nat) : ∀ n, (∀ j, j < n → g j ≤ 1) → ((List.range n).map g).sum = 1 →
    ∃ i, i < n ∧ g i = 1 ∧ ∀ j, j < n → j ≠ i → g j = 0
  | 0, _, h => by simp at h
  | n + 1, hb, h => by
    rw [List.range_succ, List.map_append, List.sum_append] at h
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
    have hn := hb n (by omega)
    rcases Nat.lt_or_ge (g n) 1 with h0 | h1
    · obtain ⟨i, hi, hg, hu⟩ := sum_one g n (fun j hj => hb j (by omega)) (by omega)
      refine ⟨i, by omega, hg, fun j hj hji => ?_⟩
      rcases Nat.lt_or_ge j n with hj' | hj'
      · exact hu j hj' hji
      · have : j = n := by omega
        subst this; omega
    · have hz : ((List.range n).map g).sum = 0 := by omega
      refine ⟨n, by omega, by omega, fun j hj hjn => ?_⟩
      have hm : g j ∈ (List.range n).map g := List.mem_map.2 ⟨j, List.mem_range.2 (by omega), rfl⟩
      have := le_sum_of_mem' hm
      omega

theorem sum_zero (F : Nat → Nat) : ∀ n, (∀ j, j < n → F j = 0) → ((List.range n).map F).sum = 0
  | 0, _ => by simp
  | n + 1, hz => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_zero F n (fun j hj => hz j (by omega))]
    simp [hz n (by omega)]

/-- A sum over `[0, n)` that vanishes off `i` is its value at `i`. -/
theorem sum_single (F : Nat → Nat) (i : Nat) : ∀ n, i < n → (∀ j, j < n → j ≠ i → F j = 0) →
    ((List.range n).map F).sum = F i
  | 0, h, _ => by omega
  | n + 1, hi, hz => by
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rcases Nat.lt_or_ge i n with h | h
    · rw [sum_single F i n h (fun j hj hji => hz j (by omega) hji), hz n (by omega) (by omega),
        Nat.add_zero]
    · have : i = n := by omega
      subst this
      rw [sum_zero F i (fun j hj => hz j (by omega) (by omega))]
      omega

section
variable (hc : ∀ e ∈ Br.table.constraints, e.eval tr t r pub = 0)
include hc

theorem br_hold {e : Expr} (he : e ∈ Br.constraints) : ev tr t r pub e = 0 := hold rfl hc he

theorem br_bool_sel (i : Nat) (hi : i < 16) : ev tr t r pub (Br.c "sel" i) ≤ 1 := by
  apply bool_le; apply br_hold hc
  unfold Br.constraints
  simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
  mem_search i hi

theorem br_bool_f (i : Nat) (hi : i < 16) : ev tr t r pub (Br.c "f" i) ≤ 1 := by
  apply bool_le; apply br_hold hc
  unfold Br.constraints
  simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
  mem_search i hi

/-- **`BR` selected slot**: on a descending row (`act = 1`, `oFV = 0`, `gdn = 1`) exactly one
selector `sel_i` is `1`, slot `i` is present (`f_i = 1`), and the nibble the row looks up against
the walk key (`nib = Σ i·sel_i`) is `i`: the row descends into child `Kids.at cs i`. -/
theorem br_sel (hA : ev tr t r pub (Br.c "act") = 1) (hv : ev tr t r pub (Br.c "oFV") = 0)
    (hg : ev tr t r pub (Br.c "gdn") = 1) :
    ∃ i, i < 16 ∧ ev tr t r pub (Br.c "sel" i) = 1 ∧
      (∀ j, j < 16 → j ≠ i → ev tr t r pub (Br.c "sel" j) = 0) ∧
      ev tr t r pub (Br.c "f" i) = 1 ∧ ev tr t r pub Br.nib = i := by
  have bs := br_bool_sel hc
  have bf := br_bool_f hc
  -- Σ sel = 1
  have h1 := br_hold hc (e := sumE ((List.range 16).map fun i => Br.c "sel" i) -
      (Br.c "act" - Br.c "oFV")) (by unfold Br.constraints; simp)
  have h1' := eq_of_sub h1
  rw [ev_sumE, List.map_map] at h1'
  have hs16 : ((List.range 16).map fun i => ev tr t r pub (Br.c "sel" i)).sum ≤ 16 := by
    have := sum_le_length ((List.range 16).map fun i => ev tr t r pub (Br.c "sel" i))
      (by intro x hx; simp only [List.mem_map, List.mem_range] at hx
          obtain ⟨j, hj, rfl⟩ := hx; exact bs j hj)
    simpa using this
  have hsum : ((List.range 16).map fun i => ev tr t r pub (Br.c "sel" i)).sum = 1 := by
    have e : ev tr t r pub (Br.c "act" - Br.c "oFV") = 1 := by rw [ev_sub, hA, hv]; try simp
    rw [e, Function.comp_def, Nat.mod_eq_of_lt (by omega)] at h1'
    exact h1'
  obtain ⟨i, hi, h1i, hu⟩ := sum_one (fun j => ev tr t r pub (Br.c "sel" j)) 16 bs hsum
  refine ⟨i, hi, h1i, hu, ?_, ?_⟩
  · -- Σ sel·f = gdn = 1
    have h2 := br_hold hc (e := sumE ((List.range 16).map fun i => Br.c "sel" i * Br.c "f" i) -
        Br.c "gdn") (by unfold Br.constraints; simp)
    have h2' := eq_of_sub h2
    rw [ev_sumE, List.map_map, hg] at h2'
    have hF : ((List.range 16).map (ev tr t r pub ∘ fun i => Br.c "sel" i * Br.c "f" i)).sum =
        ev tr t r pub (Br.c "f" i) := by
      rw [sum_single _ i 16 hi (fun j hj hji => by
        simp only [Function.comp, ev_hmul, hu j hj hji, Nat.zero_mul, Nat.zero_mod])]
      simp only [Function.comp, ev_hmul, h1i, Nat.one_mul]
      exact Nat.mod_eq_of_lt (ev_lt _)
    rw [hF, Nat.mod_eq_of_lt (ev_lt _)] at h2'
    exact h2'
  · unfold Br.nib
    rw [ev_sumE, List.map_map]
    have hN : ((List.range 16).map (ev tr t r pub ∘ fun i => sm i (Br.c "sel" i))).sum = i := by
      rw [sum_single _ i 16 hi (fun j hj hji => by
        simp only [Function.comp, sm, ev_mul, ev_const, hu j hj hji, Nat.mul_zero, Nat.zero_mod])]
      simp only [Function.comp, sm, ev_mul, ev_const, h1i, Nat.mul_one]
      have hP : i < 2013265921 := Nat.lt_of_lt_of_le hi (by decide)
      rw [Nat.mod_eq_of_lt hP, Nat.mod_eq_of_lt hP]
    rw [hN]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hi (by decide))

end

end StateM5a.FieldRows2
