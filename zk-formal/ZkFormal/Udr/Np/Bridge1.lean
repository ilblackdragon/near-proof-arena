import ZkFormal.Udr.Np.FrameMsg

/-!
# ZkFormal.Udr.Np.Bridge1 — generic pieces of the local bridge

* `passK_of_path`: the FRI pass predicate from the per-layer identities along
  the query path `j % nn i`;
* `permAt_shift`: the verifier position of the path at layer `i` is `x >>> i`;
* `foldPos` (the verifier's fold, on verifier positions) and the leaf fold
  `foldLeaf` as an iterate of `foldPos` (`foldLeaf_eq`).
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

/-! ## The pass predicate from the path identities -/

theorem passK_of_path {K : Type} [Field K] (S : Fri.Setup K) (R : Fri.Run K) (j : Nat)
    (hj : j < S.nn 0)
    (hsteps : ∀ i, i < S.r → R.f (i + 1) (j % S.nn (i + 1)) = Fri.rollW S R i (j % S.nn (i + 1)))
    (hfin : R.f S.r (j % S.nn S.r) () = ev (S.DD S.r) R.pr (S.xs S.r (j % S.nn S.r))) :
    Fri.passK S R S.r j := by
  have hdvd : ∀ i, i < S.r → S.nn (i + 1) ∣ S.nn i := fun i hi => ⟨2, by rw [S.hnn i hi]; omega⟩
  have key : ∀ k, k ≤ S.r → Fri.passK S R k (j % S.nn (S.r - k)) := by
    intro k
    induction k with
    | zero => intro _; simpa [Fri.passK] using hfin
    | succ k ih =>
      intro hk
      rw [Fri.passK]
      have e : (j % S.nn (S.r - (k + 1))) % S.nn (S.r - k) = j % S.nn (S.r - k) := by
        have := hdvd (S.r - (k + 1)) (by omega)
        rw [show S.r - (k + 1) + 1 = S.r - k by omega] at this
        exact Nat.mod_mod_of_dvd _ this
      rw [e]
      refine ⟨?_, ih (by omega)⟩
      have := hsteps (S.r - (k + 1)) (by omega)
      rw [show S.r - (k + 1) + 1 = S.r - k by omega] at this
      exact this
  have := key S.r (Nat.le_refl _)
  rwa [Nat.sub_self, Nat.mod_eq_of_lt hj] at this

/-! ## Path positions -/

theorem permK_succ_shr (n0 ℓ m j : Nat) (hj : j < 2 ^ (n0 - ℓ + m + 1)) :
    permK n0 ℓ (m + 1) j >>> 1 = permK n0 ℓ m (j % 2 ^ (n0 - ℓ + m)) := by
  rw [permK_succ, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  have : j / 2 ^ (n0 - ℓ + m) < 2 := Nat.div_lt_of_lt_mul (by rw [Nat.pow_succ] at hj; omega)
  generalize j / 2 ^ (n0 - ℓ + m) = c at *
  generalize permK n0 ℓ m (j % 2 ^ (n0 - ℓ + m)) = d
  omega

theorem permK_shift (n0 ℓ : Nat) : ∀ i k j, i ≤ k → j < 2 ^ (n0 - ℓ + k) →
    permK n0 ℓ k j >>> i = permK n0 ℓ (k - i) (j % 2 ^ (n0 - ℓ + k - i))
  | 0, k, j, _, hj => by simp [Nat.mod_eq_of_lt hj]
  | i + 1, k, j, hik, hj => by
    rw [Nat.shiftRight_add, permK_shift n0 ℓ i k j (by omega) hj,
      show k - i = (k - (i + 1)) + 1 by omega]
    have hlt : j % 2 ^ (n0 - ℓ + k - i) < 2 ^ (n0 - ℓ + (k - (i + 1)) + 1) := by
      rw [show n0 - ℓ + (k - (i + 1)) + 1 = n0 - ℓ + k - i by omega]
      exact Nat.mod_lt _ (Nat.pow_pos (by omega))
    rw [permK_succ_shr _ _ _ _ hlt, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)),
      show n0 - ℓ + (k - (i + 1)) = n0 - ℓ + k - (i + 1) by omega]

section
variable (A : Air) (prm : Params)

/-- The path through natural index `j` sits at verifier position `x >>> i`. -/
theorem permAt_path (τ : PTn) (hl : ellOf A prm τ ≤ n0Of A prm τ) (i j : Nat)
    (hi : i ≤ ellOf A prm τ) (hj : j < 2 ^ n0Of A prm τ) :
    permAt A prm τ i (j % 2 ^ (n0Of A prm τ - i)) = permAt A prm τ 0 j >>> i := by
  simp only [permAt, Nat.sub_zero]
  have e1 : n0Of A prm τ - ellOf A prm τ + ellOf A prm τ = n0Of A prm τ := by omega
  rw [permK_shift _ _ i _ j hi (by rw [e1]; exact hj), e1]

end

/-! ## The verifier's fold -/

/-- The verifier's fold of the pair at positions `p, p + 1` of layer `i`. -/
def foldPos (n0 i p : Nat) (β u0 u1 : Fp8) : Fp8 :=
  (2 : Fp8)⁻¹ * (u0 + u1) + β * (u0 - u1) * Fp8.ofBase ((2 * domPoint (K := Fp8) n0 (n0 - i) p)⁻¹)

theorem chunks2 : ∀ (n fuel : Nat) (l : List Fp8), l.length = 2 * n → n ≤ fuel →
    chunksOf.go 2 fuel l = (List.range n).map fun t => [l.getD (2 * t) 0, l.getD (2 * t + 1) 0]
  | 0, fuel, l, hl, _ => by
    obtain rfl : l = [] := List.length_eq_zero_iff.mp (by omega)
    cases fuel <;> rfl
  | n + 1, fuel, a :: b :: l, hl, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp only [List.length_cons] at hl
    rw [chunksOf.go.eq_3 _ _ _ (by simp), List.range_succ_eq_map]
    simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
      List.map_cons, List.map_map]
    rw [chunks2 n f l (by omega) (by omega)]
    simp only [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero, List.getD_cons_succ]
    congr 1
  | n + 1, _, [], hl, _ => by simp at hl
  | n + 1, _, [_], hl, _ => by simp at hl; omega

theorem foldOnce_spec (c : Ctx Fp8) (i base : Nat) (β : Fp8) (n : Nat) (us : List Fp8)
    (hl : us.length = 2 * n) :
    (foldOnce (F := Fp) c i base β us).length = n ∧
    ∀ t, t < n → (foldOnce (F := Fp) c i base β us).getD t 0 =
      foldPos c.n0 i (base + 2 * t) β (us.getD (2 * t) 0) (us.getD (2 * t + 1) 0) := by
  have hc : chunksOf 2 us = (List.range n).map fun t => [us.getD (2 * t) 0, us.getD (2 * t + 1) 0] :=
    chunks2 n us.length us hl (by omega)
  simp only [foldOnce, hc]
  refine ⟨by simp, fun t ht => ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (by simp; omega)]
  simp only [Option.map_some, Option.getD_some, List.getElem_zipIdx, List.getElem_map,
    List.getElem_range, Nat.zero_add, List.getD_cons_zero, List.getD_cons_succ, foldPos]
  rfl

/-- **The leaf fold.**  If the leaf holds the values `U 0 (base + t)` of layer
`c0` and `U (s+1)` is the verifier fold of `U s`, then `foldLeaf` returns
`U a (leaf index)`. -/
theorem foldLeaf_eq (c : Ctx Fp8) (c0 a j : Nat) (us : List Fp8) (U : Nat → Nat → Fp8)
    (hlen : us.length = 2 ^ a)
    (h0 : ∀ t, t < 2 ^ a → us.getD t 0 = U 0 ((j <<< a) + t))
    (hstep : ∀ s q, s < a → q < (j + 1) * 2 ^ (a - (s + 1)) → U (s + 1) q =
      foldPos c.n0 (c0 + s) (2 * q) (c.betas.getD (c0 + s) 0) (U s (2 * q)) (U s (2 * q + 1))) :
    foldLeaf (F := Fp) c c0 a j us = U a j := by
  let step := fun (acc : List Fp8) s =>
    foldOnce (F := Fp) c (c0 + s) (j <<< (a - s)) (c.betas.getD (c0 + s) 0) acc
  have inv : ∀ s, s ≤ a → ((List.range s).foldl step us).length = 2 ^ (a - s) ∧
      ∀ t, t < 2 ^ (a - s) → ((List.range s).foldl step us).getD t 0 = U s ((j <<< (a - s)) + t) := by
    intro s
    induction s with
    | zero => intro _; exact ⟨by simpa using hlen, fun t ht => by simpa using h0 t (by simpa using ht)⟩
    | succ s ih =>
      intro hs
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hl2 : ((List.range s).foldl step us).length = 2 * 2 ^ (a - (s + 1)) := by
        rw [ih1, show a - s = (a - (s + 1)) + 1 by omega, Nat.pow_succ]; omega
      obtain ⟨f1, f2⟩ := foldOnce_spec c (c0 + s) (j <<< (a - s)) (c.betas.getD (c0 + s) 0)
        (2 ^ (a - (s + 1))) _ hl2
      refine ⟨f1, fun t ht => ?_⟩
      show (foldOnce (F := Fp) c (c0 + s) (j <<< (a - s)) (c.betas.getD (c0 + s) 0) _).getD t 0 = _
      rw [f2 t ht, ih2 (2 * t) (by rw [show a - s = (a - (s + 1)) + 1 by omega, Nat.pow_succ]; omega),
        ih2 (2 * t + 1) (by rw [show a - s = (a - (s + 1)) + 1 by omega, Nat.pow_succ]; omega),
        hstep s _ (by omega) (by rw [Nat.shiftLeft_eq, Nat.succ_mul]; omega)]
      have e : j <<< (a - s) = 2 * (j <<< (a - (s + 1))) := by
        rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, show a - s = (a - (s + 1)) + 1 by omega, Nat.pow_succ]
        rw [Nat.mul_comm 2, Nat.mul_assoc]
      rw [e, show 2 * (j <<< (a - (s + 1))) + 2 * t = 2 * ((j <<< (a - (s + 1))) + t) by omega,
        show 2 * (j <<< (a - (s + 1))) + (2 * t + 1) = 2 * ((j <<< (a - (s + 1))) + t) + 1 by omega]
  obtain ⟨-, h2⟩ := inv a (Nat.le_refl _)
  have := h2 0 (by simp)
  simp only [Nat.sub_self, Nat.shiftLeft_zero, Nat.add_zero] at this
  exact this

end ZkFormal.Udr.Np
