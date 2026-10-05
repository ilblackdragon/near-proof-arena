import ZkFormal.Udr.Statements

/-!
# ZkFormal.Udr.GrandProduct — the grand-product and fingerprint rounds

* `gpGamma : GpGammaStmt` — distinct multisets `a`, `b` of field elements
  give equal products `∏ (γ - aᵢ) = ∏ (γ - bⱼ)` for at most `max |a| |b|`
  challenges `γ` (root bound + "equal products on enough points ⇒ `a ~ b`").
* `gpAlpha : GpAlphaStmt` — distinct multisets of width-`w` messages have
  fingerprint multisets that coincide for at most `|Ms| · w` challenges `α`
  (fix a message `m*` with different multiplicities; a bad `α` must collide
  `fp α m*` with some other message, and each collision is a root of a
  nonzero length-`w` polynomial).
-/

namespace ZkFormal.Udr

open ArenaCore.Security
open Lean.Grind

set_option linter.unusedSectionVars false

variable {K : Type} [Field K]

/-! ## Field and product helpers -/

theorem gp_mul_eq_zero {a b : K} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    have hinv := Field.mul_inv_cancel ha
    have : a⁻¹ * (a * b) = b := by grind
    grind

theorem gp_prod_eq_zero : ∀ (l : List K), l.prod = 0 → ∃ y ∈ l, y = 0
  | [], h => by
    rw [List.prod_nil] at h
    exact absurd h.symm Field.zero_ne_one
  | a :: l, h => by
    rw [List.prod_cons] at h
    rcases gp_mul_eq_zero h with h | h
    · exact ⟨a, List.mem_cons_self .., h⟩
    · obtain ⟨y, hy, hy0⟩ := gp_prod_eq_zero l h
      exact ⟨y, List.mem_cons_of_mem _ hy, hy0⟩

theorem gp_prod_perm {l l' : List K} (h : l.Perm l') : l.prod = l'.prod := by
  induction h with
  | nil => rfl
  | cons x _ ih => rw [List.prod_cons, List.prod_cons, ih]
  | swap x y l => rw [List.prod_cons, List.prod_cons, List.prod_cons, List.prod_cons]; grind
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

/-- `∏ (x - aᵢ)`. -/
def gpP (a : List K) (x : K) : K := (a.map (x - ·)).prod

theorem gpP_nil (x : K) : gpP [] x = 1 := by simp only [gpP, List.map_nil, List.prod_nil]

theorem gpP_cons (c : K) (a : List K) (x : K) : gpP (c :: a) x = (x - c) * gpP a x := by
  simp only [gpP, List.map_cons, List.prod_cons]

/-! ## Polynomiality -/

theorem isPoly_lin (c : K) : IsPoly (1 + 1) (fun x => x - c) := by
  obtain ⟨e, he⟩ := ((IsPoly.const (1 : K)).mulX).sub ((IsPoly.const c).mono (m' := 2) (by omega))
  exact ⟨e, fun x => by have := he x; simp only at this; rw [← this]; grind⟩

/-- A product of `|l|` factors, each of length `d + 1`, has length `|l|·d + 1`. -/
theorem isPoly_prod {β : Type} (d : Nat) (g : β → K → K) : ∀ (l : List β),
    (∀ i ∈ l, IsPoly (d + 1) (g i)) →
    IsPoly (l.length * d + 1) (fun x => (l.map (fun i => g i x)).prod)
  | [], _ => by
    simp only [List.length_nil, Nat.zero_mul, Nat.zero_add, List.map_nil, List.prod_nil]
    exact IsPoly.const 1
  | i :: l, h => by
    have h3 := IsPoly.mul (h i (List.mem_cons_self ..))
      (isPoly_prod d g l (fun j hj => h j (List.mem_cons_of_mem _ hj)))
    have e : d + l.length * d + 1 = (i :: l).length * d + 1 := by
      simp only [List.length_cons, Nat.succ_mul]; omega
    rw [e] at h3
    obtain ⟨c, hc⟩ := h3
    exact ⟨c, fun x => by rw [← hc x]; simp only [List.map_cons, List.prod_cons]⟩

theorem gpP_isPoly (a : List K) : IsPoly (a.length + 1) (gpP a) := by
  have := isPoly_prod 1 (fun c x => x - c) a (fun c _ => isPoly_lin c)
  rw [Nat.mul_one] at this
  exact this

/-! ## Equal products on enough points force equal multisets -/

open Classical in
theorem gp_perm_of_eq : ∀ (a b W : List K), W.Nodup → max a.length b.length < W.length →
    (∀ x, gpP a x = gpP b x) → a.Perm b
  | [], b, _, _, _, h => by
    cases b with
    | nil => exact List.Perm.refl _
    | cons c b' =>
      exfalso
      have := h c
      rw [gpP_nil, gpP_cons] at this
      have h0 : (c - c) * gpP b' c = 0 := by grind
      rw [← this] at h0
      exact Field.zero_ne_one h0.symm
  | a1 :: a', b, W, hW, hlen, h => by
    have hb0 : gpP b a1 = 0 := by rw [← h a1, gpP_cons]; grind
    have hmem : a1 ∈ b := by
      obtain ⟨y, hy, hy0⟩ := gp_prod_eq_zero _ hb0
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      have : a1 = z := by grind
      exact this ▸ hz
    have hperm := List.perm_cons_erase hmem
    have hbe : ∀ x, gpP b x = (x - a1) * gpP (b.erase a1) x := fun x => by
      rw [← gpP_cons]; exact gp_prod_perm (hperm.map _)
    have hlb := List.length_erase_of_mem hmem
    have hb1 : 1 ≤ b.length := List.length_pos_of_mem hmem
    have hW' := hW.erase a1
    have hlW : W.length - 1 ≤ (W.erase a1).length := by
      rw [List.length_erase]; split <;> omega
    simp only [List.length_cons] at hlen
    have hφ : IsPoly (max a'.length (b.erase a1).length + 1)
        (fun x => gpP a' x - gpP (b.erase a1) x) :=
      ((gpP_isPoly a').mono (by omega)).sub ((gpP_isPoly _).mono (by omega))
    have hz := hφ.eq_zero_of_roots (W.erase a1) hW' (by omega) (fun r hr => by
      have hra : r - a1 ≠ 0 := by
        have := ((List.Nodup.mem_erase_iff hW).mp hr).1
        grind
      have e := h r
      rw [gpP_cons, hbe] at e
      have : (r - a1) * (gpP a' r - gpP (b.erase a1) r) = 0 := by grind
      rcases gp_mul_eq_zero this with h1 | h1
      · exact absurd h1 hra
      · exact h1)
    have ih := gp_perm_of_eq a' (b.erase a1) (W.erase a1) hW' (by omega)
      (fun x => by have := hz x; grind)
    exact (ih.cons a1).trans hperm.symm

theorem gpGamma : GpGammaStmt := by
  intro K _ a b Ks hKs hab
  refine Nat.le_of_not_lt fun hc => hab ?_
  obtain ⟨l', hl'len, hl'mem, hl'nd⟩ :=
    filter_props Ks (fun γ => (a.map (γ - ·)).prod = (b.map (γ - ·)).prod)
  have hφ : IsPoly (max a.length b.length + 1) (fun x => gpP a x - gpP b x) :=
    ((gpP_isPoly a).mono (by omega)).sub ((gpP_isPoly b).mono (by omega))
  have hz := hφ.eq_zero_of_roots l' (hl'nd hKs) (by omega) (fun r hr => by
    have := (hl'mem r hr).2
    show gpP a r - gpP b r = 0
    simp only [gpP]; rw [this]; grind)
  exact gp_perm_of_eq a b l' (hl'nd hKs) (by omega) (fun x => by have := hz x; grind)

/-! ## Fingerprints -/

theorem fp_cons (α a : K) (m : List K) : fp α (a :: m) = a + α * fp α m := rfl

theorem fp_eq_ev (α : K) : ∀ m : List K, fp α m = ev m.length (fun k => m.getD k 0) α
  | [] => rfl
  | a :: m => by
    rw [fp_cons, fp_eq_ev α m, List.length_cons, ev_succ, List.getD_cons_zero]
    simp only [List.getD_cons_succ]

/-- Two distinct width-`w` messages collide at fewer than `w` challenges. -/
theorem fp_collide_lt {w : Nat} {m m' : List K} (hm : m.length = w) (hm' : m'.length = w)
    (hne : m ≠ m') (Ks : List K) (hKs : Ks.Nodup) :
    count Ks (fun α => fp α m = fp α m') < w := by
  have hc : ∃ k, k < w ∧ m.getD k 0 - m'.getD k 0 ≠ 0 := by
    refine Classical.byContradiction fun hno => hne (List.ext_getElem (by omega) fun i h1 h2 => ?_)
    have : m.getD i 0 - m'.getD i 0 = 0 :=
      Classical.byContradiction fun h => hno ⟨i, by omega, h⟩
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
      List.getElem?_eq_getElem h2] at this
    simp only [Option.getD_some] at this
    grind
  refine Nat.lt_of_le_of_lt (count_mono _ fun α h => ?_)
    (count_roots_lt (c := fun k => m.getD k 0 - m'.getD k 0) hc Ks hKs)
  show ev w (fun k => m.getD k 0 - m'.getD k 0) α = 0
  rw [ev_sub, ← hm, ← fp_eq_ev, hm, ← hm', ← fp_eq_ev, h]
  grind

theorem gpAlpha : GpAlphaStmt := by
  intro K _ w A B Ms Ks hKs hmem hAB
  classical
  obtain ⟨ms, hms⟩ : ∃ ms, List.count ms A ≠ List.count ms B :=
    Classical.byContradiction fun h => hAB (List.perm_iff_count.mpr fun ms =>
      Classical.byContradiction fun h' => h ⟨ms, h'⟩)
  have hmsAB : ms ∈ A ++ B := by
    refine Classical.byContradiction fun hn => hms ?_
    rw [List.mem_append, _root_.not_or] at hn
    rw [List.count_eq_zero_of_not_mem hn.1, List.count_eq_zero_of_not_mem hn.2]
  obtain ⟨_, hmsw⟩ := hmem ms hmsAB
  -- a bad `α` collides `ms` with another message of `A ++ B`
  let R : List K → K → Prop := fun m α => m ∈ A ++ B ∧ m ≠ ms ∧ fp α m = fp α ms
  have hsub : ∀ α, (A.map (fp α)).Perm (B.map (fp α)) → ∃ m ∈ Ms, R m α := by
    intro α hbad
    refine Classical.byContradiction fun hno => hms ?_
    have hiff : ∀ m ∈ A ++ B, (fp α m = fp α ms ↔ m = ms) := fun m hm => by
      refine ⟨fun he => Classical.byContradiction fun hne => hno ⟨m, (hmem m hm).1, hm, hne, he⟩,
        fun he => he ▸ rfl⟩
    have key : ∀ L : List (List K), (∀ m ∈ L, m ∈ A ++ B) →
        List.count (fp α ms) (L.map (fp α)) = List.count ms L := by
      intro L hL
      induction L with
      | nil => rfl
      | cons m L ih =>
        rw [List.map_cons, List.count_cons, List.count_cons,
          ih fun m' hm' => hL m' (List.mem_cons_of_mem _ hm')]
        have := hiff m (hL m (List.mem_cons_self ..))
        by_cases h : m = ms
        · simp [h]
        · have h' : fp α m ≠ fp α ms := fun e => h (this.mp e)
          simp [h, h']
    rw [← key A (fun m hm => List.mem_append_left _ hm),
      ← key B (fun m hm => List.mem_append_right _ hm)]
    exact hbad.count_eq _
  calc count Ks (fun α => (A.map (fp α)).Perm (B.map (fp α)))
      ≤ count Ks (fun α => ∃ m ∈ Ms, R m α) := count_mono _ hsub
    _ ≤ (Ms.map fun m => count Ks (R m)).sum := count_exists_mem_le _ _ _
    _ ≤ Ms.length * w := sum_le_length_mul _ _ _ fun m _ => by
      by_cases hm : m ∈ A ++ B ∧ m ≠ ms
      · exact Nat.le_of_lt (Nat.lt_of_le_of_lt
          (count_mono _ fun α (h : R m α) => h.2.2)
          (fp_collide_lt (hmem m hm.1).2 hmsw hm.2 Ks hKs))
      · have : count Ks (R m) ≤ count Ks (fun _ => False) :=
          count_mono _ fun α h => hm ⟨h.1, h.2.1⟩
        rw [count_const] at this
        simp only [ite_false] at this
        omega

end ZkFormal.Udr
