import ZkFormal.Algebra.Statements

/-!
# ZkFormal.Algebra.RSProofs — Reed–Solomon linearity and separation

`RSLinStmt` and `RSSepStmt` from the polynomial statements:

* `rsLin_of`: `a·f + b·g` witnesses `a·u + b·v` (eval homomorphism, degree bounds).
* `rsSep_of`: if `dist n u v < n − D + 1` and some position disagrees, the
  agreement positions (≥ `D` of them) map injectively through `pts` to roots
  of `f − g`, which therefore is zero (`EqZeroOfRootsStmt`), so `u = v`.
-/

namespace ZkFormal.Algebra

open Lean.Grind

/-- `map` preserves `Nodup` when the function is injective on the list. -/
private theorem nodup_map_of_injOn {α β : Type} (f : α → β) :
    ∀ (l : List α), l.Nodup → (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hnd, hinj => by
    rw [List.map_cons, List.nodup_cons]
    rw [List.nodup_cons] at hnd
    refine ⟨?_, nodup_map_of_injOn f l hnd.2 fun x hx y hy => hinj x (by simp [hx]) y (by simp [hy])⟩
    intro hm
    obtain ⟨b, hb, hfb⟩ := List.mem_map.1 hm
    have := hinj b (by simp [hb]) a (by simp) hfb
    subst this
    exact hnd.1 hb

theorem rsLin_of (hE : PolyEvalStmt) (hD : PolyDegStmt) : RSLinStmt := by
  intro K _ n D pts u v a b hu hv
  obtain ⟨f, hf, hfu⟩ := hu
  obtain ⟨g, hg, hgv⟩ := hv
  refine ⟨Poly.smul a f + Poly.smul b g, ?_, ?_⟩
  · exact (hD K _ _ a D D).2.2.2.2.1 ((hD K f g a D D).2.2.2.2.2.1 hf)
      ((hD K g g b D D).2.2.2.2.2.1 hg)
  · intro i hi
    show a * u i + b * v i = _
    rw [(hE K _ _ (pts i) a).1, (hE K f g (pts i) a).2.2.2.2.1,
      (hE K g f (pts i) b).2.2.2.2.1, hfu i hi, hgv i hi]

theorem rsSep_of (hE : PolyEvalStmt) (hD : PolyDegStmt) (hR : EqZeroOfRootsStmt)
    (hZ : IsZeroEvalStmt) : RSSepStmt := by
  intro K _ _ n D pts hpts u v hu hv hdist i hi
  obtain ⟨f, hf, hfu⟩ := hu
  obtain ⟨g, hg, hgv⟩ := hv
  apply Classical.byContradiction
  intro hne
  -- agreement positions
  let A := (List.range n).filter fun j => decide (u j = v j)
  have hlen : A.length + LineLemma.dist n u v = n := by
    have h := List.length_eq_countP_add_countP (fun j => decide (u j = v j)) (l := List.range n)
    simp only [List.length_range] at h
    simp only [A, LineLemma.dist]
    rw [List.countP_eq_length_filter] at h
    have : (List.range n).countP (fun j => ¬ (decide (u j = v j)) = true) =
        (List.range n).countP (fun j => decide (u j ≠ v j)) := by
      apply List.countP_congr; intro j _; simp
    omega
  have hpos : 0 < LineLemma.dist n u v := by
    unfold LineLemma.dist
    rw [List.countP_pos_iff]
    exact ⟨i, List.mem_range.2 hi, by simpa using hne⟩
  have hAmem : ∀ j ∈ A, j < n ∧ u j = v j := by
    intro j hj
    simp only [A, List.mem_filter, List.mem_range, decide_eq_true_eq] at hj
    exact hj
  have hnd : (A.map pts).Nodup := by
    apply nodup_map_of_injOn pts A ((List.nodup_range).filter _)
    intro x hx y hy hxy
    exact hpts x y (hAmem x hx).1 (hAmem y hy).1 hxy
  have hdeg : (f - g).DegLt D :=
    (hD K f (-g) 0 D D).2.2.2.2.1 hf ((hD K g g 0 D D).2.2.2.2.2.2.1 hg)
  have hev : ∀ j, j < n → (f - g).eval (pts j) = u j - v j := by
    intro j hj
    rw [(hE K f g (pts j) 0).2.2.2.1, hfu j hj, hgv j hj]
  have hzero : (f - g).IsZero := by
    apply hR K (f - g) D (A.map pts) hdeg hnd
    · rw [List.length_map]; omega
    · intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      obtain ⟨hjn, hjuv⟩ := hAmem j hj
      rw [hev j hjn, hjuv]; grind
  have h0 := hZ K (f - g) (pts i) hzero
  rw [hev i hi] at h0
  exact hne (by grind)

end ZkFormal.Algebra
