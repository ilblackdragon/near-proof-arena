import ZkFormal.NearV3.Extract.Ups.LayoutRows

/-!
# ZkFormal.NearV3.Extract.Ups.FieldRows — row facts of `nodeV3`'s field grammar on `Q`

A row `C` with successor `D` (`URowOk C D`): field states are one-hot on node-part rows,
a part starts with a `TAG` field, a field counts `idx = 0, 1, …` and keeps its state, a field
end inside a part starts the next field, the part ends exactly at the end of its `MEM` field,
and the field lengths per state.
-/

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

theorem memFields {e : Expr} (h : e ∈ cFields) : e ∈ UpsV3.constraints := by
  unfold UpsV3.constraints; simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inr h)))

theorem memRows {e : Expr} (h : e ∈ cRows) : e ∈ UpsV3.constraints := by
  unfold UpsV3.constraints; simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))))

theorem one_lt : (1 : Nat) < P := by have := P_gt; omega

section
variable {C D : URow} (ok : URowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok

include hC in
theorem stBool {x : Nat} (hx : x ∈ states) : C x = 0 ∨ C x = 1 :=
  rowBool ok hC (by simp only [rowBools, List.mem_append]; exact Or.inl (Or.inr hx))

include hC in
/-- Field states: their sum is `qb`. -/
theorem stSum : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = C qb := by
  have h := fact ok (e := sub (sumc states) (c qb)) (memFields (by simp [cFields]))
  simp only [sumc, states, List.map_cons, List.map_nil, Dsl.sum] at h
  uev_simp
  try simp only [cast_ofNat] at *
  have b := fun {x} (hx : x ∈ states) => le1 (stBool ok hC hx)
  have := b (x := sTAG) (by simp [states]); have := b (x := sHPL) (by simp [states])
  have := b (x := sHPF) (by simp [states]); have := b (x := sKEY) (by simp [states])
  have := b (x := sVLEN) (by simp [states]); have := b (x := sVH) (by simp [states])
  have := b (x := sBM) (by simp [states]); have := b (x := sCH) (by simp [states])
  have := b (x := sMEM) (by simp [states])
  apply natv (by have := P_gt; omega) (hC _)
  simp only [natCast_add]; grind

/-- The field grammar facts of a row `C` with successor `D`. -/
abbrev FieldRowP (C D : URow) : Prop :=
    (C fs = 0 ∨ C fs = 1) ∧ (C fe = 0 ∨ C fe = 1) ∧
    (C pf = 1 → C qb = 1 → C sTAG = 1 ∧ C fs = 1) ∧
    (C fs = 1 → C idx = 0) ∧
    (C qb = 1 → C fe = 0 → (∀ x ∈ states, D x = C x) ∧ ((D idx : Nat) : Fp) = ((C idx : Nat) : Fp) + 1 ∧
      D fs = 0) ∧
    (C qb = 1 → C fe = 1 → C pl = 0 → D idx = 0 ∧ D fs = 1) ∧
    (C qb = 1 → C pl = C sMEM * C fe)

include hC hD in
/-- The field grammar, row by row. -/
theorem fieldRow : FieldRowP C D := by
  have bfs := rowBool ok hC (x := fs) (by simp [rowBools])
  have bfe := rowBool ok hC (x := fe) (by simp [rowBools])
  have bpl := rowBool ok hC (x := pl) (by simp [rowBools])
  have bqb := rowBool ok hC (x := qb) (by simp [rowBools])
  have bMEM := stBool ok hC (x := sMEM) (by simp [states])
  have r1 := fact ok (e := .mul (c pf) (.mul (c qb) (not (c sTAG)))) (memFields (by simp [cFields]))
  have r2 := fact ok (e := .mul (c pf) (.mul (c qb) (not (c fs)))) (memFields (by simp [cFields]))
  have r3 := fact ok (e := .mul (c fs) (c idx)) (memFields (by simp [cFields]))
  have rs : ∀ x ∈ states, uev C D (.mul (.mul (c qb) (not (c fe))) (sub (n x) (c x))) = 0 := fun x hx =>
    fact ok (memFields (by
      unfold cFields; simp only [List.mem_append, List.mem_map]
      exact Or.inl (Or.inl (Or.inl (Or.inr ⟨x, hx, rfl⟩)))))
  have r4 := fact ok (e := .mul (.mul (c qb) (not (c fe))) (sub (n idx) (.add (c idx) (k 1))))
    (memFields (by simp [cFields]))
  have r5 := fact ok (e := .mul (.mul (c qb) (not (c fe))) (n fs)) (memFields (by simp [cFields]))
  have r6 := fact ok (e := .mul (mul3 (c qb) (c fe) (not (c pl))) (n idx)) (memFields (by simp [cFields]))
  have r7 := fact ok (e := .mul (mul3 (c qb) (c fe) (not (c pl))) (not (n fs))) (memFields (by simp [cFields]))
  have r8 := fact ok (e := .mul (c qb) (sub (c pl) (.mul (c sMEM) (c fe)))) (memRows (by simp [cRows]))
  have one := one_lt
  have nz : (1 : Fp) ≠ 0 := by decide
  refine ⟨bfs, bfe, ?_, ?_, ?_, ?_, ?_⟩
  · intro h h'
    uev_simp; simp only [cast_ofNat, h, h', cast1] at r1 r2
    exact ⟨natv (hC _) one (by grind), natv (hC _) one (by grind)⟩
  · intro h
    uev_simp; simp only [cast_ofNat, h, cast1] at r3
    exact natv (hC _) (by have := P_gt; omega) (by rw [cast0]; grind)
  · intro h h'
    refine ⟨fun x hx => ?_, ?_, ?_⟩
    · have := rs x hx
      uev_simp; simp only [cast_ofNat, h, h', cast1, cast0] at this
      exact natv (hD _) (hC _) (by grind)
    · uev_simp; simp only [cast_ofNat, h, h', cast1, cast0] at r4; grind
    · uev_simp; simp only [cast_ofNat, h, h', cast1, cast0] at r5
      exact natv (hD _) (by have := P_gt; omega) (by rw [cast0]; grind)
  · intro h h' h''
    uev_simp; simp only [cast_ofNat, h, h', h'', cast1, cast0] at r6 r7
    exact ⟨natv (hD _) (by have := P_gt; omega) (by rw [cast0]; grind), natv (hD _) one (by grind)⟩
  · intro h
    uev_simp; simp only [cast_ofNat, h, cast1] at r8
    apply natv (hC _) (by rcases bMEM with h1 | h1 <;> rcases bfe with h2 | h2 <;> simp [h1, h2] <;> omega)
    rw [natCast_mul]; grind

end

end ZkFormal.NearV3.UpsRows
