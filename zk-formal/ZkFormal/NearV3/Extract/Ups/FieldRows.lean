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

theorem memPlan {e : Expr} (h : e ∈ cPlan) : e ∈ UpsV3.constraints := by
  unfold UpsV3.constraints; simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))

theorem memBool {e : Expr} (h : e ∈ cBool) : e ∈ UpsV3.constraints := by
  unfold UpsV3.constraints; simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))))

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

/-- Field lengths at a field end (`idx` of the last row), in `Fp`. -/
abbrev FieldEndP (C : URow) : Prop :=
    (C sTAG = 1 → (C idx : Fp) = 0) ∧ (C sHPL = 1 → (C idx : Fp) = 3) ∧ (C sHPF = 1 → (C idx : Fp) = 0) ∧
    (C sKEY = 1 → (C idx : Fp) + 2 = (C qhk : Fp)) ∧ (C sVLEN = 1 → (C idx : Fp) = 3) ∧
    (C sVH = 1 → (C idx : Fp) = 31) ∧ (C sBM = 1 → (C idx : Fp) = 1) ∧ (C sCH = 1 → (C idx : Fp) = 31) ∧
    (C sMEM = 1 → (C idx : Fp) = 7)

theorem fieldEnd (hfe : C fe = 1) : FieldEndP C := by
  have l1 := fact ok (e := .mul (c fe) (.mul (c sTAG) (c idx))) (memFields (by simp [cFields]))
  have l2 := fact ok (e := .mul (c fe) (.mul (c sHPL) (sub (c idx) (k 3)))) (memFields (by simp [cFields]))
  have l3 := fact ok (e := .mul (c fe) (.mul (c sHPF) (c idx))) (memFields (by simp [cFields]))
  have l4 := fact ok (e := .mul (c fe) (.mul (c sKEY) (sub (.add (c idx) (k 2)) (c qhk)))) (memFields (by simp [cFields]))
  have l5 := fact ok (e := .mul (c fe) (.mul (c sVLEN) (sub (c idx) (k 3)))) (memFields (by simp [cFields]))
  have l6 := fact ok (e := .mul (c fe) (.mul (c sVH) (sub (c idx) (k 31)))) (memFields (by simp [cFields]))
  have l7 := fact ok (e := .mul (c fe) (.mul (c sBM) (sub (c idx) (k 1)))) (memFields (by simp [cFields]))
  have l8 := fact ok (e := .mul (c fe) (.mul (c sCH) (sub (c idx) (k 31)))) (memFields (by simp [cFields]))
  have l9 := fact ok (e := .mul (c fe) (.mul (c sMEM) (sub (c idx) (k 7)))) (memFields (by simp [cFields]))
  uev_simp
  simp only [cast_ofNat, hfe, cast1] at l1 l2 l3 l4 l5 l6 l7 l8 l9
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h => ?_⟩
  · rw [h, cast1] at l1; grind
  · rw [h, cast1] at l2; grind
  · rw [h, cast1] at l3; grind
  · rw [h, cast1] at l4; grind
  · rw [h, cast1] at l5; grind
  · rw [h, cast1] at l6; grind
  · rw [h, cast1] at l7; grind
  · rw [h, cast1] at l8; grind
  · rw [h, cast1] at l9; grind

/-- Field successions at a field end inside a part (`Fp`, the part constants of `C`). -/
abbrev FieldSuccP (C D : URow) : Prop :=
    (C sTAG = 1 → (D sHPL : Fp) = (C qtl : Fp) + (C qte : Fp) ∧ (D sBM : Fp) = (C qtb1 : Fp) ∧
      (D sVLEN : Fp) = (C qtb2 : Fp)) ∧
    (C sHPL = 1 → D sHPF = 1) ∧
    (C sHPF = 1 → (D sKEY : Fp) = 1 - (C nokey : Fp) ∧ (D sVLEN : Fp) = (C nokey : Fp) * (C qtl : Fp) ∧
      (D sCH : Fp) = (C nokey : Fp) * (C qte : Fp)) ∧
    (C sKEY = 1 → (D sVLEN : Fp) = (C qtl : Fp) ∧ (D sCH : Fp) = (C qte : Fp)) ∧
    (C sVLEN = 1 → D sVH = 1) ∧
    (C sVH = 1 → (D sMEM : Fp) = (C qtl : Fp) ∧ (D sBM : Fp) = (C qtb2 : Fp)) ∧
    (C sBM = 1 → (D sMEM : Fp) = (C nochild : Fp) ∧ (D sCH : Fp) = 1 - (C nochild : Fp)) ∧
    (C sCH = 1 → (D sCH : Fp) + (D sMEM : Fp) = 1 ∧ (D sMEM : Fp) = (C lastw : Fp))

include hD in
theorem fieldSucc (hfe : C fe = 1) : FieldSuccP C D := by
  have s1 := fact ok (e := mul3 (c fe) (c sTAG) (sub (.add (c qtl) (c qte)) (n sHPL))) (memFields (by simp [cFields]))
  have s2 := fact ok (e := mul3 (c fe) (c sTAG) (sub (c qtb1) (n sBM))) (memFields (by simp [cFields]))
  have s3 := fact ok (e := mul3 (c fe) (c sTAG) (sub (c qtb2) (n sVLEN))) (memFields (by simp [cFields]))
  have s4 := fact ok (e := mul3 (c fe) (c sHPL) (not (n sHPF))) (memFields (by simp [cFields]))
  have s5 := fact ok (e := mul3 (c fe) (c sHPF) (sub (not (c nokey)) (n sKEY))) (memFields (by simp [cFields]))
  have s6 := fact ok (e := mul3 (c fe) (c sHPF) (sub (.mul (c nokey) (c qtl)) (n sVLEN))) (memFields (by simp [cFields]))
  have s7 := fact ok (e := mul3 (c fe) (c sHPF) (sub (.mul (c nokey) (c qte)) (n sCH))) (memFields (by simp [cFields]))
  have s8 := fact ok (e := mul3 (c fe) (c sKEY) (sub (c qtl) (n sVLEN))) (memFields (by simp [cFields]))
  have s9 := fact ok (e := mul3 (c fe) (c sKEY) (sub (c qte) (n sCH))) (memFields (by simp [cFields]))
  have s10 := fact ok (e := mul3 (c fe) (c sVLEN) (not (n sVH))) (memFields (by simp [cFields]))
  have s11 := fact ok (e := mul3 (c fe) (c sVH) (sub (c qtl) (n sMEM))) (memFields (by simp [cFields]))
  have s12 := fact ok (e := mul3 (c fe) (c sVH) (sub (c qtb2) (n sBM))) (memFields (by simp [cFields]))
  have s13 := fact ok (e := mul3 (c fe) (c sBM) (sub (c nochild) (n sMEM))) (memFields (by simp [cFields]))
  have s14 := fact ok (e := mul3 (c fe) (c sBM) (sub (not (c nochild)) (n sCH))) (memFields (by simp [cFields]))
  have s15 := fact ok (e := mul3 (c fe) (c sCH) (sub (k 1) (.add (n sCH) (n sMEM)))) (memFields (by simp [cFields]))
  have s16 := fact ok (e := mul3 (c fe) (c sCH) (sub (c lastw) (n sMEM))) (memFields (by simp [cFields]))
  have one := one_lt
  uev_simp
  simp only [cast_ofNat, hfe, cast1] at s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h, cast1] at s1 s2 s3; exact ⟨by grind, by grind, by grind⟩
  · rw [h, cast1] at s4; exact natv (hD _) one (by grind)
  · rw [h, cast1] at s5 s6 s7; exact ⟨by grind, by grind, by grind⟩
  · rw [h, cast1] at s8 s9; exact ⟨by grind, by grind⟩
  · rw [h, cast1] at s10; exact natv (hD _) one (by grind)
  · rw [h, cast1] at s11 s12; exact ⟨by grind, by grind⟩
  · rw [h, cast1] at s13 s14; exact ⟨by grind, by grind⟩
  · rw [h, cast1] at s15 s16; exact ⟨by grind, by grind⟩

include hC in
/-- A part flag on the part's first row. -/
theorem partBool (hpf : C pf = 1) {x : Nat} (hx : x ∈ partBools) : C x = 0 ∨ C x = 1 := by
  have h := fact ok (e := Expr.mul (c pf) (Dsl.bool (c x))) (memBool (by
    unfold cBool; simp only [List.mem_append, List.mem_map]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨x, hx, rfl⟩)))))))
  uev_simp
  simp only [hpf] at h
  have e : Fp.ofNat 1 = 1 := rfl
  rw [e] at h
  exact nat01 (hC x) (by grind)

include hC in
/-- The node type of the part (one-hot), `nokey`, `nochild`, on the part's first row. -/
theorem partHead (hpf : C pf = 1) (hq : C qb = 1) :
    (C qtl = 0 ∨ C qtl = 1) ∧ (C qte = 0 ∨ C qte = 1) ∧ (C qtb1 = 0 ∨ C qtb1 = 1) ∧ (C qtb2 = 0 ∨ C qtb2 = 1) ∧
    C qtl + C qte + C qtb1 + C qtb2 = 1 ∧ (C nokey = 0 ∨ C nokey = 1) ∧ (C nochild = 0 ∨ C nochild = 1) ∧
    (C nokey = 1 → C qhk = 1) := by
  have b1 := partBool ok hC hpf (x := qtl) (by simp [partBools])
  have b2 := partBool ok hC hpf (x := qte) (by simp [partBools])
  have b3 := partBool ok hC hpf (x := qtb1) (by simp [partBools])
  have b4 := partBool ok hC hpf (x := qtb2) (by simp [partBools])
  have b5 := partBool ok hC hpf (x := nokey) (by simp [partBools])
  have b6 := partBool ok hC hpf (x := nochild) (by simp [partBools])
  have h1 := fact ok (e := .mul (.mul (c qb) (c pf)) (sub (sumc [qtl, qte, qtb1, qtb2]) (k 1))) (memPlan (by simp [cPlan]))
  have h2 := fact ok (e := .mul (c pf) (.mul (c nokey) (sub (c qhk) (k 1)))) (memPlan (by simp [cPlan]))
  simp only [sumc, List.map_cons, List.map_nil, Dsl.sum] at h1
  uev_simp
  simp only [cast_ofNat, hpf, hq, cast1] at h1 h2
  refine ⟨b1, b2, b3, b4, ?_, b5, b6, fun h => ?_⟩
  · have := le1 b1; have := le1 b2; have := le1 b3; have := le1 b4
    apply natv (by have := P_gt; omega) one_lt
    simp only [natCast_add]; grind
  · rw [h, cast1] at h2; exact natv (hC _) one_lt (by grind)

include hC in
/-- An extension has one window: its `CH` rows are `lastw`. -/
theorem extLastw (ht : C qte = 1) (hc : C sCH = 1) : C lastw = 1 := by
  have h := fact ok (e := mul3 (c qte) (c sCH) (not (c lastw))) (memFields (by simp [cFields]))
  uev_simp
  simp only [cast_ofNat, ht, hc, cast1] at h
  exact natv (hC _) one_lt (by grind)

end

end ZkFormal.NearV3.UpsRows
