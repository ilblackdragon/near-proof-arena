import ZkFormal.NearV3.Extract.Ups.Rows

/-!
# ZkFormal.NearV3.Extract.Ups.LayoutRows — row facts of the segment layout

Pure row lemmas (a row `C` with successor `D`, `URowOk C D`): the walk rows, the value part
and the node parts follow each other; the position counter `qpos`; part and segment constants.
Equations that can wrap modulo `P` are stated in `Fp`.
-/

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

section
variable {C D : URow} (ok : URowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok

macro "cmem2" : tactic => `(tactic| simp [UpsV3.constraints, UpsV3.cRows, UpsV3.cConst, UpsV3.cBool])

include hC hD in
theorem layoutRow :
    (C pf = 0 ∨ C pf = 1) ∧ (C pl = 0 ∨ C pl = 1) ∧
    (C pf = 1 → C vb = 1 ∨ C qb = 1) ∧ (C pl = 1 → C vb = 1 ∨ C qb = 1) ∧
    (C pf = 1 → C qpos = 0) ∧
    (C wt3 = 1 → D vb = 1 ∧ D pf = 1) ∧
    (C vb = 1 → C pl = 0 → D vb = 1 ∧ D pf = 0 ∧ (D qpos : Fp) = (C qpos : Fp) + 1) ∧
    (C vb = 1 → C pl = 1 → D qb = 1 ∧ D pf = 1 ∧ D j = 1) ∧
    (C vb = 1 → C j = 0) ∧
    (C qb = 1 → C pl = 0 → D qb = 1 ∧ D pf = 0 ∧ (D qpos : Fp) = (C qpos : Fp) + 1) ∧
    (C qb = 1 → C pl = 1 → C rootP ≠ 1 → D qb = 1 ∧ D pf = 1 ∧ (D j : Fp) = (C j : Fp) + 1) ∧
    (C qb = 1 → C pl = 1 → (C qpos : Fp) + 1 = (C qlen : Fp)) ∧
    (C vb = 1 → C pl = 1 → (C qpos : Fp) + 1 =
      (C L0 : Fp) + (256 : Nat) * (C L1 : Fp) + (65536 : Nat) * (C L2 : Fp)) := by
  have one : (1 : Nat) < P := by have := P_gt; omega
  have bpf := rowBool ok hC (x := pf) (by simp [rowBools])
  have bpl := rowBool ok hC (x := pl) (by simp [rowBools])
  have bvb := rowBool ok hC (x := vb) (by simp [rowBools])
  have bqb := rowBool ok hC (x := qb) (by simp [rowBools])
  have r1 := fact ok (e := .mul (c pf) (not (.add (c vb) (c qb)))) (by cmem2)
  have r2 := fact ok (e := .mul (c pl) (not (.add (c vb) (c qb)))) (by cmem2)
  have r3 := fact ok (e := .mul (c pf) (c qpos)) (by cmem2)
  have r4 := fact ok (e := .mul (c wt3) (not (n vb))) (by cmem2)
  have r5 := fact ok (e := .mul (c wt3) (not (n pf))) (by cmem2)
  have r6 := fact ok (e := mul3 (c vb) (not (c pl)) (not (n vb))) (by cmem2)
  have r7 := fact ok (e := mul3 (c vb) (not (c pl)) (n pf)) (by cmem2)
  have r8 := fact ok (e := mul3 (.add (c vb) (c qb)) (not (c pl)) (sub (n qpos) (.add (c qpos) (k 1)))) (by cmem2)
  have r9 := fact ok (e := mul3 (c vb) (c pl) (not (n qb))) (by cmem2)
  have r10 := fact ok (e := mul3 (c vb) (c pl) (not (n pf))) (by cmem2)
  have r11 := fact ok (e := mul3 (c vb) (c pl) (sub (n j) (k 1))) (by cmem2)
  have r12 := fact ok (e := .mul (c vb) (c j)) (by cmem2)
  have r13 := fact ok (e := mul3 (c qb) (not (c pl)) (not (n qb))) (by cmem2)
  have r14 := fact ok (e := mul3 (c qb) (not (c pl)) (n pf)) (by cmem2)
  have r15 := fact ok (e := .mul (mul3 (c qb) (c pl) (not (c rootP))) (not (n qb))) (by cmem2)
  have r16 := fact ok (e := .mul (mul3 (c qb) (c pl) (not (c rootP))) (not (n pf))) (by cmem2)
  have r17 := fact ok (e := .mul (mul3 (c qb) (c pl) (not (c rootP))) (sub (n j) (.add (c j) (k 1)))) (by cmem2)
  have r18 := fact ok (e := mul3 (c qb) (c pl) (sub (.add (c qpos) (k 1)) (c qlen))) (by cmem2)
  have r19 := fact ok (e := mul3 (c vb) (c pl) (sub (.add (c qpos) (k 1)) Lexpr)) (by cmem2)
  simp only [Lexpr] at r19
  uev_simp
  try simp only [cast_ofNat] at *
  simp only [cast0, cast1] at *
  obtain ⟨bact, hact, -⟩ := kinds ok hC hD
  refine ⟨bpf, bpl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; rw [h] at r1
    rcases bvb with hv | hv
    · rcases bqb with hq | hq
      · rw [hv, hq, cast0] at r1; exact absurd r1 (by decide)
      · exact Or.inr hq
    · exact Or.inl hv
  · intro h; rw [h] at r2
    rcases bvb with hv | hv
    · rcases bqb with hq | hq
      · rw [hv, hq, cast0] at r2; exact absurd r2 (by decide)
      · exact Or.inr hq
    · exact Or.inl hv
  · intro h; simp only [h, cast0, cast1] at r3; exact natv (hC _) (by have := P_gt; omega) (by rw [cast0]; grind)
  · intro h; simp only [h, cast0, cast1] at r4 r5
    exact ⟨natv (hD _) one (by grind), natv (hD _) one (by grind)⟩
  · intro h h'
    have hq : C qb = 0 := by rcases bact with h0 | h0 <;> omega
    simp only [h, h', hq, cast0, cast1] at r6 r7 r8
    exact ⟨natv (hD _) one (by grind), natv (hD _) (by have := P_gt; omega) (by rw [cast0]; grind), by grind⟩
  · intro h h'; simp only [h, h', cast0, cast1] at r9 r10 r11
    exact ⟨natv (hD _) one (by grind), natv (hD _) one (by grind), natv (hD _) one (by grind)⟩
  · intro h; simp only [h, cast0, cast1] at r12; exact natv (hC _) (by have := P_gt; omega) (by rw [cast0]; grind)
  · intro h h'
    have hv : C vb = 0 := by rcases bact with h0 | h0 <;> omega
    simp only [h, h', hv, cast0, cast1] at r13 r14 r8
    exact ⟨natv (hD _) one (by grind), natv (hD _) (by have := P_gt; omega) (by rw [cast0]; grind), by grind⟩
  · intro h h' h''
    simp only [h, h', cast0, cast1] at r15 r16 r17
    have hne : (1 : Fp) + -((C rootP : Nat) : Fp) ≠ 0 := by
      intro h0; apply h''; exact natv (hC _) one (by grind)
    have e1 := (mul_eq_zero'.mp r15).resolve_left (by intro h0; apply hne; grind)
    have e2 := (mul_eq_zero'.mp r16).resolve_left (by intro h0; apply hne; grind)
    have e3 := (mul_eq_zero'.mp r17).resolve_left (by intro h0; apply hne; grind)
    exact ⟨natv (hD _) one (by grind), natv (hD _) one (by grind), by grind⟩
  · intro h h'; simp only [h, h', cast0, cast1] at r18; grind
  · intro h h'; simp only [h, h', cast0, cast1] at r19; grind

include hC hD in
/-- Part constants inside a part. -/
theorem pconst (hb : C vb = 1 ∨ C qb = 1) (hp : C pl = 0) {x : Nat} (hx : x ∈ partConst) : D x = C x := by
  have h := fact ok (e := Dsl.mul3 (.add (c vb) (c qb)) (not (c pl)) (sub (n x) (c x))) (by
    simp only [UpsV3.constraints, cConst, List.mem_append, List.mem_map]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr ⟨x, hx, rfl⟩)))))))))
  have bvb := rowBool ok hC (x := vb) (by simp [rowBools])
  have bqb := rowBool ok hC (x := qb) (by simp [rowBools])
  obtain ⟨bact, hact, -⟩ := kinds ok hC hD
  uev_simp
  try simp only [cast_ofNat] at *
  have hs : C vb + C qb = 1 := by rcases bact with h0 | h0 <;> omega
  have e : ((C vb : Nat) : Fp) + ((C qb : Nat) : Fp) = 1 := by rw [← natCast_add, hs]; rfl
  rw [e, hp] at h; simp only [cast0, cast1] at h
  exact natv (hD _) (hC _) (by grind)

include hC hD in
/-- Segment constants, except across the segment end. -/
theorem sconst (ha : C act = 1) (hne : ¬ (C qb = 1 ∧ C pl = 1 ∧ C rootP = 1)) {x : Nat} (hx : x ∈ segConst) :
    D x = C x := by
  have h := fact ok (e := Expr.mul (sub (c act) (mul3 (c qb) (c pl) (c rootP))) (sub (n x) (c x))) (by
    simp only [UpsV3.constraints, cConst, List.mem_append, List.mem_map]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨x, hx, rfl⟩)))))))))
  have bqb := rowBool ok hC (x := qb) (by simp [rowBools])
  have bpl := rowBool ok hC (x := pl) (by simp [rowBools])
  have one : (1 : Nat) < P := by have := P_gt; omega
  uev_simp
  try simp only [cast_ofNat] at *
  rw [ha] at h; simp only [cast0, cast1] at h
  have hnz : (1 : Fp) + -(((C qb : Nat) : Fp) * ((C pl : Nat) : Fp) * ((C rootP : Nat) : Fp)) ≠ 0 := by
    rcases bqb with hq | hq
    · rw [hq]; simp only [cast0]; intro h0; exact absurd (by grind : (1 : Fp) = 0) (by decide)
    · rcases bpl with hp | hp
      · rw [hp]; simp only [cast0]; intro h0; exact absurd (by grind : (1 : Fp) = 0) (by decide)
      · rw [hq, hp]; simp only [cast1]; intro h0
        exact hne ⟨hq, hp, natv (hC _) one (by grind)⟩
  have := (mul_eq_zero'.mp h).resolve_left hnz
  exact natv (hD _) (hC _) (by grind)

end

end ZkFormal.NearV3.UpsRows
