import ZkFormal.NearV3.Render.Ups.CompactExtract.FieldRows
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
section
variable {C D : URow} (ok : RowOk C D) (hC : ∀x,C x<P) (hD : ∀x,D x<P)
include ok hC hD
theorem sconst (ha : C act = 1) (hne : ¬ (C qb = 1 ∧ C pl = 1 ∧ C rootP = 1)) {x : Nat} (hx : x ∈ segConst) :
    D x = C x := by
  have h := fact ok (e := Expr.mul (sub (c act) (mul3 (c qb) (c pl) (c rootP))) (sub (n x) (c x))) (by simp only [compactConstraints,cConst,List.mem_append,List.mem_map,or_assoc]; exact Or.inr (Or.inr (Or.inl ⟨x,hx,rfl⟩)))
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
end ZkFormal.NearV3.Render.UpsRelay.Extract
