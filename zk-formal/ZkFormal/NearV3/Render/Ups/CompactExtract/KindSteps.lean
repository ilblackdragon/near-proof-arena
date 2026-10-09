import ZkFormal.NearV3.Render.Ups.CompactExtract.Kinds
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
section
variable {C D : URow} (ok : RowOk C D) (hC : ∀x,C x<P) (hD : ∀x,D x<P)
include ok hC hD
theorem kinds :
    (C act = 0 ∨ C act = 1) ∧ C act = C wk + C vb + C qb ∧ C wk = C sf + C wt1 + C wt2 + C wt3 ∧
    (C sf = 0 ∨ C sf = 1) ∧ (C wt1 = 0 ∨ C wt1 = 1) ∧ (C wt2 = 0 ∨ C wt2 = 1) ∧ (C wt3 = 0 ∨ C wt3 = 1) ∧
    (C vb = 0 ∨ C vb = 1) ∧ (C qb = 0 ∨ C qb = 1) ∧ (C wk = 0 ∨ C wk = 1) ∧ (C pl = 0 ∨ C pl = 1) ∧
    (C sf = 1 → D wt1 = 1) ∧ (C wt1 = 1 → D wt2 = 1) ∧ (C wt2 = 1 → D wt3 = 1) ∧ (C wt3 = 1 → D qb = 1) ∧
    (C vb = 1 → C pl = 0 → D vb = 1) ∧ (C vb = 1 → C pl = 1 → D qb = 1) ∧
    (C qb = 1 → C pl = 0 → D qb = 1) ∧ (C qb = 1 → C pl = 1 → C rootP ≠ 1 → D qb = 1) ∧
    (C qb = 1 → C pl = 1 → C rootP = 1 → D act = D sf) := by
  have b := fun {x} (hx : x ∈ rowBools) => rowBool ok hC hx
  have bact := b (x := act) (by simp [rowBools])
  have bwk := b (x := wk) (by simp [rowBools])
  have bvb := b (x := vb) (by simp [rowBools])
  have bqb := b (x := qb) (by simp [rowBools])
  have bsf := b (x := sf) (by simp [rowBools])
  have bw1 := b (x := wt1) (by simp [rowBools])
  have bw2 := b (x := wt2) (by simp [rowBools])
  have bw3 := b (x := wt3) (by simp [rowBools])
  have bpl := b (x := pl) (by simp [rowBools])
  have h1 := fact ok (e := sub (c act) (.add (c wk) (.add (c vb) (c qb)))) (by simp [compactConstraints,compactRows,UpsV3.cRows])
  have h2 := fact ok (e := sub (c wk) (.add (c sf) (.add (c wt1) (.add (c wt2) (c wt3))))) (by simp [compactConstraints,compactRows,UpsV3.cRows])
  have t1 := fact ok (e := .mul (c sf) (not (n wt1))) (by simp [compactConstraints,compactRows,UpsV3.cRows])
  have t2 := fact ok (e := .mul (c wt1) (not (n wt2))) (by simp [compactConstraints,compactRows,UpsV3.cRows])
  have t3 := fact ok (e := .mul (c wt2) (not (n wt3))) (by simp [compactConstraints,compactRows,UpsV3.cRows])
  have t4 := fact ok (e := .mul (c wt3) (not (n qb))) (by simp [compactConstraints,compactRows,UpsV3.cRows])
  have t7 := fact ok (e := mul3 (c qb) (not (c pl)) (not (n qb))) (by simp [compactConstraints,compactRows,UpsV3.cRows])
  have t8 := fact ok (e := .mul (mul3 (c qb) (c pl) (not (c rootP))) (not (n qb))) (by simp [compactConstraints,compactRows,UpsV3.cRows])
  have t9 := fact ok (e := .mul (mul3 (c qb) (c pl) (c rootP)) (sub (n act) (n sf))) (by simp [compactConstraints,compactRows,UpsV3.cRows])
  have hv := noValue ok hC
  uev_simp
  try simp only [cast_ofNat] at *
  have one : (1 : Nat) < P := by have := P_gt; omega
  refine ⟨bact, ?_, ?_, bsf, bw1, bw2, bw3, bvb, bqb, bwk, bpl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : ((C act : Nat) : Fp) = ((C wk + C vb + C qb : Nat) : Fp) := by
      rw [natCast_add, natCast_add]; grind
    exact natv (hC _) (by have := P_gt; omega) this
  · have : ((C wk : Nat) : Fp) = ((C sf + C wt1 + C wt2 + C wt3 : Nat) : Fp) := by
      rw [natCast_add, natCast_add, natCast_add]; grind
    exact natv (hC _) (by have := P_gt; omega) this
  · intro h; rw [h] at t1; exact natv (hD _) one (by grind)
  · intro h; rw [h] at t2; exact natv (hD _) one (by grind)
  · intro h; rw [h] at t3; exact natv (hD _) one (by grind)
  · intro h; rw [h] at t4; exact natv (hD _) one (by grind)
  · intro h _; omega
  · intro h _; omega
  · intro h h'; rw [h, h'] at t7; exact natv (hD _) one (by grind)
  · intro h h' h''
    rw [h, h'] at t8
    have hne : ((1 : Nat) : Fp) + -((C rootP : Nat) : Fp) ≠ 0 := by
      intro h0; apply h''; exact natv (hC _) one (by grind)
    have : ((1 : Nat) : Fp) + -((D qb : Nat) : Fp) = 0 := by
      rcases mul_eq_zero'.mp t8 with h0 | h0
      · exfalso; apply hne; grind
      · exact h0
    exact natv (hD _) one (by grind)
  · intro h h' h''; rw [h, h', h''] at t9; exact natv (hD _) (hD _) (by grind)

end
end ZkFormal.NearV3.Render.UpsRelay.Extract
