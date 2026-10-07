import ZkFormal.NearV3.Rcpt.Extract.V.StrField

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 NearSpec
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- A bit window of the active V3 receipt table represents a bounded natural. -/
theorem bitsX_eval {q : Nat} (hq : q<tr.height tt) (off len : Nat) (hb : off+len≤66) :
    (bitsX off len).eval tr tt q pub = ((bitsVal (fun j => cv tr tt q (xb j)) off len : Nat) : Fp) ∧
    bitsVal (fun j => cv tr tt q (xb j)) off len < 2^len := by
  have hbits : ∀ j, j<len → tr.cell tt q (xb (off+j))=0 ∨ tr.cell tt q (xb (off+j))=1 := by
    intro j hj
    apply isBool hL hq
    have hm : xb (off+j)∈(List.range 66).map xb := List.mem_map.mpr ⟨off+j,List.mem_range.mpr (by omega),rfl⟩
    simp only [boolCols,List.mem_append]
    exact Or.inl (Or.inr hm)
  exact ⟨eval_bits tr tt q pub xb off len hbits, bitsVal_lt _ off len (fun j hj => cv_bool (hbits j hj))⟩

/-- Length bounds `2 ≤ L ≤ 64` of a string field. -/
theorem str_len {s r0 L X Lc : Nat} (F : RFld tr tt s r0 L X) (hH : r0 + L < tr.height tt)
    (hc : ∀ k, k < L → tr.cell tt (r0 + k) Lc = ((L : Nat) : Fp))
    (m1 : mul3 (c fe) (c X) (sub (sub (c Lc) (k 2)) (bitsX 0 6)) ∈ RcptV3.constraints)
    (m2 : mul3 (c fe) (c X) (sub (sub (k 64) (c Lc)) (bitsX 6 6)) ∈ RcptV3.constraints) :
    2 ≤ L ∧ L ≤ 64 := by
  have hp := F.fld.pos
  have hq : r0 + (L - 1) < tr.height tt := by omega
  have c1 := con hL hq m1
  have c2 := con hL hq m2
  obtain ⟨b1, l1⟩ := bitsX_eval hL hq 0 6 (by omega)
  obtain ⟨b2, l2⟩ := bitsX_eval hL hq 6 6 (by omega)
  simp only [eval_mul3, eval_c, eval_sub, eval_k] at c1 c2
  rw [F.fld.fe (L - 1) (by omega), if_pos (by omega), F.fld.st (L - 1) (by omega), hc (L - 1) (by omega), b1] at c1
  rw [F.fld.fe (L - 1) (by omega), if_pos (by omega), F.fld.st (L - 1) (by omega), hc (L - 1) (by omega), b2] at c2
  have hLP : L < P := by have := hP hL; omega
  have e1 : L = 2 + bitsVal (fun j => cv tr tt (r0 + (L - 1)) (xb j)) 0 6 := by
    apply ofNat_inj hLP (by simp at l1; unfold P; omega); rw [natCast_add]; grind
  have e2 : 64 = L + bitsVal (fun j => cv tr tt (r0 + (L - 1)) (xb j)) 6 6 := by
    apply ofNat_inj (by unfold P; omega) (by simp at l2; unfold P; omega); rw [natCast_add]; grind
  omega


end ZkFormal.NearV3.RcptV3Proof
