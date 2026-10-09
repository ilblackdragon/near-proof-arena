import ZkFormal.NearV3.Render.Ups.CompactExtract.ByteRows
import ZkFormal.NearV3.Extract.Ups.HeaderBits
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
section
variable {C D : URow} (ok : RowOk C D) (hC : ∀ x, C x < P)
include ok hC

theorem headerBits (hst : C sTAG + C sHPL + C sHPF=1) : ∀ i, i<8 → C (reg i)≤1 := by
  intro i hi
  have f := fact ok (e:=Expr.mul (sumc [sTAG,sHPL,sHPF]) (Dsl.bool (c (reg i))))
    (memBool (by
      unfold cBool
      simp only [List.mem_append,List.mem_map,List.mem_range]
      exact Or.inl (Or.inl (Or.inl (Or.inr ⟨i,hi,rfl⟩)))))
  simp only [sumc,List.map_cons,List.map_nil,Dsl.sum] at f
  uev_simp
  have hg : (Fp.ofNat (C sTAG) + (Fp.ofNat (C sHPL) + (Fp.ofNat (C sHPF) + 0)))=1 := by
    change ((C sTAG : Fp) + ((C sHPL : Fp) + ((C sHPF : Fp) + 0)))=1
    have hn : C sTAG+(C sHPL+C sHPF)=1 := by omega
    have hc := congrArg (fun n : Nat => (n : Fp)) hn
    simp only [natCast_add,cast1] at hc
    grind
  simp only [cast0,cast1] at f
  rw [hg] at f
  exact le1 (nat01 (hC _) (by grind))

theorem headerByte_lt (hoh : C sTAG+C sHPL+C sHPF+C sKEY+C sVLEN+C sVH+C sBM+C sCH+C sMEM=1)
    (hh : C sHPL=1) : C b<256 := by
  have hb := headerBits ok hC (by omega)
  have h0 := hb 0 (by decide); have h1 := hb 1 (by decide)
  have h2 := hb 2 (by decide); have h3 := hb 3 (by decide)
  have h4 := hb 4 (by decide); have h5 := hb 5 (by decide)
  have h6 := hb 6 (by decide); have h7 := hb 7 (by decide)
  have h := hplNibble ok hC hoh hh
  have he : C b = 16*(C (reg 0)+2*C (reg 1)+4*C (reg 2)+8*C (reg 3))+
      (C (reg 4)+2*C (reg 5)+4*C (reg 6)+8*C (reg 7)) := by
    apply natv (hC _) (by unfold P; omega)
    simp only [natCast_add,natCast_mul,cast_ofNat,UpsV3.hb,lb,Nat.reducePow,Nat.reduceAdd] at h ⊢
    grind
  omega
end
end ZkFormal.NearV3.Render.UpsRelay.Extract
