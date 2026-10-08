import ZkFormal.NearV3.Qv.Extract.NativeGroupKey

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.CombinedTable
open Candidates.ValueTable (reg)

variable {tr : Trace Fp} {tt r : Nat} {pub : List Fp}
variable (hL : TableLocal table tr tt pub) (hr : r<tr.height tt)
variable (hw : tr.cell tt r walk=1)
include hL hr hw

theorem walk_register_bool (i : Nat) (hi : i<8) :
    tr.cell tt r (reg i)=0 ∨ tr.cell tt r (reg i)=1 := by
  have hm := List.mem_map_of_mem (f:=fun i => Expr.mul (c walk) (Dsl.bool (c (reg i)))) (List.mem_range.mpr hi)
  have he : Expr.mul (c walk) (Dsl.bool (c (reg i)))∈constraints := by
    unfold constraints
    simp only [List.mem_append,hm,true_or,or_true]
  have hh := con hL hr he
  simp only [eval_mul,eval_c,eval_bool,hw] at hh
  apply bool_cases
  grind

/-- Nibble expressions are canonical four-bit naturals on every actual walk row. -/
theorem walk_nibble_eval (off : Nat) (hoff : off+4≤8) :
    (nibble off).eval tr tt r pub=(bitsVal (fun i => cv tr tt r (reg i)) off 4 : Fp) ∧
      bitsVal (fun i => cv tr tt r (reg i)) off 4<16 := by
  constructor
  · exact eval_bits tr tt r pub reg off 4 (fun i hi => walk_register_bool hL hr hw (off+i) (by omega))
  · exact bitsVal_lt _ off 4 (fun i hi => cv_bool (walk_register_bool hL hr hw (off+i) (by omega)))

/-- The physical wb register and its two KEYNIB symbols encode exactly the
same byte, with a derived byte range and no canonical-renderer assumption. -/
theorem walk_nibbles_byte : cv tr tt r wb<256 ∧
    (nibble 0).eval tr tt r pub=((cv tr tt r wb%16 : Nat) : Fp) ∧
    (nibble 4).eval tr tt r pub=((cv tr tt r wb/16 : Nat) : Fp) := by
  obtain ⟨hl,hlo⟩ := walk_nibble_eval hL hr hw 0 (by omega)
  obtain ⟨hh,hhi⟩ := walk_nibble_eval hL hr hw 4 (by omega)
  let l := bitsVal (fun i => cv tr tt r (reg i)) 0 4
  let h := bitsVal (fun i => cv tr tt r (reg i)) 4 4
  have hb := con hL hr (e:=eqG (c walk) (c wb) (.add (nibble 0) (smul 16 (nibble 4))))
    (by simp [constraints])
  simp only [eval_eqG,eval_c,eval_add,eval_smul,hw,hl,hh] at hb
  have hfield : (cv tr tt r wb:Fp)=((l+16*h:Nat):Fp) := by
    rw [←cell_eq_cast tr tt r wb]
    simp only [natCast_add,natCast_mul]
    change tr.cell tt r wb=(l:Fp)+(16:Nat)*(h:Fp)
    dsimp [l,h]
    grind
  have hp : 256<P := by decide
  have hnat : cv tr tt r wb=l+16*h := ofNat_inj (cv_lt _ _ _ _) (by dsimp [l,h]; omega) hfield
  have hlow : cv tr tt r wb%16=l := by dsimp [l,h] at *; omega
  have hhigh : cv tr tt r wb/16=h := by dsimp [l,h] at *; omega
  refine ⟨by dsimp [l,h] at hnat; omega,?_,?_⟩
  · rw [hlow]; exact hl
  · rw [hhigh]; exact hh

end ZkFormal.NearV3.Qv.Extract
