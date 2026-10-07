import ZkFormal.NearV3.Qv.Candidates.CombinedWalkCells
import ZkFormal.NearV3.Qv.Candidates.CombinedTable
import ZkFormal.NearV3.Qv.Candidates.NaturalEval
import ZkFormal.NearV3.Render.WalkGen

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Near ValueGen

theorem byte_low_bits (b : UInt8) :
    b.toNat%2 + 2*(b.toNat/2%2) + 4*(b.toNat/4%2) + 8*(b.toNat/8%2) = b.toNat%16 := by
  have h := ZkFormal.NearV3.Render.WalkGen.bits_sum b.toNat 4
  simp [List.range_succ] at h
  omega

theorem byte_high_bits (b : UInt8) :
    b.toNat/16%2 + 2*(b.toNat/32%2) + 4*(b.toNat/64%2) + 8*(b.toNat/128%2) = b.toNat/16 := by
  have h := ZkFormal.NearV3.Render.WalkGen.bits_sum (b.toNat/16) 4
  have hb := b.toNat_lt
  have hb' : b.toNat/16 < 16 := by omega
  simp [List.range_succ,Nat.div_div_eq_div_mul,Nat.mod_eq_of_lt hb'] at h
  omega

theorem Walk.low_nibble (w : Walk) (pos : Nat) (b : UInt8) :
    rowNatEval (w.row pos b) (CombinedTable.nibble 0) = b.toNat%16 := by
  simp [CombinedTable.nibble,ValueTable.reg,Dsl.sum,Dsl.smul,Dsl.c,rowNatEval,List.range_succ]
  have h := byte_low_bits b
  omega

theorem Walk.high_nibble (w : Walk) (pos : Nat) (b : UInt8) :
    rowNatEval (w.row pos b) (CombinedTable.nibble 4) = b.toNat/16 := by
  simp [CombinedTable.nibble,ValueTable.reg,Dsl.sum,Dsl.smul,Dsl.c,rowNatEval,List.range_succ]
  have h := byte_high_bits b
  omega

theorem Walk.byte_reconstructed (w : Walk) (pos : Nat) (b : UInt8) :
    rowNatEval (w.row pos b) (CombinedTable.nibble 0) +
      16*rowNatEval (w.row pos b) (CombinedTable.nibble 4) = b.toNat := by
  rw [Walk.low_nibble,Walk.high_nibble]
  omega

theorem Walk.field_low_nibble {F : Type} [Lean.Grind.CommRing F]
    (w : Walk) (pos : Nat) (b : UInt8) (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast ((w.row pos b).getD c 0)) :
    (CombinedTable.nibble 0).eval tr t r pub =
      @Nat.cast F Lean.Grind.Semiring.natCast (b.toNat%16) := by
  rw [eval_nat_row _ _ _ _ _ _ (by decide) hc,Walk.low_nibble]

theorem Walk.field_high_nibble {F : Type} [Lean.Grind.CommRing F]
    (w : Walk) (pos : Nat) (b : UInt8) (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast ((w.row pos b).getD c 0)) :
    (CombinedTable.nibble 4).eval tr t r pub =
      @Nat.cast F Lean.Grind.Semiring.natCast (b.toNat/16) := by
  rw [eval_nat_row _ _ _ _ _ _ (by decide) hc,Walk.high_nibble]

private theorem flatMap_zipIdx_first {α β : Type} (xs : List α) (f : α → List β) :
    xs.zipIdx.flatMap (fun x => f x.1) = xs.flatMap f := by
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp

private theorem nibbles_flatMap (bs : NearSpec.Bytes) :
    bs.flatMap (fun b => [b.toNat/16,b.toNat%16]) = NearSpec.nibbles bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [NearSpec.nibbles,ih]

theorem Walk.key_symbols (w : Walk) :
    w.rows.flatMap (fun row => [rowNatEval row (CombinedTable.nibble 4),
      rowNatEval row (CombinedTable.nibble 0)]) = NearSpec.nibbles w.kind.bytes := by
  simp only [Walk.rows,List.flatMap_map,Function.comp_def,Walk.high_nibble,Walk.low_nibble]
  exact (flatMap_zipIdx_first w.kind.bytes
    (fun b : UInt8 => [b.toNat/16,b.toNat%16])).trans (nibbles_flatMap w.kind.bytes)

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
