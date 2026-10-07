import ZkFormal.NearV3.Qv.Candidates.CombinedInside
import ZkFormal.NearV3.Qv.Candidates.CombinedWalkBits

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl ValueGen

variable {F : Type} [Lean.Grind.CommRing F]

theorem Walk.byte_equation (w : Walk) (pos : Nat) (b : UInt8)
    (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row pos b).getD c 0)) :
    (eqG (c CombinedTable.walk) (c CombinedTable.wb)
      (Expr.add (CombinedTable.nibble 0) (smul 16 (CombinedTable.nibble 4)))).eval tr t r pub=0 := by
  have he : (Expr.add (CombinedTable.nibble 0) (smul 16 (CombinedTable.nibble 4))).eval
      tr t r pub = @Nat.cast F Lean.Grind.Semiring.natCast b.toNat := by
    rw [eval_nat_row _ _ _ _ _ _ (by decide) hc]
    exact congrArg (@Nat.cast F Lean.Grind.Semiring.natCast) (w.byte_reconstructed pos b)
  change tr.cell t r CombinedTable.walk * (tr.cell t r CombinedTable.wb + -
    (Expr.add (CombinedTable.nibble 0) (smul 16 (CombinedTable.nibble 4))).eval tr t r pub)=0
  rw [he,hc]
  simp [hc,CombinedTable.wb,Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.Semiring.mul_zero]

theorem Walk.mode_equation (w : Walk) (pos : Nat) (b : UInt8)
    (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row pos b).getD c 0)) :
    (eqG (c CombinedTable.walk) CombinedTable.readMode
      (Expr.add (Expr.mul (c CombinedTable.main) (Expr.add (c CombinedTable.lo) CombinedTable.group))
        (smul 2 (Dsl.not (c CombinedTable.main))))).eval tr t r pub=0 := by
  cases hk : w.kind <;> by_cases ht : w.tau=0
  all_goals simp [eqG,c,k,sub,smul,Dsl.not,Expr.eval,Expr.evalWith,rowEnv,hc,
    CombinedTable.walk,CombinedTable.readMode,CombinedTable.main,CombinedTable.lo,
    CombinedTable.hi,CombinedTable.group,ValueTable.len,Walk.mode,Kind.code,hk,ht,
    Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.natCast_one]
  all_goals try simp [ht,Bool.toNat]
  all_goals try simp only [Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.natCast_one]
  all_goals grind

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
