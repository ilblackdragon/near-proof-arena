import ZkFormal.NearV3.Qv.Candidates.CombinedImplicitOrder
import ZkFormal.NearV3.Qv.Candidates.CombinedPhysical

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl
open CombinedTable
variable {F : Type} [Lean.Grind.CommRing F]

theorem implicit_step_equations (a b : Walk) (ht : b.tau=a.tau+1)
    (pos : Nat) (ab bb : UInt8) (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((a.row pos ab).getD c 0))
    (hn : ∀ c, tr.cell t ((r+1)%tr.height t) c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((b.row 0 bb).getD c 0)) :
    ∀ e ∈ [eqG advanceImplicit (n main) (k 0),
      eqG advanceImplicit (n ValueTable.tau) (Expr.add (c ValueTable.tau) (k 1))],
      e.eval tr t r pub=0 := by
  have hb : b.tau≠0 := by omega
  simp [eqG,c,n,k,sub,Expr.eval,Expr.evalWith,rowEnv,hc,hn,main,ValueTable.tau,
    hb,Bool.toNat,ht,Lean.Grind.Semiring.natCast_add,
    Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.natCast_one,
    Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.AddCommGroup.neg_zero,
    Lean.Grind.Semiring.add_zero,Lean.Grind.Semiring.mul_zero]

theorem enter_implicit_equations (b : Walk) (ht : b.tau=1)
    (bb : UInt8) (tr : Trace F) (t r : Nat) (pub : List F)
    (hn : ∀ c, tr.cell t ((r+1)%tr.height t) c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((b.row 0 bb).getD c 0)) :
    ∀ e ∈ [eqG leaveMain (n main) (k 0),eqG leaveMain (n ValueTable.tau) (k 1)],
      e.eval tr t r pub=0 := by
  simp [eqG,c,n,k,sub,Expr.eval,Expr.evalWith,rowEnv,hn,main,ValueTable.tau,ht,
    Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.natCast_one,
    Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.AddCommGroup.neg_zero,
    Lean.Grind.Semiring.add_zero,Lean.Grind.Semiring.mul_zero]

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
