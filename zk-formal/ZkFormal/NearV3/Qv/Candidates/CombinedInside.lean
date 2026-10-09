import ZkFormal.NearV3.Qv.Candidates.CombinedBoolean

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

/-- All metadata carried through a multi-byte key is independent of byte position. -/
theorem Walk.same_word_cells (w : Walk) (pos npos : Nat) (b nb : UInt8) :
    ∀ x ∈ [CombinedTable.lo,CombinedTable.hi,CombinedTable.slot,ValueTable.vid,
      ValueTable.tau,ValueTable.users,CombinedTable.absent,CombinedTable.main,
      CombinedTable.lastMain,ValueTable.count],
      (w.row npos nb).getD x 0=(w.row pos b).getD x 0 := by
  simp [CombinedTable.lo,CombinedTable.hi,CombinedTable.slot,ValueTable.vid,
    ValueTable.tau,ValueTable.users,CombinedTable.absent,CombinedTable.main,
    CombinedTable.lastMain,ValueTable.count]

theorem Walk.inside_metadata {F : Type} [Lean.Grind.CommRing F]
    (w : Walk) (pos : Nat) (b nb : UInt8) (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row pos b).getD c 0))
    (hn : ∀ c, tr.cell t ((r+1)%tr.height t) c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row (pos+1) nb).getD c 0)) :
    ∀ x ∈ [CombinedTable.lo,CombinedTable.hi,CombinedTable.slot,ValueTable.vid,
      ValueTable.tau,ValueTable.users,CombinedTable.absent,CombinedTable.main,
      CombinedTable.lastMain,ValueTable.count],
      (eqG CombinedTable.inside (n x) (c x)).eval tr t r pub=0 := by
  intro x hx
  have he := w.same_word_cells pos (pos+1) b nb x hx
  simp only [eqG,sub,n,c,Expr.eval,Expr.evalWith,rowEnv,Bool.true_eq,Bool.false_eq_true,
    ite_true,ite_false,hc,hn,he,Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.Semiring.mul_zero]

theorem Walk.inside_clock {F : Type} [Lean.Grind.CommRing F]
    (w : Walk) (pos : Nat) (b nb : UInt8) (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row pos b).getD c 0))
    (hn : ∀ c, tr.cell t ((r+1)%tr.height t) c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row (pos+1) nb).getD c 0)) :
    ∀ e ∈ [eqG CombinedTable.inside (n CombinedTable.walk) (k 1),
      Expr.mul CombinedTable.inside (n CombinedTable.wf),
      eqG CombinedTable.inside (n CombinedTable.wp) (Expr.add (c CombinedTable.wp) (k 1))],
      e.eval tr t r pub=0 := by
  have hadd := @Lean.Grind.Semiring.natCast_add F _ pos 1
  simp [eqG,sub,n,c,k,Expr.eval,Expr.evalWith,rowEnv,hc,hn,
    CombinedTable.walk,CombinedTable.wf,CombinedTable.wp,hadd,
    Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.natCast_one,
    Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.Semiring.mul_zero]

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
