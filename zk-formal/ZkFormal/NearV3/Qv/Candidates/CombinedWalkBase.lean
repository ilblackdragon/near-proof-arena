import ZkFormal.NearV3.Qv.Candidates.CombinedBoundary

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

/- Walk markers satisfy all transformed parser constraints. The only neighbor
requirement is the original parser's record-start condition. -/
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem Walk.base_constraints {F : Type} [Lean.Grind.CommRing F]
    (w : Walk) (pos : Nat) (b : UInt8) (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row pos b).getD c 0))
    (hn : tr.cell t ((r+1)%tr.height t) ValueTable.act=0 ∨
      tr.cell t ((r+1)%tr.height t) ValueTable.vf=1) :
    ∀ e ∈ ValueTable.constraints, (CombinedTable.parserExpr e).eval tr t r pub=0 := by
  simp only [Expr.eval,CombinedTable.parserExpr_eval]
  rcases hn with hn | hn
  all_goals
    simp [ValueTable.constraints,ValueTable.modes,ValueTable.phases,ValueTable.selectors,
      ValueTable.subpos,ValueTable.wordEnd,ValueTable.headerEnd,ValueTable.entryEnd,
      ValueTable.mode,ValueTable.counterBytes,ValueTable.same,
      Expr.evalWith,CombinedTable.parserEnv,rowEnv,c,n,k,ZkFormal.Near.Dsl.bool,
      sub,sum,smul,mul3,eqG,ZkFormal.Near.Dsl.not,
      ValueTable.act,ValueTable.vf,ValueTable.vl,ValueTable.vz,ValueTable.gb,
      ValueTable.cont,ValueTable.vid,ValueTable.len,ValueTable.pos,ValueTable.byte,ValueTable.users,
      ValueTable.tau,ValueTable.entry,ValueTable.count,ValueTable.mEmpty,ValueTable.mBuffer,
      ValueTable.mRaw,ValueTable.header,ValueTable.shard,ValueTable.firstIndex,ValueTable.nextIndex,
      ValueTable.sel,ValueTable.reg,CombinedTable.walk,List.range_succ,Function.comp_def,hc,
      Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.natCast_one,
      Lean.Grind.Semiring.zero_mul,Lean.Grind.Semiring.mul_zero,
      Lean.Grind.Semiring.one_mul,Lean.Grind.Semiring.mul_one,
      Lean.Grind.Semiring.add_zero,Lean.Grind.AddCommMonoid.zero_add,
      Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.AddCommGroup.neg_zero]
  all_goals simp only [ValueTable.act,ValueTable.vf] at hn
  all_goals simp [hn,Lean.Grind.Semiring.zero_mul,Lean.Grind.Semiring.mul_zero,
    Lean.Grind.AddCommGroup.add_neg_cancel]


theorem Walk.base_to_walk {F : Type} [Lean.Grind.CommRing F]
    (w next : Walk) (pos npos : Nat) (b nb : UInt8)
    (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row pos b).getD c 0))
    (hn : ∀ c, tr.cell t ((r+1)%tr.height t) c =
      @Nat.cast F Lean.Grind.Semiring.natCast ((next.row npos nb).getD c 0)) :
    ∀ e ∈ ValueTable.constraints, (CombinedTable.parserExpr e).eval tr t r pub=0 := by
  apply w.base_constraints pos b tr t r pub hc
  right
  rw [hn]
  simp [ValueTable.vf,Lean.Grind.Semiring.natCast_one]

theorem Walk.base_to_padding {F : Type} [Lean.Grind.CommRing F]
    (w : Walk) (pos : Nat) (b : UInt8) (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row pos b).getD c 0))
    (hn : ∀ c, tr.cell t ((r+1)%tr.height t) c = 0) :
    ∀ e ∈ ValueTable.constraints, (CombinedTable.parserExpr e).eval tr t r pub=0 :=
  w.base_constraints pos b tr t r pub hc (Or.inl (hn _))

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen

