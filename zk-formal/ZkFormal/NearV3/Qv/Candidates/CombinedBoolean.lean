import ZkFormal.NearV3.Qv.Candidates.CombinedWalkBase

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

private theorem bool_nat_bound (b : Bool) : b.toNat≤1 := by cases b <;> decide

theorem Walk.flag_bounds (w : Walk) (pos : Nat) (b : UInt8) :
    ∀ c ∈ [CombinedTable.walk,CombinedTable.lo,CombinedTable.hi,CombinedTable.wf,
      CombinedTable.wl,CombinedTable.wend,CombinedTable.absent,CombinedTable.groupByte,
      CombinedTable.countRead,CombinedTable.main,CombinedTable.lastMain,CombinedTable.present],
      (w.row pos b).getD c 0≤1 := by
  cases hk : w.kind <;>
    simp [CombinedTable.walk,CombinedTable.lo,CombinedTable.hi,CombinedTable.wf,
      CombinedTable.wl,CombinedTable.wend,CombinedTable.absent,CombinedTable.groupByte,
      CombinedTable.countRead,CombinedTable.main,CombinedTable.lastMain,CombinedTable.present,
      hk,Kind.code,bool_nat_bound]

theorem Walk.byte_bit_bounds (w : Walk) (pos : Nat) (b : UInt8) :
    ∀ i<8, (w.row pos b).getD (ValueTable.reg i) 0≤1 := by
  intro i hi
  have he : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [ValueTable.reg]
  all_goals omega

private theorem cast_bit {F : Type} [Lean.Grind.CommRing F] (n : Nat) (hn : n≤1) :
    (@Nat.cast F Lean.Grind.Semiring.natCast n) *
      ((@Nat.cast F Lean.Grind.Semiring.natCast n) + -1)=0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
  all_goals simp only [Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.natCast_one]
  all_goals grind

theorem Walk.flag_constraints {F : Type} [Lean.Grind.CommRing F]
    (w : Walk) (pos : Nat) (b : UInt8) (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row pos b).getD c 0)) :
    ∀ x ∈ [CombinedTable.walk,CombinedTable.lo,CombinedTable.hi,CombinedTable.wf,
      CombinedTable.wl,CombinedTable.wend,CombinedTable.absent,CombinedTable.groupByte,
      CombinedTable.countRead,CombinedTable.main,CombinedTable.lastMain,CombinedTable.present],
      (Dsl.bool (c x)).eval tr t r pub=0 := by
  intro x hx
  simp only [Dsl.bool,Dsl.sub,Dsl.k,Dsl.c,Expr.eval,Expr.evalWith,rowEnv,
    Lean.Grind.Semiring.natCast_one,Bool.false_eq_true,ite_false,hc]
  exact cast_bit (F:=F) _ (w.flag_bounds pos b x hx)

theorem Walk.byte_bit_constraints {F : Type} [Lean.Grind.CommRing F]
    (w : Walk) (pos : Nat) (b : UInt8) (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row pos b).getD c 0)) :
    ∀ i<8, (Expr.mul (c CombinedTable.walk) (Dsl.bool (c (ValueTable.reg i)))).eval tr t r pub=0 := by
  intro i hi
  have hb := cast_bit (F:=F) _ (w.byte_bit_bounds pos b i hi)
  simp only [Dsl.bool,Dsl.sub,Dsl.k,Dsl.c,Expr.eval,Expr.evalWith,rowEnv,
    Lean.Grind.Semiring.natCast_one,Bool.false_eq_true,ite_false,hc,hb,Lean.Grind.Semiring.mul_zero]


theorem Walk.multiplicity_constraints {F : Type} [Lean.Grind.CommRing F]
    (w : Walk) (pos : Nat) (b : UInt8) (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row pos b).getD c 0)) :
    ∀ i ∈ CombinedTable.interactions, ∀ e ∈ i.mult,
      (Dsl.bool e).eval tr t r pub=0 := by
  have hb (bb : Bool) : (@Nat.cast F Lean.Grind.Semiring.natCast bb.toNat) *
      ((@Nat.cast F Lean.Grind.Semiring.natCast bb.toNat) + -1)=0 :=
    cast_bit _ (bool_nat_bound bb)
  simp [CombinedTable.interactions,send,recv,ValueTable.headerEnd,
    Dsl.bool,Dsl.sub,Dsl.not,Dsl.k,Dsl.c,Expr.eval,Expr.evalWith,rowEnv,hc,
    ValueTable.gb,ValueTable.vf,ValueTable.shard,ValueTable.header,ValueTable.sel,
    CombinedTable.walk,CombinedTable.wf,CombinedTable.wl,CombinedTable.present,
    CombinedTable.groupByte,CombinedTable.countRead,
    Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.natCast_one,
    Lean.Grind.Semiring.zero_mul,Lean.Grind.Semiring.mul_zero,
    Lean.Grind.AddCommGroup.add_neg_cancel,hb]


theorem Walk.table_bit_constraints {F : Type} [Lean.Grind.CommRing F]
    (w : Walk) (pos : Nat) (b : UInt8) (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row pos b).getD c 0)) :
    ∀ e ∈ CombinedTable.table.bitConstraints, e.eval tr t r pub=0 := by
  intro e he
  obtain ⟨i,hi,he⟩ := List.mem_flatMap.mp he
  obtain ⟨bit,hbit,rfl⟩ := List.mem_map.mp he
  exact w.multiplicity_constraints pos b tr t r pub hc i hi bit hbit

theorem Walk.inactive_gate_zero {F : Type} [Lean.Grind.CommRing F]
    (w : Walk) (pos : Nat) (b : UInt8) (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row pos b).getD c 0)) (x : Nat) :
    (Expr.mul (c x) (Dsl.not (c CombinedTable.walk))).eval tr t r pub=0 := by
  simp [Expr.eval,Expr.evalWith,rowEnv,Dsl.c,Dsl.not,Dsl.sub,Dsl.k,CombinedTable.walk,hc,
    Lean.Grind.Semiring.natCast_one,Lean.Grind.AddCommGroup.add_neg_cancel,
    Lean.Grind.Semiring.mul_zero]

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen


