import ZkFormal.NearV3.Qv.Candidates.CombinedImplicitSteps

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl NearSpec
open CombinedTable

def mainStepConstraints : List Expr :=
  [eqG advanceMain (n main) (k 1),
   eqG advanceMain (n slot) (Expr.add (c slot) (k 1)),
   eqG advanceMain (n lo) (Dsl.not (Expr.mul (c lo) (Dsl.not (c hi)))),
   eqG advanceMain (n hi) (sub (Expr.add (c lo) (c hi)) group),
   eqG advanceMain (n ValueTable.count) (c ValueTable.count)]

theorem main_step_equations {F : Type} [Lean.Grind.CommRing F]
    (a b : Walk) (i count : Nat)
    (ha : a.orderData=(0,i,count,min i 3))
    (hb : b.orderData=(0,i+1,count,min (i+1) 3))
    (pos : Nat) (ab bb : UInt8) (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((a.row pos ab).getD c 0))
    (hn : ∀ c, tr.cell t ((r+1)%tr.height t) c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((b.row 0 bb).getD c 0)) :
    ∀ e ∈ mainStepConstraints, e.eval tr t r pub=0 := by
  simp only [Walk.orderData,Prod.mk.injEq] at ha hb
  by_cases h3 : i<3
  · have he : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases he with rfl | rfl | rfl
    all_goals simp [mainStepConstraints,eqG,c,n,k,sub,Dsl.not,group,
      Expr.eval,Expr.evalWith,rowEnv,hc,hn,main,slot,lo,hi,ValueTable.count,
      ha.1,ha.2.1,ha.2.2.1,ha.2.2.2,hb.1,hb.2.1,hb.2.2.1,hb.2.2.2,
      Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.natCast_one,
      Lean.Grind.Semiring.natCast_add,Lean.Grind.AddCommGroup.add_neg_cancel,
      Lean.Grind.Semiring.mul_zero,Lean.Grind.Semiring.zero_mul,
      Lean.Grind.Semiring.one_mul,Lean.Grind.Semiring.mul_one,
      Lean.Grind.Semiring.add_zero,Lean.Grind.AddCommMonoid.zero_add,
      Lean.Grind.AddCommGroup.neg_zero]
    all_goals grind
  · have hia : min i 3=3 := Nat.min_eq_right (by omega)
    have hib : min (i+1) 3=3 := Nat.min_eq_right (by omega)
    simp [mainStepConstraints,eqG,c,n,k,sub,Dsl.not,group,
      Expr.eval,Expr.evalWith,rowEnv,hc,hn,main,slot,lo,hi,ValueTable.count,
      ha.1,ha.2.1,ha.2.2.1,ha.2.2.2,hb.1,hb.2.1,hb.2.2.1,hb.2.2.2,hia,hib,
      Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.natCast_one,
      Lean.Grind.Semiring.natCast_add,Lean.Grind.AddCommGroup.add_neg_cancel,
      Lean.Grind.Semiring.mul_zero,Lean.Grind.Semiring.zero_mul,
      Lean.Grind.Semiring.one_mul,Lean.Grind.Semiring.mul_one,
      Lean.Grind.Semiring.add_zero,Lean.Grind.AddCommMonoid.zero_add,
      Lean.Grind.AddCommGroup.neg_zero]
    grind


theorem mainPlan_step_equations {F : Type} [Lean.Grind.CommRing F]
    (pre : PTrie) (v : MainValues) (K : Nat) (resolve : Resolve)
    (d : Walk) (i : Nat) (hi : i+1<3+v.shards.length)
    (pos : Nat) (ab bb : UInt8) (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      (((mainPlan pre v K resolve).getD i d).row pos ab |>.getD c 0))
    (hn : ∀ c, tr.cell t ((r+1)%tr.height t) c = @Nat.cast F Lean.Grind.Semiring.natCast
      (((mainPlan pre v K resolve).getD (i+1) d).row 0 bb |>.getD c 0)) :
    ∀ e ∈ mainStepConstraints, e.eval tr t r pub=0 :=
  main_step_equations _ _ i v.shards.length
    (mainPlan_at_order pre v K resolve d i (by omega))
    (mainPlan_at_order pre v K resolve d (i+1) hi) pos ab bb tr t r pub hc hn

theorem main_step_mem : ∀ e ∈ mainStepConstraints, e ∈ CombinedTable.constraints := by
  intro e he
  simp only [mainStepConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  all_goals simp [CombinedTable.constraints]

theorem Walk.nonterminal_step_gates {F : Type} [Lean.Grind.CommRing F]
    (w : Walk) (pos : Nat) (b : UInt8) (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row pos b).getD c 0)) (hp : pos+1≠w.kind.bytes.length) :
    ∀ e ∈ [more,advanceMain,leaveMain,advanceImplicit], e.eval tr t r pub=0 := by
  simp [more,advanceMain,leaveMain,advanceImplicit,mul3,c,sub,
    Expr.eval,Expr.evalWith,rowEnv,hc,wl,wend,hp,Bool.toNat,
    Lean.Grind.Semiring.natCast_zero,Lean.Grind.AddCommGroup.neg_zero,
    Lean.Grind.Semiring.add_zero,Lean.Grind.Semiring.zero_mul]

theorem Walk.final_step_gates {F : Type} [Lean.Grind.CommRing F]
    (w : Walk) (pos : Nat) (b : UInt8) (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row pos b).getD c 0)) (hf : w.final=true) :
    ∀ e ∈ [more,advanceMain,leaveMain,advanceImplicit], e.eval tr t r pub=0 := by
  simp [more,advanceMain,leaveMain,advanceImplicit,mul3,c,sub,
    Expr.eval,Expr.evalWith,rowEnv,hc,wl,wend,hf,
    Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.Semiring.zero_mul]

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen

