import ZkFormal.NearV3.Qv.Candidates.CombinedMetadataEquations

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl
open CombinedTable

variable {F : Type} [Lean.Grind.CommRing F]

def firstConstraints : List Expr :=
  [Expr.mul .isFirst (Dsl.not (c walk)),Expr.mul .isFirst (Dsl.not (c wf)),
   Expr.mul .isFirst (Dsl.not (c main)),Expr.mul .isFirst (c ValueTable.tau),
   Expr.mul .isFirst (c slot),Expr.mul .isFirst (c lo),Expr.mul .isFirst (c hi)]

theorem first_main_constraints (v : MainValues) (K : Nat) (resolve : Resolve)
    (tr : Trace F) (t : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t 0 c = @Nat.cast F Lean.Grind.Semiring.natCast
      (((mainWalk v K resolve .delayed 0 v.delayed).row 0 7).getD c 0)) :
    ∀ e ∈ firstConstraints, e.eval tr t 0 pub=0 := by
  simp [firstConstraints,Expr.eval,Expr.evalWith,rowEnv,c,k,sub,Dsl.not,hc,
    walk,wf,main,ValueTable.tau,slot,lo,hi,mainWalk,Kind.code,
    Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.natCast_one,
    Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.Semiring.mul_zero]

theorem nonfirst_constraints (tr : Trace F) (t r : Nat) (pub : List F) (hr : r≠0) :
    ∀ e ∈ firstConstraints, e.eval tr t r pub=0 := by
  simp [firstConstraints,Expr.eval,Expr.evalWith,rowEnv,hr,Lean.Grind.Semiring.zero_mul]

theorem Walk.no_restart_equation (w : Walk) (pos : Nat) (b : UInt8)
    (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row pos b).getD c 0)) :
    (mul3 .isTransition (Dsl.not (c walk)) (n walk)).eval tr t r pub=0 := by
  simp [mul3,c,k,sub,Dsl.not,Expr.eval,Expr.evalWith,rowEnv,hc,walk,
    Lean.Grind.Semiring.natCast_one,Lean.Grind.AddCommGroup.add_neg_cancel,
    Lean.Grind.Semiring.mul_zero,Lean.Grind.Semiring.zero_mul]

theorem Walk.physical_last_equation (w : Walk) (pos : Nat) (b : UInt8)
    (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row pos b).getD c 0))
    (he : r+1=tr.height t → pos+1=w.kind.bytes.length ∧ w.final=true) :
    (mul3 .isLast (c walk) (Dsl.not (c wend))).eval tr t r pub=0 := by
  by_cases hr : r+1=tr.height t
  · obtain ⟨hp,hf⟩ := he hr
    simp [mul3,c,k,sub,Dsl.not,Expr.eval,Expr.evalWith,rowEnv,hc,wend,hp,hf,
      Lean.Grind.Semiring.natCast_one,Lean.Grind.AddCommGroup.add_neg_cancel,
      Lean.Grind.Semiring.mul_zero]
  · simp [mul3,Expr.eval,Expr.evalWith,rowEnv,hr,Lean.Grind.Semiring.zero_mul]

theorem Walk.exit_equation (w : Walk) (pos : Nat) (b : UInt8)
    (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row pos b).getD c 0))
    (he : pos+1=w.kind.bytes.length → w.final=true →
      r+1=tr.height t ∨ tr.cell t ((r+1)%tr.height t) walk=0) :
    (mul3 .isTransition (c wend) (n walk)).eval tr t r pub=0 := by
  by_cases hp : pos+1=w.kind.bytes.length <;> cases hf : w.final
  all_goals try simp [mul3,c,Expr.eval,Expr.evalWith,rowEnv,hc,wend,hp,hf,Bool.toNat,
    Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.mul_zero,Lean.Grind.Semiring.zero_mul]
  rcases he hp hf with hr | hn
  · simp [mul3,Expr.eval,Expr.evalWith,rowEnv,hr,Lean.Grind.Semiring.zero_mul]
  · simp [mul3,n,Expr.eval,Expr.evalWith,rowEnv,hn,Lean.Grind.Semiring.mul_zero]


theorem next_word_start_equations (next : Walk) (b : UInt8)
    (tr : Trace F) (t r : Nat) (pub : List F)
    (hn : ∀ c, tr.cell t ((r+1)%tr.height t) c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((next.row 0 b).getD c 0)) :
    ∀ e ∈ [eqG more (n walk) (k 1),eqG more (n wf) (k 1)], e.eval tr t r pub=0 := by
  simp [eqG,n,k,sub,Expr.eval,Expr.evalWith,rowEnv,hn,walk,wf,
    Lean.Grind.Semiring.natCast_one,Lean.Grind.AddCommGroup.add_neg_cancel,
    Lean.Grind.Semiring.mul_zero]

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen

