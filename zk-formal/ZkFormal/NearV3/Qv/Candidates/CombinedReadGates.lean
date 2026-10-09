import ZkFormal.NearV3.Qv.Candidates.CombinedReadAlgebra

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl
open CombinedTable

/-- The generated marker and request gates, without any accepted-trace premise. -/
def readGateConstraints : List Expr :=
  [eqG (c walk) (c ValueTable.act) (k 1),
   eqG (c walk) (c ValueTable.vz) (k 1),
   eqG (c walk) (c ValueTable.mRaw) (k 1),
   Expr.mul (c wend) (Dsl.not (c wl)),
   Expr.mul (c absent) (Expr.mul (c walk) (c ValueTable.vid)),
   sub (c present) (Expr.mul (c wl) (Dsl.not (c absent))),
   sub (c groupByte) (mul3 (c walk) group (Dsl.not (c wf))),
   sub (c countRead) (mul3 (c present) (c main) (Expr.mul (c lo) (Dsl.not (c hi)))),
   Expr.mul (c wf) (c wp)]


theorem read_gate_mem : ∀ e ∈ readGateConstraints, e ∈ CombinedTable.constraints := by
  intro e he
  simp only [readGateConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [CombinedTable.constraints]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
theorem Walk.read_gate_constraints {F : Type} [Lean.Grind.CommRing F]
    (w : Walk) (pos : Nat) (b : UInt8) (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row pos b).getD c 0)) :
    ∀ e ∈ readGateConstraints, e.eval tr t r pub=0 := by
  cases hk : w.kind <;> cases hv : w.value.isSome <;>
    cases hf : w.final <;> by_cases hp : pos=0 <;>
    by_cases hl : pos+1=w.kind.bytes.length <;> by_cases ht : w.tau=0
  all_goals try simp [hk,Kind.bytes,NearSpec.u64,NearSpec.leN_length,hp] at hl
  all_goals simp [readGateConstraints,eqG,c,k,sub,mul3,Dsl.not,Expr.eval,Expr.evalWith,rowEnv,
    walk,wend,wl,absent,present,groupByte,group,wf,wp,countRead,main,lo,hi,
    ValueTable.act,ValueTable.vz,ValueTable.mRaw,ValueTable.vid,hc,Kind.code,Kind.bytes,NearSpec.u64,NearSpec.leN_length,hk,hv,hf,hp,hl,ht,
    Bool.toNat,Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.natCast_one,
    Lean.Grind.Semiring.zero_mul,Lean.Grind.Semiring.mul_zero,
    Lean.Grind.Semiring.one_mul,Lean.Grind.Semiring.mul_one,
    Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.AddCommGroup.neg_zero,
    Lean.Grind.Semiring.add_zero,Lean.Grind.AddCommMonoid.zero_add]
  all_goals try omega
  all_goals grind

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
