import ZkFormal.NearV3.Qv.Candidates.CombinedReadGates

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl NearSpec
open CombinedTable

variable {F : Type} [Lean.Grind.CommRing F]

theorem Walk.last_position_equation (w : Walk) (pos : Nat) (b : UInt8)
    (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row pos b).getD c 0)) :
    (eqG (c wl) (c wp) (smul 8 group)).eval tr t r pub=0 := by
  cases hk : w.kind <;> by_cases hl : pos+1=w.kind.bytes.length
  all_goals try simp [hk,Kind.bytes,u64,leN_length] at hl
  all_goals try (have hp : pos=0 := by omega; subst pos)
  all_goals try (have hp : pos=8 := by omega; subst pos)
  all_goals simp [eqG,c,k,sub,smul,group,Expr.eval,Expr.evalWith,rowEnv,hc,
    wl,wp,lo,hi,Kind.code,Kind.bytes,u64,leN_length,hk,hl,Bool.toNat,
    Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.natCast_one]
  all_goals grind

theorem Walk.first_byte_equation (w : Walk) (pos : Nat) (b : UInt8)
    (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row pos b).getD c 0))
    (hb : pos=0 → b=w.kind.bytes.headD 0) :
    (eqG (c wf) (c wb) (sum [k 7,smul 6 (c lo),smul 3 (c hi)])).eval tr t r pub=0 := by
  by_cases hp : pos=0
  · subst pos
    have he := hb rfl
    cases hk : w.kind <;>
      simp [hk,Kind.bytes] at he <;> subst b
    all_goals simp [eqG,c,k,sub,smul,sum,Expr.eval,Expr.evalWith,rowEnv,hc,
      wf,wb,lo,hi,Kind.code,hk,Lean.Grind.Semiring.natCast_one,
      Lean.Grind.Semiring.natCast_zero]
    all_goals grind
  · simp [eqG,c,Expr.eval,Expr.evalWith,rowEnv,hc,wf,hp,Bool.toNat,
      Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.zero_mul]

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
