import ZkFormal.NearV3.Qv.Candidates.ValueTable
import ZkFormal.Algebra.Fp

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open ZkFormal.Air

/-- The positive, current-row expression fragment used by parser interactions. -/
def rowNatExpr : Expr → Bool
  | .const _ | .col _ false => true
  | .add a b | .mul a b => rowNatExpr a && rowNatExpr b
  | _ => false

def rowNatEval (row : List Nat) : Expr → Nat
  | .const n => n
  | .col c false => row.getD c 0
  | .add a b => rowNatEval row a + rowNatEval row b
  | .mul a b => rowNatEval row a * rowNatEval row b
  | _ => 0

variable {F : Type} [Lean.Grind.CommRing F]

theorem eval_nat_row (e : Expr) (tr : Trace F) (t r : Nat) (pub : List F)
    (row : List Nat) (he : rowNatExpr e=true)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast (row.getD c 0)) :
    e.eval tr t r pub = @Nat.cast F Lean.Grind.Semiring.natCast (rowNatEval row e) := by
  induction e with
  | const n => rfl
  | col c nx => cases nx <;> simp_all [rowNatExpr,rowNatEval,Expr.eval,Expr.evalWith,rowEnv]
  | add a b ia ib =>
    simp only [rowNatExpr,Bool.and_eq_true] at he
    change a.eval tr t r pub + b.eval tr t r pub = _
    rw [ia he.1,ib he.2]
    exact (Lean.Grind.Semiring.natCast_add _ _).symm
  | mul a b ia ib =>
    simp only [rowNatExpr,Bool.and_eq_true] at he
    change a.eval tr t r pub * b.eval tr t r pub = _
    rw [ia he.1,ib he.2]
    exact (Lean.Grind.Semiring.natCast_mul _ _).symm
  | pub n => simp [rowNatExpr] at he
  | isFirst => simp [rowNatExpr] at he
  | isLast => simp [rowNatExpr] at he
  | isTransition => simp [rowNatExpr] at he
  | neg a ia => simp [rowNatExpr] at he

theorem interaction_nat_fragment :
    ValueTable.interactions.all (fun i => i.mult.all rowNatExpr && i.msg.all rowNatExpr)=true := by
  decide +kernel

end ZkFormal.NearV3.Qv.Candidates.ValueGen
