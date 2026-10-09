import ZkFormal.NearV3.Qv.Candidates.CombinedTable

namespace ZkFormal.NearV3.Qv.Candidates.CombinedTable
open ZkFormal.Air

def parserEnv {R : Type} (env : Env R) : Env R :=
  { env with col := fun x next => if x = ValueTable.len then
      env.mul (env.col x next) (env.add (env.ofNat 1) (env.neg (env.col walk next)))
    else env.col x next }

theorem parserExpr_eval {R : Type} (env : Env R) (e : Expr) :
    (parserExpr e).evalWith env = e.evalWith (parserEnv env) := by
  induction e with
  | col x next =>
    simp only [parserExpr]
    split <;> simp_all [Expr.evalWith,parserEnv,ZkFormal.Near.Dsl.not,
      ZkFormal.Near.Dsl.sub,ZkFormal.Near.Dsl.k]
  | add a b ha hb => simp [parserExpr,Expr.evalWith,parserEnv,ha,hb]
  | mul a b ha hb => simp [parserExpr,Expr.evalWith,parserEnv,ha,hb]
  | neg a ha => simp [parserExpr,Expr.evalWith,parserEnv,ha]
  | _ => rfl

theorem parserEnv_eq {R : Type} (env : Env R)
    (h : ∀ next, env.mul (env.col ValueTable.len next)
      (env.add (env.ofNat 1) (env.neg (env.col walk next))) = env.col ValueTable.len next) :
    parserEnv env = env := by
  have hc : (fun x next => if x = ValueTable.len then
      env.mul (env.col x next) (env.add (env.ofNat 1) (env.neg (env.col walk next)))
      else env.col x next) = env.col := by
    funext x next
    split
    · rename_i hx; subst x; exact h next
    · rfl
  unfold parserEnv
  rw [hc]

theorem parser_row_preserved {F : Type} [Lean.Grind.CommRing F]
    (tr : Trace F) (t r : Nat) (pub : List F)
    (hw : ∀ next, (rowEnv tr t r pub).col walk next = 0) (e : Expr) :
    (parserExpr e).eval tr t r pub = e.eval tr t r pub := by
  unfold Expr.eval
  rw [parserExpr_eval, parserEnv_eq]
  intro next
  have hh := hw next
  change tr.cell t (if next then (r+1)%tr.height t else r) walk = 0 at hh
  simp only [rowEnv,hh,Lean.Grind.Semiring.natCast_one]
  grind

end ZkFormal.NearV3.Qv.Candidates.CombinedTable
