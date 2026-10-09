import ZkFormal.NearV3.Assembly.RoutingQScratch

namespace ZkFormal.NearV3.Assembly.RoutingQCandidate
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

private theorem foldMul_eval (tr : Trace Fp) (t r : Nat) (pub : List Fp) (a b : Expr) :
    (foldMul a b).eval tr t r pub=a.eval tr t r pub*b.eval tr t r pub := by
  unfold foldMul
  split <;> simp only [Expr.eval,Expr.evalWith,rowEnv] <;> grind

private theorem foldAdd_eval (tr : Trace Fp) (t r : Nat) (pub : List Fp) (a b : Expr) :
    (foldAdd a b).eval tr t r pub=a.eval tr t r pub+b.eval tr t r pub := by
  unfold foldAdd
  split <;> simp only [Expr.eval,Expr.evalWith,rowEnv] <;> grind

theorem atState_eval {tr : Trace Fp} {t r state : Nat} {pub : List Fp}
    (hs : ∀c,4≤c → c≤26 → tr.cell t r c=if c=state then 1 else 0) (e : Expr) :
    (atState state e).eval tr t r pub=e.eval tr t r pub := by
  induction e with
  | const => rfl
  | col c nx =>
    cases nx with
    | true => rfl
    | false =>
      by_cases hc : 4≤c ∧ c≤26
      · simp only [atState,if_pos hc]
        have hh := hs c hc.1 hc.2
        by_cases he : c=state <;> simp only [Expr.eval,Expr.evalWith,rowEnv] <;> simp_all <;> grind
      · simp only [atState,if_neg hc]
  | pub => rfl
  | isFirst => rfl
  | isLast => rfl
  | isTransition => rfl
  | mul a b ia ib => simp only [atState,foldMul_eval,ia,ib,eval_mul]
  | add a b ia ib => simp only [atState,foldAdd_eval,ia,ib,eval_add]
  | neg a ia =>
    unfold atState
    split
    · rename_i he
      have hz : a.eval tr t r pub=0 := by rw [←ia,he];rfl
      change (0:Fp)= -(a.eval tr t r pub)
      rw [hz]
      grind
    · simp only [eval_neg,ia]

theorem added_degree : qBound.degree=3 ∧ qBound.colBound≤RcptV3.width := by decide

end ZkFormal.NearV3.Assembly.RoutingQCandidate
