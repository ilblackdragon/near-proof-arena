import ZkFormal.NearV3.Candidates.ProcPriorVertical4ClockTrace
namespace ZkFormal.NearV3.Candidates.ProcPriorVertical4DataEval
open ZkFormal.Air ZkFormal.Algebra ProcPriorVertical4ClockCases ProcPriorVertical4Linear

def overlayEnv (d dn : Nat→Fp) (s sn : Nat) (f l fn ln gf gl : Bool) : Env Fp:=
  ProcPriorCells.env (cell d s f l) (cell dn sn fn ln) (flag gf) (flag gl) (flag (!gl))
def logicalEnv (d dn : Nat→Fp) (f l : Bool) : Env Fp:=
  ProcPriorCells.env d dn (flag f) (flag l) (1+ -(flag l))

/-- Every component reads only the shared data prefix. Its row flags are the
actual installed window markers, rather than the outer table's first/last row. -/
theorem expression_data (d dn : Nat→Fp) (s sn : Nat) (f l fn ln gf gl : Bool)
    (e : Expr) (hc:e.colBound≤23) :
    e.evalWith (windowEnv (overlayEnv d dn s sn f l fn ln gf gl))=
      e.evalWith (logicalEnv d dn f l) := by
  induction e with
  | const n=>rfl
  | pub n=>rfl
  | col i nx=>
    have hi:i<23:=by change i+1≤23 at hc; omega
    cases nx <;> simp [Expr.evalWith,windowEnv,overlayEnv,logicalEnv,ProcPriorCells.env,cell,hi]
  | isFirst=>rfl
  | isLast=>rfl
  | isTransition=>rfl
  | neg a ih=>exact congrArg Neg.neg (ih hc)
  | add a b ia ib=>
    have ha:a.colBound≤23:=Nat.le_trans (Nat.le_max_left _ _) hc
    have hb:b.colBound≤23:=Nat.le_trans (Nat.le_max_right _ _) hc
    change a.evalWith (windowEnv (overlayEnv d dn s sn f l fn ln gf gl)) + b.evalWith (windowEnv (overlayEnv d dn s sn f l fn ln gf gl))=
      a.evalWith (logicalEnv d dn f l) + b.evalWith (logicalEnv d dn f l)
    rw [ia ha,ib hb]
  | mul a b ia ib=>
    have ha:a.colBound≤23:=Nat.le_trans (Nat.le_max_left _ _) hc
    have hb:b.colBound≤23:=Nat.le_trans (Nat.le_max_right _ _) hc
    change a.evalWith (windowEnv (overlayEnv d dn s sn f l fn ln gf gl)) * b.evalWith (windowEnv (overlayEnv d dn s sn f l fn ln gf gl))=
      a.evalWith (logicalEnv d dn f l) * b.evalWith (logicalEnv d dn f l)
    rw [ia ha,ib hb]

theorem translated_data (d dn : Nat→Fp) (s sn : Nat) (f l fn ln gf gl : Bool)
    (e : Expr) (hc:e.colBound≤23) :
    (expression e).evalWith (overlayEnv d dn s sn f l fn ln gf gl)=
      e.evalWith (logicalEnv d dn f l) :=
  (expression_eval _ e).trans (expression_data d dn s sn f l fn ln gf gl e hc)

theorem component_columns : ∀T∈components,∀e∈T.exprs,e.colBound≤23 := by
  have h:components.all (fun T=>T.exprs.all (fun e=>decide (e.colBound≤23)))=true:=by decide +kernel
  exact fun T ht e he=>of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h T ht) e he)
end ZkFormal.NearV3.Candidates.ProcPriorVertical4DataEval
