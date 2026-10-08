import ZkFormal.NearV3.Candidates.ProcPriorIdBits
import ZkFormal.NearV3.Candidates.ProcPriorIdRanges
import ZkFormal.NearV3.Candidates.ProcPriorIndexed
namespace ZkFormal.NearV3.Candidates.ProcPriorIdTrace
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ProcPriorIdRows ProcPriorCells

def cells (xs : List Row) (t j : Nat) : Nat→Fp :=
  match xs[j]? with
  | none=>fun _=>0
  | some a=>ProcPriorIdCells.cells a (xs[j+1]?) t
def trace (xs : List Row) (t : Nat) : Trace Fp where
  log := fun _=>22
  cell := fun _ j=>cells xs t j

theorem cells_some (xs : List Row) (t j : Nat) (a : Row) (ha:xs[j]?=some a) :
    cells xs t j=ProcPriorIdCells.cells a (xs[j+1]?) t := by simp [cells,ha]
theorem cells_none (xs : List Row) (t j : Nat) (ha:xs[j]?=none) :
    cells xs t j=fun _=>0 := by simp [cells,ha]

theorem eval_pub (e : Expr) (he:e.pubBound=0) (en : Env Fp) (p : Nat→Fp) :
    e.evalWith {en with pub:=p}=e.evalWith en := by
  induction e with
  | pub i => simp [Expr.pubBound] at he
  | add a b ia ib | mul a b ia ib =>
    simp only [Expr.pubBound,Nat.max_eq_zero_iff] at he
    simp only [Expr.evalWith,ia he.1,ib he.2]
  | neg a ia => exact congrArg en.neg (ia he)
  | _ => rfl

theorem row_eval (xs : List Row) (t tt j : Nat) (pub : List Fp) (e : Expr) (he:e.pubBound=0) :
    e.eval (trace xs t) tt j pub=
      e.evalWith (env (cells xs t j) (cells xs t ((j+1)%2^22))
        (if j=0 then 1 else 0) (if j+1=2^22 then 1 else 0) (if j+1=2^22 then 0 else 1)) := by
  let en:=env (cells xs t j) (cells xs t ((j+1)%2^22))
    (if j=0 then 1 else 0) (if j+1=2^22 then 1 else 0) (if j+1=2^22 then 0 else 1)
  have hc:rowEnv (trace xs t) tt j pub={en with pub:=fun i=>pub.getD i 0} := by
    simp only [rowEnv,trace,Trace.height,en,env]
    congr 1
    funext c nx
    cases nx <;> rfl
  change e.evalWith (rowEnv (trace xs t) tt j pub)=e.evalWith en
  rw [hc]
  exact eval_pub e he en (fun i=>pub.getD i 0)

theorem bounds (pb qb rb cb : Nat) :
    ∀e∈(ProcPriorIdTable.table pb qb rb cb).exprs,e.pubBound=0 := by
  have h: ((ProcPriorIdTable.table pb qb rb cb).exprs.all (fun e=>decide (e.pubBound=0)))=true := by
    change ((ProcPriorIdTable.table 0 0 0 0).exprs.all (fun e=>decide (e.pubBound=0)))=true
    decide +kernel
  exact fun e he=>of_decide_eq_true (List.all_eq_true.mp h e he)

end ZkFormal.NearV3.Candidates.ProcPriorIdTrace
