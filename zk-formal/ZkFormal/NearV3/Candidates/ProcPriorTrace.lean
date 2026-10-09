import ZkFormal.NearV3.Candidates.ProcPriorIndexed
namespace ZkFormal.NearV3.Candidates.ProcPriorTrace
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ProcPriorRows ProcPriorCells

def nextSame (xs : List Row) (j : Nat) (a : Row) : Bool :=
  match xs[j+1]? with | none=>false | some b=>decide (a.event.link=b.event.link)
def nextInverse (xs : List Row) (j : Nat) (a : Row) : Fp :=
  match xs[j+1]? with | none=>0 | some b=>(Fp.ofNat b.event.link-Fp.ofNat a.event.link)⁻¹
def cells (xs : List Row) (t j : Nat) : Nat→Fp :=
  match xs[j]? with
  | none=>fun _=>0
  | some a=>cell a t (nextSame xs j a) (nextInverse xs j a)
def trace (xs : List Row) (t : Nat) : Trace Fp where
  log := fun _=>22
  cell := fun _ j=>cells xs t j

theorem cells_some (xs : List Row) (t j : Nat) (a : Row) (ha:xs[j]?=some a) :
    cells xs t j=cell a t (nextSame xs j a) (nextInverse xs j a) := by simp [cells,ha]
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

theorem bounds (wb rb cb : Nat) :
    ∀e∈(ProcPriorMemoryTable.table wb rb cb).exprs,e.pubBound=0 := by
  have h: ((ProcPriorMemoryTable.table wb rb cb).exprs.all (fun e=>decide (e.pubBound=0)))=true := by
    change ((ProcPriorMemoryTable.table 0 0 0).exprs.all (fun e=>decide (e.pubBound=0)))=true
    decide +kernel
  exact fun e he=>of_decide_eq_true (List.all_eq_true.mp h e he)

end ZkFormal.NearV3.Candidates.ProcPriorTrace
