import ZkFormal.NearV3.Rcpt.Candidates.SizeCountTables
import ZkFormal.Near.Extract.Common
namespace ZkFormal.NearV3.Candidates.CountLift
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Rcpt.Candidates.SizeCount

def tally (tr : Trace Fp) (inc : Expr) (t r : Nat) (pub : List Fp) : Fp :=
  ((List.range r).map (fun q=>inc.eval tr t q pub)).sum

def trace (tr : Trace Fp) (col : Nat) (inc : Expr) (pub : List Fp) : Trace Fp :=
  {log:=tr.log,cell:=fun t r c=>if c=col then tally tr inc t r pub else tr.cell t r c}

theorem prefix_zero (tr : Trace Fp) (inc : Expr) (t : Nat) (pub : List Fp) :
    tally tr inc t 0 pub=0 := rfl

theorem sum_append (xs ys : List Fp) : (xs++ys).sum=xs.sum+ys.sum := by
  induction xs with
  | nil => change ys.sum=0+ys.sum; grind
  | cons x xs ih =>
    change x+(xs++ys).sum=(x+xs.sum)+ys.sum
    rw [ih]
    grind

theorem prefix_succ (tr : Trace Fp) (inc : Expr) (t r : Nat) (pub : List Fp) :
    tally tr inc t (r+1) pub=tally tr inc t r pub+inc.eval tr t r pub := by
  simp only [tally,List.range_succ,List.map_append,List.map_cons,List.map_nil,sum_append]
  change _+(_+0)=_
  grind

theorem current (tr : Trace Fp) (col : Nat) (inc : Expr) (t r : Nat) (pub : List Fp) :
    (Dsl.c col).eval (trace tr col inc pub) t r pub=tally tr inc t r pub := by
  simp [Dsl.c,Expr.eval,Expr.evalWith,rowEnv,trace]

theorem next (tr : Trace Fp) (col : Nat) (inc : Expr) (t r : Nat) (pub : List Fp) :
    (Dsl.n col).eval (trace tr col inc pub) t r pub=tally tr inc t ((r+1)%tr.height t) pub := by
  simp [Dsl.n,Expr.eval,Expr.evalWith,rowEnv,trace,Trace.height]

theorem eval_old (tr : Trace Fp) (col : Nat) (inc : Expr) (t r : Nat) (pub : List Fp)
    (e : Expr) (he : e.colBound≤col) :
    e.eval (trace tr col inc pub) t r pub=e.eval tr t r pub := by
  induction e with
  | col i nx =>
    have hi : i≠col := by change i+1≤col at he; omega
    simp only [Expr.eval,Expr.evalWith,rowEnv,trace,if_neg hi]
    rfl
  | add a b ia ib =>
    change a.eval _ _ _ _+b.eval _ _ _ _=_
    rw [ia (by change max a.colBound b.colBound≤col at he; omega),
      ib (by change max a.colBound b.colBound≤col at he; omega)]
    rfl
  | mul a b ia ib =>
    change a.eval _ _ _ _*b.eval _ _ _ _=_
    rw [ia (by change max a.colBound b.colBound≤col at he; omega),
      ib (by change max a.colBound b.colBound≤col at he; omega)]
    rfl
  | neg a ia => exact congrArg Neg.neg (ia he)
  | _ => rfl

theorem count_local (tr : Trace Fp) (col : Nat) (inc : Expr) (t r : Nat) (pub : List Fp)
    (hinc : inc.colBound≤col) (hr : r<tr.height t) :
    ∀e∈countConstraints col inc,e.eval (trace tr col inc pub) t r pub=0 := by
  intro e he
  simp only [countConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl
  · change ((Expr.isFirst).eval (trace tr col inc pub) t r pub) * (Dsl.c col).eval (trace tr col inc pub) t r pub=0
    rw [current]
    change (if r=0 then 1 else 0 : Fp)*tally tr inc t r pub=0
    by_cases h:r=0
    · subst r; rw [prefix_zero]; grind
    · simp only [if_neg h]; grind
  · change ((Expr.isTransition).eval (trace tr col inc pub) t r pub)*
      ((Dsl.n col).eval (trace tr col inc pub) t r pub +
       -((Dsl.c col).eval (trace tr col inc pub) t r pub+inc.eval (trace tr col inc pub) t r pub))=0
    rw [current,next,eval_old tr col inc t r pub inc hinc]
    change (if r+1=tr.height t then 0 else 1 : Fp)*
      (tally tr inc t ((r+1)%tr.height t) pub +
       -(tally tr inc t r pub+inc.eval tr t r pub))=0
    by_cases h:r+1=tr.height t
    · simp only [if_pos h]; grind
    · rw [if_neg h,Nat.mod_eq_of_lt (by omega),prefix_succ]
      grind

def table (T : Air.Table) (col : Nat) (inc : Expr) : Air.Table :=
  {T with
    width:=col+1, constraints:=T.constraints++countConstraints col inc,
    interactions:=T.interactions.map (withCount (Dsl.c col))}

theorem lift_local {T : Air.Table} {tr : Trace Fp} {col t : Nat} {inc : Expr} {pub : List Fp}
    (h : TableLocal T tr t pub)
    (hcols : ∀e∈T.exprs,e.colBound≤col) (hinc : inc.colBound≤col) :
    TableLocal (table T col inc) (trace tr col inc pub) t pub := by
  refine ⟨h.log_ge,h.log_le,?_,?_⟩
  · intro r hr e he
    rcases List.mem_append.mp he with ho|hc
    · rw [eval_old _ _ _ _ _ _ _ (hcols e (List.mem_append_left _ ho))]
      exact h.constr r hr e ho
    · exact count_local tr col inc t r pub hinc hr e hc
  · intro r hr i hi e he
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    have hm : (withCount (Dsl.c col) j).mult=j.mult := by unfold withCount; split <;> rfl
    rw [hm] at he
    rw [eval_old _ _ _ _ _ _ _ (hcols e
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨j,hj,List.mem_append_left _ he⟩)))]
    exact h.bits r hr j hj e he
end ZkFormal.NearV3.Candidates.CountLift
