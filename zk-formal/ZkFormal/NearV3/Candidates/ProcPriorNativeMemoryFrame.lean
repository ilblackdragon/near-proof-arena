import ZkFormal.NearV3.Candidates.ProcPriorNativeMemoryChain
namespace ZkFormal.NearV3.Candidates.ProcPriorNativeMemory
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Chacha.Table.E
open ProcPriorMemoryTable ProcPriorCells

theorem cells_some (xs : List Tagged) (j : Nat) (a : Tagged) (ha:xs[j]?=some a) :
    cells xs j=cell a.row a.tau (nextSame xs j a) (nextInverse xs j a) := by simp [cells,ha]
theorem cells_none (xs : List Tagged) (j : Nat) (ha:xs[j]?=none) :
    cells xs j=fun _=>0 := by simp [cells,ha]

theorem chain_pair (xs : List Tagged) (h:Chain xs) (j : Nat) (a b : Tagged)
    (ha:xs[j]?=some a) (hb:xs[j+1]?=some b) : Follows a b := by
  induction xs generalizing j with
  | nil=>simp at ha
  | cons c xs ih=>
    cases xs with
    | nil=>cases j <;> simp at hb
    | cons d xs=>
      cases j with
      | zero=>simp only [List.getElem?_cons_zero,Option.some.injEq] at ha
              simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] at hb
              subst a;subst b;exact h.1
      | succ j=>exact ih h.2 j ha hb

theorem row_eval (xs : List Tagged) (tt j : Nat) (pub : List Fp) (e : Expr) (he:e.pubBound=0) :
    e.eval (trace xs) tt j pub=
      e.evalWith (env (cells xs j) (cells xs ((j+1)%2^22))
        (if j=0 then 1 else 0) (if j+1=2^22 then 1 else 0) (if j+1=2^22 then 0 else 1)) := by
  let en:=env (cells xs j) (cells xs ((j+1)%2^22))
    (if j=0 then 1 else 0) (if j+1=2^22 then 1 else 0) (if j+1=2^22 then 0 else 1)
  have hc:rowEnv (trace xs) tt j pub={en with pub:=fun i=>pub.getD i 0} := by
    simp only [rowEnv,trace,Trace.height,en,env]
    congr 1
    funext c nx
    cases nx <;> rfl
  change e.evalWith (rowEnv (trace xs) tt j pub)=e.evalWith en
  rw [hc]
  exact ProcPriorTrace.eval_pub e he en (fun i=>pub.getD i 0)

theorem pair_bits (a b : Tagged) (first : Fp) (ns : Bool) (ni : Fp)
    (wb rb cb : Nat) (i : Interaction) (hi:i∈interactions wb rb cb) (e : Expr) (he:e∈i.mult) :
    e.evalWith (pairEnv a b first ns ni)=0 ∨ e.evalWith (pairEnv a b first ns ni)=1 := by
  have hone : Fp.ofNat 1 = (1:Fp) := rfl
  simp only [interactions,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl
  all_goals simp only [List.mem_singleton] at he; subst e
  all_goals simp only [Expr.evalWith,pairEnv,env,cell,adjacent,notE,sub,k,c,n,act,query,same,
    Bool.false_eq_true,ite_false,ite_true,hone]
  all_goals cases a.row.event.query <;> cases b.row.event.query <;>
    by_cases hk:address a=address b <;> (try simp [bit,hk]) <;> grind

end ZkFormal.NearV3.Candidates.ProcPriorNativeMemory
