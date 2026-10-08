import ZkFormal.NearV3.Candidates.ProcPriorBoundary
namespace ZkFormal.NearV3.Candidates.ProcPriorCellBits
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Chacha.Table.E
open ProcPriorMemoryTable ProcPriorCells ProcPriorActive ProcPriorBoundary

theorem pair_bits (a b : ProcPriorRows.Row) (t : Nat) (first : Fp) (ns : Bool) (ni : Fp)
    (wb rb cb : Nat) (i : Interaction) (hi:i∈interactions wb rb cb) (e : Expr) (he:e∈i.mult) :
    e.evalWith (pairEnv a b t first ns ni)=0 ∨ e.evalWith (pairEnv a b t first ns ni)=1 := by
  have hone : Fp.ofNat 1 = (1:Fp) := rfl
  simp only [interactions,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl
  all_goals simp only [List.mem_singleton] at he; subst e
  all_goals simp only [Expr.evalWith,pairEnv,env,cell,adjacent,notE,sub,k,c,n,act,query,same,
    Bool.false_eq_true,ite_false,ite_true,hone]
  all_goals cases a.event.query <;> cases b.event.query <;>
    by_cases hk:a.event.link=b.event.link <;> (try simp [bit,hk]) <;> grind

theorem end_bits (a : ProcPriorRows.Row) (t : Nat) (first : Fp)
    (wb rb cb : Nat) (i : Interaction) (hi:i∈interactions wb rb cb) (e : Expr) (he:e∈i.mult) :
    e.evalWith (endEnv a t first)=0 ∨ e.evalWith (endEnv a t first)=1 := by
  have hone : Fp.ofNat 1 = (1:Fp) := rfl
  simp only [interactions,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl
  all_goals simp only [List.mem_singleton] at he; subst e
  all_goals simp only [Expr.evalWith,endEnv,env,cell,adjacent,notE,sub,k,c,n,act,query,same,
    Bool.false_eq_true,ite_false,ite_true,hone]
  all_goals cases a.event.query <;> (try simp [bit]) <;> grind

theorem padding_bits (nxt : Nat→Fp) (first last trans : Fp)
    (wb rb cb : Nat) (i : Interaction) (hi:i∈interactions wb rb cb) (e : Expr) (he:e∈i.mult) :
    e.evalWith (env (fun _=>0) nxt first last trans)=0 := by
  have hone : Fp.ofNat 1 = (1:Fp) := rfl
  simp only [interactions,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl
  all_goals simp only [List.mem_singleton] at he; subst e
  all_goals simp only [Expr.evalWith,env,adjacent,notE,sub,k,c,n,
    Bool.false_eq_true,ite_false,ite_true,hone]
  all_goals grind

end ZkFormal.NearV3.Candidates.ProcPriorCellBits
