import ZkFormal.NearV3.Candidates.ProcPriorActive
namespace ZkFormal.NearV3.Candidates.ProcPriorBoundary
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Chacha.Table.E
open ProcPriorMemoryTable ProcPriorCells

def endEnv (a : ProcPriorRows.Row) (t : Nat) (first : Fp) : Env Fp :=
  env (cell a t false 0) (fun _=>0) first 0 1

theorem end_constraints (a : ProcPriorRows.Row) (t : Nat) (first : Fp)
    (hf:first=0 ∨ a.before=ProcPriorCarry.zero)
    (hq:a.event.query=true → a.before=ProcPriorValues.value a.event)
    (e : Expr) (hm:e∈constraints) : e.evalWith (endEnv a t first)=0 := by
  have hzero : Fp.ofNat 0 = (0:Fp) := rfl
  have hone : Fp.ofNat 1 = (1:Fp) := rfl
  rcases List.mem_append.mp hm with hm|hm
  · obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hm
    exact active_boolean a t false 0 _ first 0 1 c hc
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [Expr.evalWith,endEnv,env,cell,adjacent,delta,addr,nextAddr,
      notE,sub,k,c,n,act,tau,link,query,lo,hi,beforeLo,beforeHi,same,inverse,
      Bool.false_eq_true,ite_false,ite_true,hone,bit]
    all_goals try grind
    all_goals cases hquery:a.event.query
    all_goals simp [hquery,ProcPriorValues.value,ProcPriorCarry.zero] at *
    all_goals try grind
    all_goals rcases hf with hf|hf <;> simp_all <;> grind

/-- Inactive padding permits the physical wrap to the first active row only
at the last row, where the transition selector vanishes. -/
theorem padding_constraints (nxt : Nat→Fp) (first last trans : Fp)
    (hn:trans=0 ∨ nxt act=0) (e : Expr) (hm:e∈constraints) :
    e.evalWith (env (fun _=>0) nxt first last trans)=0 := by
  have hzero : Fp.ofNat 0 = (0:Fp) := rfl
  have hone : Fp.ofNat 1 = (1:Fp) := rfl
  rcases List.mem_append.mp hm with hm|hm
  · obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hm
    simp only [ZkFormal.Chacha.Table.boolC,sub,k,ZkFormal.Chacha.Table.E.c,Expr.evalWith,env,
      Bool.false_eq_true,ite_false,hone]
    grind
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [Expr.evalWith,env,adjacent,delta,addr,nextAddr,notE,sub,k,c,n,
      Bool.false_eq_true,ite_false,ite_true,hone]
    all_goals rcases hn with hn|hn <;> grind

end ZkFormal.NearV3.Candidates.ProcPriorBoundary
