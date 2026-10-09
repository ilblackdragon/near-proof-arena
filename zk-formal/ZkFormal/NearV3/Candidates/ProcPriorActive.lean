import ZkFormal.NearV3.Candidates.ProcPriorCells
namespace ZkFormal.NearV3.Candidates.ProcPriorActive
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Chacha.Table.E
open ProcPriorMemoryTable ProcPriorCells

def pairEnv (a b : ProcPriorRows.Row) (t : Nat) (first : Fp) (ns : Bool) (ni : Fp) : Env Fp :=
  env (cell a t (decide (a.event.link=b.event.link))
    (Fp.ofNat b.event.link-Fp.ofNat a.event.link)⁻¹) (cell b t ns ni) first 0 1

/-- Ordinary adjacent-row semantics imply every memory constraint. -/
theorem pair_constraints (a b : ProcPriorRows.Row) (t : Nat) (first : Fp) (ns : Bool) (ni : Fp)
    (ha:a.event.link<4096) (hb:b.event.link<4096)
    (hf:first=0 ∨ a.before=ProcPriorCarry.zero)
    (hq:a.event.query=true → a.before=ProcPriorValues.value a.event)
    (hn:b.before=if a.event.link=b.event.link then ProcPriorValues.value a.event else ProcPriorCarry.zero)
    (he:a.event.query=true → a.event.link≠b.event.link)
    (e : Expr) (hm:e∈constraints) : e.evalWith (pairEnv a b t first ns ni)=0 := by
  have hone : Fp.ofNat 1 = (1:Fp) := rfl
  have hzero : Fp.ofNat 0 = (0:Fp) := rfl
  have hd:=delta_inverse a.event.link b.event.link ha hb
  have hdz:=link_delta a.event.link b.event.link ha hb
  rcases List.mem_append.mp hm with hm|hm
  · obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hm
    exact active_boolean a t _ _ _ first 0 1 c hc
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [Expr.evalWith,pairEnv,env,cell,adjacent,delta,addr,nextAddr,
      notE,sub,k,c,n,act,tau,link,query,lo,hi,beforeLo,beforeHi,same,inverse,
      Bool.false_eq_true,ite_false,ite_true,hone]
    all_goals try grind
    all_goals by_cases hk:a.event.link=b.event.link
    all_goals cases hquery:a.event.query
    all_goals simp [bit,hk,hquery,ProcPriorValues.value,ProcPriorCarry.zero] at *
    all_goals try grind
    all_goals rcases hf with hf|hf <;> simp_all <;> grind

end ZkFormal.NearV3.Candidates.ProcPriorActive
