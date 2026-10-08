import ZkFormal.NearV3.Candidates.ProcPriorIdActive
namespace ZkFormal.NearV3.Candidates.ProcPriorIdBoundary
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha.Table.E
open ProcPriorIdRows ProcPriorCells ProcPriorIdCells ProcPriorIdTable ProcPriorIdCarryFields ProcPriorIdGateFields

theorem end_constraints (a : Row) (t : Nat) (fi : Fp)
    (hf:fi=0 ∨ a.before=none) (e : Expr) (he:e∈constraints) :
    e.evalWith (env (cells a none t) (fun _=>0) fi 0 1)=0 := by
  have hone:Fp.ofNat 1=(1:Fp):=rfl
  have htake:=take_field a
  have hmissing:=missing_index a
  have hfirst:fi*bit a.before.isSome=0 ∧ fi*Fp.ofNat (a.before.getD 0)=0 := by
    have hz:Fp.ofNat 0=(0:Fp):=rfl
    rcases hf with hf|hf
    · subst fi; grind
    · simp [hf,bit,hz]; grind
  simp only [constraints,List.mem_append] at he
  rcases he with (((he|he)|he)|he)|he
  · obtain ⟨cc,hc,rfl⟩:=List.mem_map.mp he
    have hc':cc∈[0,6,7,9,10,11,12,16,17,18,19]:=hc
    rcases boolean_cells a none t cc hc' with hv|hv
    all_goals simp [ZkFormal.Chacha.Table.boolC,sub,k,c,Expr.evalWith,env,hv,hone]
    all_goals grind
  all_goals simp only [eqs,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at he
  all_goals first
    | (rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
    | (rcases he with rfl|rfl)
  all_goals
    simp [eqs,dTop,dMid,dLo,top,adjacent,notE,sub,k,c,n,Expr.evalWith,env,cells,
      act,tau,keyLo,keyMid,keyHi,ordinal,isPublic,found,index,ProcPriorIdTable.take,
      eqTop,eqMid,eqLo,invTop,invMid,invLo,gTop,gMid,gAll,gPublic,hone,sameTop,sameMid,sameLo,eqLimb,invLimb,gateMid,gateAll,nextPublic,bit]
  all_goals simp only [bit] at htake hmissing hfirst
  all_goals grind

end ZkFormal.NearV3.Candidates.ProcPriorIdBoundary
