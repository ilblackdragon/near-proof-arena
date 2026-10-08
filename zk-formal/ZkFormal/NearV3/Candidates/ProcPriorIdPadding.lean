import ZkFormal.NearV3.Candidates.ProcPriorIdBoundary
namespace ZkFormal.NearV3.Candidates.ProcPriorIdPadding
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha.Table.E
open ProcPriorIdTable ProcPriorCells

theorem padding_constraints (nxt : Nat→Fp) (fi la tr : Fp)
    (hn:tr=0 ∨ nxt act=0) (e : Expr) (he:e∈constraints) :
    e.evalWith (env (fun _=>0) nxt fi la tr)=0 := by
  have hzm (x:Fp):(0:Fp)*x=0:=by grind
  have hmz (x:Fp):x*(0:Fp)=0:=by grind
  have ha (x:Fp):(0:Fp)+x=x:=by grind
  have haz (x:Fp):x+(0:Fp)=x:=by grind
  have hnz:-(0:Fp)=0:=by grind
  have hone:Fp.ofNat 1=(1:Fp):=rfl
  have hf:constraints.map (·.evalWith (env (fun _=>0) nxt fi la tr))=List.replicate constraints.length (0:Fp) := by
    rcases hn with hn|hn
    all_goals simp [constraints,eqs,dTop,dMid,dLo,top,adjacent,ZkFormal.Chacha.Table.boolC,notE,sub,k,c,n,
      Expr.evalWith,env,hzm,hmz,ha,haz,hnz,hone,hn,List.replicate]
  have hm:e.evalWith (env (fun _=>0) nxt fi la tr)∈constraints.map (·.evalWith (env (fun _=>0) nxt fi la tr)):=List.mem_map.mpr ⟨e,he,rfl⟩
  rw [hf] at hm
  exact (List.mem_replicate.mp hm).2

end ZkFormal.NearV3.Candidates.ProcPriorIdPadding
