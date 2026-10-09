import ZkFormal.NearV3.Candidates.ProcPriorIdPadding
namespace ZkFormal.NearV3.Candidates.ProcPriorIdBits
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha.Table.E
open ProcPriorIdRows ProcPriorCells ProcPriorIdCells ProcPriorIdTable

theorem active_bits (a : Row) (after : Option Row) (t : Nat) (nxt : Nat→Fp)
    (hn:nxt act=0 ∨ nxt act=1) (fi la tr : Fp) (pb qb rb cb : Nat)
    (i : Interaction) (hi:i∈interactions pb qb rb cb) (e : Expr) (he:e∈i.mult) :
    e.evalWith (env (cells a after t) nxt fi la tr)=0 ∨
    e.evalWith (env (cells a after t) nxt fi la tr)=1 := by
  have hone:Fp.ofNat 1=(1:Fp):=rfl
  change nxt 0=0 ∨ nxt 0=1 at hn
  have hp:=ProcPriorIdCells.bit_bool a.event.isPublic
  have ht:=ProcPriorIdCells.bit_bool (sameTop a after)
  have hm:=ProcPriorIdCells.bit_bool (gateMid a after)
  have hg:=ProcPriorIdCells.bit_bool (gateAll a after && a.event.isPublic && nextPublic after)
  simp only [interactions,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [List.mem_singleton] at he; subst e
  all_goals simp [adjacent,notE,sub,k,c,n,Expr.evalWith,env,cells,act,isPublic,gTop,gMid,gPublic,hone]
  all_goals grind

theorem padding_bits (nxt : Nat→Fp) (fi la tr : Fp) (pb qb rb cb : Nat)
    (i : Interaction) (hi:i∈interactions pb qb rb cb) (e : Expr) (he:e∈i.mult) :
    e.evalWith (env (fun _=>0) nxt fi la tr)=0 := by
  have hone:Fp.ofNat 1=(1:Fp):=rfl
  simp only [interactions,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [List.mem_singleton] at he; subst e
  all_goals simp [adjacent,notE,sub,k,c,n,Expr.evalWith,env,hone]
  all_goals grind

end ZkFormal.NearV3.Candidates.ProcPriorIdBits
