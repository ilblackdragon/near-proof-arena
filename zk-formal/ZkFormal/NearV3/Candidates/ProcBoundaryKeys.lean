import ZkFormal.NearV3.Candidates.ProcBoundaryLocal
namespace ZkFormal.NearV3.Candidates.ProcBoundaryKeys
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ZkFormal.Chacha.Table.E
open ProcBoundaryRepair

/-- An empty processing instance may be followed by a new independently bound seed. -/
theorem key_to_key (R S : Run) (ht : S.tau=R.tau+1)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c,tr.cell t r c=Fp.ofNat ((keyV R 15).cell c))
    (hn : ∀ c,tr.cell t ((r+1)%tr.height t) c=Fp.ofNat ((keyV S 0).cell c)) :
    ∀ e∈cKey,e.eval tr t r pub=0 := by
  simp only [cKey,Proc.cKey,List.take,List.drop,List.forall_mem_append,List.forall_mem_cons,
    List.forall_mem_nil,List.forall_mem_map]
  simp [rotation,Proc.mul3,Proc.notE,Proc.gB,sub,smul,c,n,k,Expr.eval,Expr.evalWith,rowEnv,hc,hn,
    PV.cell,Proc.kK,Proc.kl,Proc.kc,Proc.ikc,Proc.tau,Proc.colL,Proc.sbIn,Proc.sbOut,
    Proc.kq,Proc.Tq,Proc.Kq,Proc.zq,Proc.kH,Proc.kE,Proc.le,keyV,zeroV,b2n,ht]
  have cast_eq (a : Nat) : Fp.ofNat a = (a : Fp) := rfl
  simp only [cast_eq]
  simp only [keyLimb]
  repeat constructor
  all_goals first | grind | (intro i hi; grind)
end ZkFormal.NearV3.Candidates.ProcBoundaryKeys
