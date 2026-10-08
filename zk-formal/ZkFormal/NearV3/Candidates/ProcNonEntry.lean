import ZkFormal.NearV3.Candidates.ProcEntryScalar
namespace ZkFormal.NearV3.Candidates.ProcNonEntry
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ZkFormal.Chacha.Table.E

/-- Every native row outside the entry stream satisfies the complete entry group. -/
theorem constraints (R : Run) (V : PV)
    (hv : (∃ j,V=keyV R j) ∨ (∃ rd,V=hdrV R rd) ∨ V=tailV R ∨ V=padPV)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c,tr.cell t r c=Fp.ofNat (V.cell c)) :
    ∀ e ∈ Proc.cEnt,e.eval tr t r pub=0 := by
  rcases hv with ⟨j,rfl⟩ | ⟨rd,rfl⟩ | rfl | rfl
  all_goals simp only [Proc.cEnt,List.forall_mem_cons,List.forall_mem_nil]
  all_goals
    simp [Proc.mul3,Proc.notE,sub,smul,c,n,k,Expr.eval,Expr.evalWith,rowEnv,hc,
      PV.cell,Proc.kE,Proc.le,Proc.x,Proc.Lr,Proc.lastf,Proc.rem,Proc.irem,Proc.ok,Proc.cS,Proc.cR,Proc.cL,
      Proc.za,Proc.alOut,Proc.ia,Proc.zn,Proc.z,Proc.pm,Proc.cg,Proc.kH,Proc.zk,
      Proc.cx,Proc.Kq,Proc.cy,Proc.K,Proc.ts,keyV,hdrV,tailV,padPV,baseV,zeroV,
      ProcEntryScalar.flag_cast]
    have cast_eq (a : Nat) : Fp.ofNat a = (a : Fp) := rfl
    simp only [cast_eq]
  case inr.inl =>
    by_cases h : rd.K=0 <;> simp [h] <;> grind
  all_goals grind
end ZkFormal.NearV3.Candidates.ProcNonEntry
