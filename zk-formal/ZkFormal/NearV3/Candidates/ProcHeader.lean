import ZkFormal.NearV3.Candidates.ProcEntryScalar
namespace ZkFormal.NearV3.Candidates.ProcHeader
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ZkFormal.Chacha.Table.E

/-- Ordinary round sequencing: zero rounds advance their ordinal; positive keys reset it. -/
def RoundOk (rd : RoundD) : Prop := rd.K<P ∧
  (if rd.K=0 then rd.z=rd.zq+1 else rd.z=0 ∧ rd.zq=0)

theorem header_constraints (R : Run) (rd : RoundD) (es : Array Entry)
    (hr : RoundOk rd) (hx : es[0]!.x=0)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c,tr.cell t r c=Fp.ofNat ((hdrV R rd).cell c))
    (hn : ∀ c,tr.cell t ((r+1)%tr.height t) c=Fp.ofNat ((entV R rd es 0).cell c)) :
    ∀ e ∈ Proc.cHdr,e.eval tr t r pub=0 := by
  rcases hr with ⟨hk,hz⟩
  have hi := ProcEntryScalar.inverse rd.K hk
  simp only [Proc.cHdr,List.forall_mem_append,List.forall_mem_cons,List.forall_mem_nil,List.forall_mem_map,
    Proc.roundCols,Proc.instCols,List.forall_mem_cons,List.forall_mem_nil]
  simp [Proc.mul3,Proc.notE,Proc.gB,Proc.gR,sub,smul,c,n,k,Expr.eval,Expr.evalWith,rowEnv,hc,hn,
    PV.cell,Proc.kH,Proc.kE,Proc.kK,Proc.T,Proc.Tq,Proc.kq,Proc.kend,Proc.Kq,Proc.K,Proc.zq,Proc.z,
    Proc.zk,Proc.iK,Proc.Lr,Proc.x,Proc.kl,Proc.le,Proc.tau,hdrV,entV,baseV,zeroV,
    ProcEntryScalar.flag_cast,hx]
  have cast_eq (a : Nat) : Fp.ofNat a = (a : Fp) := rfl
  by_cases h : rd.K=0
  · simp only [if_pos h] at hz hi ⊢
    simp [h,hz,cast_eq]; grind
  · simp only [if_neg h] at hz hi ⊢
    simp [hz.1,hz.2,cast_eq] at hi ⊢
    grind
end ZkFormal.NearV3.Candidates.ProcHeader
