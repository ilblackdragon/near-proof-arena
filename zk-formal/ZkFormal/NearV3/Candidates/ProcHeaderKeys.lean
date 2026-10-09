import ZkFormal.NearV3.Candidates.ProcHeader
namespace ZkFormal.NearV3.Candidates.ProcHeaderKeys
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ZkFormal.Chacha.Table.E

theorem key_to_key (R : Run) (i j : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c,tr.cell t r c=Fp.ofNat ((keyV R i).cell c))
    (hn : ∀ c,tr.cell t ((r+1)%tr.height t) c=Fp.ofNat ((keyV R j).cell c)) :
    ∀ e ∈ Proc.cHdr,e.eval tr t r pub=0 := by
  simp only [Proc.cHdr,List.forall_mem_append,List.forall_mem_cons,List.forall_mem_nil,List.forall_mem_map,
    Proc.roundCols,Proc.instCols,List.forall_mem_cons,List.forall_mem_nil]
  simp [Proc.mul3,Proc.notE,Proc.gB,Proc.gR,sub,smul,c,n,k,Expr.eval,Expr.evalWith,rowEnv,hc,hn,
    PV.cell,Proc.kH,Proc.kE,Proc.kK,Proc.T,Proc.Tq,Proc.kq,Proc.kend,Proc.Kq,Proc.K,Proc.zq,Proc.z,
    Proc.zk,Proc.iK,Proc.Lr,Proc.x,Proc.kl,Proc.le,Proc.tau,keyV,zeroV,
    ProcEntryScalar.flag_cast]
  have cast_eq (a : Nat) : Fp.ofNat a = (a : Fp) := rfl
  simp only [cast_eq]
  grind

def Initial (rd : RoundD) : Prop := rd.kst=0 ∧ rd.T=T0 ∧ rd.Kq=Proc.KSENT ∧ rd.zq=0

theorem key_to_header (R : Run) (rd : RoundD) (hinit : Initial rd)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c,tr.cell t r c=Fp.ofNat ((keyV R 15).cell c))
    (hn : ∀ c,tr.cell t ((r+1)%tr.height t) c=Fp.ofNat ((hdrV R rd).cell c)) :
    ∀ e ∈ Proc.cHdr,e.eval tr t r pub=0 := by
  rcases hinit with ⟨hk,ht,hK,hz⟩
  simp only [Proc.cHdr,List.forall_mem_append,List.forall_mem_cons,List.forall_mem_nil,List.forall_mem_map,
    Proc.roundCols,Proc.instCols,List.forall_mem_cons,List.forall_mem_nil]
  simp [Proc.mul3,Proc.notE,Proc.gB,Proc.gR,sub,smul,c,n,k,Expr.eval,Expr.evalWith,rowEnv,hc,hn,
    PV.cell,Proc.kH,Proc.kE,Proc.kK,Proc.T,Proc.Tq,Proc.kq,Proc.kend,Proc.Kq,Proc.K,Proc.zq,Proc.z,
    Proc.zk,Proc.iK,Proc.Lr,Proc.x,Proc.kl,Proc.le,Proc.tau,keyV,hdrV,baseV,zeroV,
    ProcEntryScalar.flag_cast,hk,ht,hK,hz]
  have cast_eq (a : Nat) : Fp.ofNat a = (a : Fp) := rfl
  simp only [cast_eq]
  grind

theorem key_to_tail (R : Run) (hempty : R.rounds=[])
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c,tr.cell t r c=Fp.ofNat ((keyV R 15).cell c))
    (hn : ∀ c,tr.cell t ((r+1)%tr.height t) c=Fp.ofNat ((tailV R).cell c)) :
    ∀ e ∈ Proc.cHdr,e.eval tr t r pub=0 := by
  simp only [Proc.cHdr,List.forall_mem_append,List.forall_mem_cons,List.forall_mem_nil,List.forall_mem_map,
    Proc.roundCols,Proc.instCols,List.forall_mem_cons,List.forall_mem_nil]
  simp [Proc.mul3,Proc.notE,Proc.gB,Proc.gR,sub,smul,c,n,k,Expr.eval,Expr.evalWith,rowEnv,hc,hn,
    PV.cell,Proc.kH,Proc.kE,Proc.kK,Proc.T,Proc.Tq,Proc.kq,Proc.kend,Proc.Kq,Proc.K,Proc.zq,Proc.z,
    Proc.zk,Proc.iK,Proc.Lr,Proc.x,Proc.kl,Proc.le,Proc.tau,keyV,tailV,zeroV,
    ProcEntryScalar.flag_cast,hempty]
  have cast_eq (a : Nat) : Fp.ofNat a = (a : Fp) := rfl
  simp only [cast_eq]
  grind
end ZkFormal.NearV3.Candidates.ProcHeaderKeys
