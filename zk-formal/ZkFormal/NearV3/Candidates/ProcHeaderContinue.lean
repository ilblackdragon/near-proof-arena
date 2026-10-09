import ZkFormal.NearV3.Candidates.ProcHeader
namespace ZkFormal.NearV3.Candidates.ProcHeaderContinue
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ZkFormal.Chacha.Table.E

theorem entry_to_entry (R : Run) (rd : RoundD) (es : Array Entry) (i j : Nat)
    (hi : i+1≠es.size) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c,tr.cell t r c=Fp.ofNat ((entV R rd es i).cell c))
    (hn : ∀ c,tr.cell t ((r+1)%tr.height t) c=Fp.ofNat ((entV R rd es j).cell c)) :
    ∀ e ∈ Proc.cHdr,e.eval tr t r pub=0 := by
  simp only [Proc.cHdr,List.forall_mem_append,List.forall_mem_cons,List.forall_mem_nil,List.forall_mem_map,
    Proc.roundCols,Proc.instCols,List.forall_mem_cons,List.forall_mem_nil]
  simp [Proc.mul3,Proc.notE,Proc.gB,Proc.gR,sub,smul,c,n,k,Expr.eval,Expr.evalWith,rowEnv,hc,hn,
    PV.cell,Proc.kH,Proc.kE,Proc.kK,Proc.T,Proc.Tq,Proc.kq,Proc.kend,Proc.Kq,Proc.K,Proc.zq,Proc.z,
    Proc.zk,Proc.iK,Proc.Lr,Proc.x,Proc.kl,Proc.le,Proc.tau,entV,baseV,zeroV,
    ProcEntryScalar.flag_cast,hi]
  have cast_eq (a : Nat) : Fp.ofNat a = (a : Fp) := rfl
  simp only [cast_eq]
  grind

/-- A following round starts from the preceding round's native carry values. -/
def Follows (a b : RoundD) : Prop :=
  b.kst=a.kend ∧ b.T=a.T+a.Lr ∧ b.Kq=a.K ∧ b.zq=a.z

theorem entry_to_header (R : Run) (rd next : RoundD) (es : Array Entry) (i : Nat)
    (hi : i+1=es.size) (hf : Follows rd next)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c,tr.cell t r c=Fp.ofNat ((entV R rd es i).cell c))
    (hn : ∀ c,tr.cell t ((r+1)%tr.height t) c=Fp.ofNat ((hdrV R next).cell c)) :
    ∀ e ∈ Proc.cHdr,e.eval tr t r pub=0 := by
  rcases hf with ⟨hk,ht,hK,hz⟩
  simp only [Proc.cHdr,List.forall_mem_append,List.forall_mem_cons,List.forall_mem_nil,List.forall_mem_map,
    Proc.roundCols,Proc.instCols,List.forall_mem_cons,List.forall_mem_nil]
  simp [Proc.mul3,Proc.notE,Proc.gB,Proc.gR,sub,smul,c,n,k,Expr.eval,Expr.evalWith,rowEnv,hc,hn,
    PV.cell,Proc.kH,Proc.kE,Proc.kK,Proc.T,Proc.Tq,Proc.kq,Proc.kend,Proc.Kq,Proc.K,Proc.zq,Proc.z,
    Proc.zk,Proc.iK,Proc.Lr,Proc.x,Proc.kl,Proc.le,Proc.tau,entV,hdrV,baseV,zeroV,
    ProcEntryScalar.flag_cast,hi,hk,ht,hK,hz]
  have cast_eq (a : Nat) : Fp.ofNat a = (a : Fp) := rfl
  simp only [cast_eq]
  grind
theorem entry_to_tail (R : Run) (rd : RoundD) (es : Array Entry) (i : Nat)
    (hi : i+1=es.size) (hlast : R.rounds.getLast?=some rd)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c,tr.cell t r c=Fp.ofNat ((entV R rd es i).cell c))
    (hn : ∀ c,tr.cell t ((r+1)%tr.height t) c=Fp.ofNat ((tailV R).cell c)) :
    ∀ e ∈ Proc.cHdr,e.eval tr t r pub=0 := by
  simp only [Proc.cHdr,List.forall_mem_append,List.forall_mem_cons,List.forall_mem_nil,List.forall_mem_map,
    Proc.roundCols,Proc.instCols,List.forall_mem_cons,List.forall_mem_nil]
  simp [Proc.mul3,Proc.notE,Proc.gB,Proc.gR,sub,smul,c,n,k,Expr.eval,Expr.evalWith,rowEnv,hc,hn,
    PV.cell,Proc.kH,Proc.kE,Proc.kK,Proc.T,Proc.Tq,Proc.kq,Proc.kend,Proc.Kq,Proc.K,Proc.zq,Proc.z,
    Proc.zk,Proc.iK,Proc.Lr,Proc.x,Proc.kl,Proc.le,Proc.tau,entV,tailV,baseV,zeroV,
    ProcEntryScalar.flag_cast,hi,hlast]
  have cast_eq (a : Nat) : Fp.ofNat a = (a : Fp) := rfl
  simp only [cast_eq]
  grind
end ZkFormal.NearV3.Candidates.ProcHeaderContinue
