import ZkFormal.NearV3.Candidates.ProcHeader
import ZkFormal.NearV3.Candidates.ProcKindHeight
namespace ZkFormal.NearV3.Candidates.ProcHeaderPadding
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ZkFormal.Chacha.Table.E
open ProcHeightBits ProcNativeRows ProcKindHeight

theorem quiet (V : PV) (hv : V.kH=0 ∧ V.kE=0 ∧ V.kK=0 ∧ V.kl=0 ∧ V.le=0)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c,tr.cell t r c=Fp.ofNat (V.cell c))
    (hnh : tr.cell t ((r+1)%tr.height t) Proc.kH=0)
    (hne : tr.cell t ((r+1)%tr.height t) Proc.kE=0) :
    ∀ e ∈ Proc.cHdr,e.eval tr t r pub=0 := by
  rcases hv with ⟨hh,he,hk,hl,hle⟩
  simp only [Proc.kH,Proc.kE] at hnh hne
  simp only [Proc.cHdr,List.forall_mem_append,List.forall_mem_cons,List.forall_mem_nil,List.forall_mem_map,
    Proc.roundCols,Proc.instCols,List.forall_mem_cons,List.forall_mem_nil]
  simp [Proc.mul3,Proc.notE,Proc.gB,Proc.gR,sub,smul,c,n,k,Expr.eval,Expr.evalWith,rowEnv,hc,
    PV.cell,Proc.kH,Proc.kE,Proc.kK,Proc.T,Proc.Tq,Proc.kq,Proc.kend,Proc.Kq,Proc.K,Proc.zq,Proc.z,
    Proc.zk,Proc.iK,Proc.Lr,Proc.x,Proc.kl,Proc.le,Proc.tau,hh,he,hk,hl,hle,hnh,hne]
  have cast_eq (a : Nat) : Fp.ofNat a = (a : Fp) := rfl
  simp only [cast_eq]
  repeat constructor <;> grind

theorem suffix_flags (R : Run) (r : Nat) (hr : (procVs R).length≤r) :
    (atRow R r).kH=0 ∧ (atRow R r).kE=0 ∧ (atRow R r).kK=0 ∧
    (atRow R r).kl=0 ∧ (atRow R r).le=0 := by
  rw [atRow,dif_neg (by omega)]
  split <;> simp [tailV,padPV,zeroV]

theorem native_padding (R : Run) (r t : Nat) (pub : List Fp)
    (hrow : (procVs R).length≤r) (hr : r<2^22) :
    ∀ e ∈ Proc.cHdr,e.eval (trace R) t r pub=0 := by
  apply quiet (atRow R r) (suffix_flags R r hrow) (trace R) t r pub (cell_cast R t r)
  all_goals
    change (trace R).cell t ((r+1)%(2^22)) _=0
    by_cases hl : r+1<2^22
    · rw [Nat.mod_eq_of_lt hl,cell_cast]
      have hs := suffix_flags R (r+1) (by omega)
      simp [PV.cell,Proc.kH,Proc.kE,hs.1,hs.2.1]
      rfl
    · have he : r+1=2^22 := by omega
      rw [he,Nat.mod_self,cell_cast,first]
      rfl
end ZkFormal.NearV3.Candidates.ProcHeaderPadding
