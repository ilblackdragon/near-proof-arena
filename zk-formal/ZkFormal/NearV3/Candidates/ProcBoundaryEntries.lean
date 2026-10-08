import ZkFormal.NearV3.Candidates.ProcBoundaryKeys
import ZkFormal.NearV3.Candidates.ProcNonKeyEval
namespace ZkFormal.NearV3.Candidates.ProcBoundaryEntries
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ZkFormal.Chacha.Table.E
open ProcBoundaryRepair

theorem entry_to_key (R S : Run) (rd : RoundD) (es : Array Entry) (i : Nat)
    (hi : i+1=es.size) (ht : S.tau=R.tau+1)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c,tr.cell t r c=Fp.ofNat ((entV R rd es i).cell c))
    (hn : ∀ c,tr.cell t ((r+1)%tr.height t) c=Fp.ofNat ((keyV S 0).cell c)) :
    ∀ e∈cKey,e.eval tr t r pub=0 := by
  simp only [cKey,Proc.cKey,List.take,List.drop,List.forall_mem_append,List.forall_mem_cons,
    List.forall_mem_nil,List.forall_mem_map]
  simp [rotation,Proc.mul3,Proc.notE,Proc.gB,sub,smul,c,n,k,Expr.eval,Expr.evalWith,rowEnv,hc,hn,
    PV.cell,Proc.kK,Proc.kl,Proc.kc,Proc.ikc,Proc.tau,Proc.colL,Proc.sbIn,Proc.sbOut,
    Proc.kq,Proc.Tq,Proc.Kq,Proc.zq,Proc.kH,Proc.kE,Proc.le,keyV,entV,baseV,zeroV,b2n,hi,ht]
  have cast_eq (a : Nat) : Fp.ofNat a = (a : Fp) := rfl
  have hinv := ProcNonKeyEval.pad_inverse
  simp only [cast_eq] at hinv ⊢
  repeat apply And.intro
  all_goals first | grind | (intro j hj; grind)

theorem header_entry_to_key (R S : Run) (rd : RoundD) (es : Array Entry) (i : Nat)
    (hi : i+1=es.size) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c,tr.cell t r c=Fp.ofNat ((entV R rd es i).cell c))
    (hn : ∀ c,tr.cell t ((r+1)%tr.height t) c=Fp.ofNat ((keyV S 0).cell c)) :
    ∀ e∈Proc.cHdr,e.eval tr t r pub=0 := by
  simp only [Proc.cHdr,List.forall_mem_append,List.forall_mem_cons,List.forall_mem_nil,List.forall_mem_map,
    Proc.roundCols,Proc.instCols,List.forall_mem_cons,List.forall_mem_nil]
  simp [Proc.mul3,Proc.notE,Proc.gB,Proc.gR,sub,smul,c,n,k,Expr.eval,Expr.evalWith,rowEnv,hc,hn,
    PV.cell,Proc.kH,Proc.kE,Proc.kK,Proc.T,Proc.Tq,Proc.kq,Proc.kend,Proc.Kq,Proc.K,Proc.zq,Proc.z,
    Proc.zk,Proc.iK,Proc.Lr,Proc.x,Proc.kl,Proc.le,Proc.tau,keyV,entV,baseV,zeroV,b2n,hi]
  have cast_eq (a : Nat) : Fp.ofNat a = (a : Fp) := rfl
  simp only [cast_eq]
  repeat apply And.intro <;> grind

theorem header_key_to_key (R S : Run) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c,tr.cell t r c=Fp.ofNat ((keyV R 15).cell c))
    (hn : ∀ c,tr.cell t ((r+1)%tr.height t) c=Fp.ofNat ((keyV S 0).cell c)) :
    ∀ e∈Proc.cHdr,e.eval tr t r pub=0 := by
  simp only [Proc.cHdr,List.forall_mem_append,List.forall_mem_cons,List.forall_mem_nil,List.forall_mem_map,
    Proc.roundCols,Proc.instCols,List.forall_mem_cons,List.forall_mem_nil]
  simp [Proc.mul3,Proc.notE,Proc.gB,Proc.gR,sub,smul,c,n,k,Expr.eval,Expr.evalWith,rowEnv,hc,hn,
    PV.cell,Proc.kH,Proc.kE,Proc.kK,Proc.T,Proc.Tq,Proc.kq,Proc.kend,Proc.Kq,Proc.K,Proc.zq,Proc.z,
    Proc.zk,Proc.iK,Proc.Lr,Proc.x,Proc.kl,Proc.le,Proc.tau,keyV,zeroV,b2n]
  have cast_eq (a : Nat) : Fp.ofNat a = (a : Fp) := rfl
  simp only [cast_eq]
  repeat apply And.intro <;> grind
end ZkFormal.NearV3.Candidates.ProcBoundaryEntries
