import ZkFormal.NearV3.Candidates.ProcEntryScalar
namespace ZkFormal.NearV3.Candidates.ProcEntryAdjacent
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ZkFormal.Chacha.Table.E

theorem adjacent_entry (R : Run) (rd : RoundD) (es : Array Entry) (i : Nat)
    (hlen : rd.Lr=es.size) (hx : es[i]!.x=i)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c,tr.cell t r c=Fp.ofNat ((entV R rd es i).cell c))
    (hnx : i+1≠es.size → tr.cell t ((r+1)%tr.height t) Proc.x=Fp.ofNat (i+1))
    (hnt : i+1≠es.size → tr.cell t ((r+1)%tr.height t) Proc.ts=Fp.ofNat es[i+1]!.ts) :
    ∀ e ∈ Proc.cEnt.take 3 ++ Proc.cEnt.drop 14,e.eval tr t r pub=0 := by
  simp only [Proc.cEnt,List.drop,List.take,List.forall_mem_append,List.forall_mem_cons,List.forall_mem_nil]
  simp [Proc.mul3,Proc.notE,sub,smul,c,n,k,Expr.eval,Expr.evalWith,rowEnv,hc,
    PV.cell,Proc.kE,Proc.le,Proc.x,Proc.Lr,Proc.cx,Proc.T,Proc.ts,
    entV,baseV,zeroV,ProcEntryScalar.flag_cast,hx,hlen]
  have cast_eq (a : Nat) : Fp.ofNat a = (a : Fp) := rfl
  simp only [Proc.x,Proc.ts] at hnx hnt
  by_cases hi : i+1=es.size
  · simp only [if_pos hi]
    rw [←hi]
    simp only [cast_eq]
    grind
  · simp [hi,hnx hi,hnt hi,cast_eq]; grind

theorem entry_constraints (R : Run) (rd : RoundD) (es : Array Entry) (i : Nat)
    (hok : ProcEntryScalar.EntryOk rd.z es[i]!)
    (hlen : rd.Lr=es.size) (hx : es[i]!.x=i)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c,tr.cell t r c=Fp.ofNat ((entV R rd es i).cell c))
    (hnx : i+1≠es.size → tr.cell t ((r+1)%tr.height t) Proc.x=Fp.ofNat (i+1))
    (hnt : i+1≠es.size → tr.cell t ((r+1)%tr.height t) Proc.ts=Fp.ofNat es[i+1]!.ts) :
    ∀ e ∈ Proc.cEnt,e.eval tr t r pub=0 := by
  have hp : Proc.cEnt = Proc.cEnt.take 3 ++ (Proc.cEnt.drop 3).take 11 ++ Proc.cEnt.drop 14 := rfl
  have ha := adjacent_entry R rd es i hlen hx tr t r pub hc hnx hnt
  have hs := ProcEntryScalar.local_entry R rd es i hok tr t r pub hc
  rw [hp]
  simp only [List.forall_mem_append] at ha ⊢
  exact ⟨⟨ha.1,hs⟩,ha.2⟩
end ZkFormal.NearV3.Candidates.ProcEntryAdjacent
