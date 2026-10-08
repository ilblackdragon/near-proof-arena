import ZkFormal.NearV3.Candidates.ProcBits
import ZkFormal.NearV3.Candidates.SchedField
namespace ZkFormal.NearV3.Candidates.ProcEntryScalar
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ZkFormal.Chacha.Table.E

/-- Ordinary replay facts; these concern native integers and Boolean decisions. -/
def EntryOk (z : Nat) (e : Entry) : Prop :=
  e.rem < P ∧ e.alOut < P ∧ e.ok = (e.cS && e.cR && e.cL) ∧
  e.zn = if e.alOut = 0 then z+1 else 0

theorem flag_cast (b : Bool) : Fp.ofNat (b2n b) = if b then 1 else 0 := by
  cases b <;> rfl

theorem inverse (a : Nat) (ha : a<P) :
    Fp.ofNat a * Fp.ofNat (finv a) = if a=0 then 0 else 1 := by
  simpa [Nat.mod_eq_of_lt ha] using SchedField.inverse_product a

theorem local_entry (R : Run) (rd : RoundD) (es : Array Entry) (i : Nat)
    (hok : EntryOk rd.z es[i]!) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c,tr.cell t r c=Fp.ofNat ((entV R rd es i).cell c)) :
    ∀ e ∈ (Proc.cEnt.drop 3).take 11,e.eval tr t r pub=0 := by
  rcases hok with ⟨hr,ha,ho,hz⟩
  have hir := inverse es[i]!.rem hr
  have hia := inverse es[i]!.alOut ha
  simp only [Proc.cEnt,List.drop,List.take,List.forall_mem_cons,List.forall_mem_nil]
  simp [Proc.mul3,Proc.notE,sub,smul,c,n,k,Expr.eval,Expr.evalWith,rowEnv,hc,
    PV.cell,Proc.kE,Proc.lastf,Proc.rem,Proc.irem,Proc.ok,Proc.cS,Proc.cR,Proc.cL,
    Proc.za,Proc.alOut,Proc.ia,Proc.zn,Proc.z,Proc.pm,Proc.cg,Proc.kH,Proc.zk,
    Proc.cx,Proc.Kq,Proc.cy,Proc.K,Proc.ts,entV,baseV,zeroV,flag_cast,ho,hz]
  have cast_eq (a : Nat) : Fp.ofNat a = (a : Fp) := rfl
  by_cases hrem : es[i]!.rem=0 <;> by_cases hal : es[i]!.alOut=0 <;>
    by_cases hs : es[i]!.cS=true <;> by_cases hrr : es[i]!.cR=true <;>
    by_cases hl : es[i]!.cL=true <;>
    simp_all [cast_eq] <;> grind
/-- The entry constructor used by the replay loop computes both decisions. -/
theorem replay_entry (z : Nat) (e : Entry) (hr : e.rem<P) (ha : e.alOut<P) :
    EntryOk z { e with ok := (e.cS && e.cR && e.cL), zn := if e.alOut=0 then z+1 else 0 } := by
  exact ⟨hr,ha,rfl,rfl⟩
end ZkFormal.NearV3.Candidates.ProcEntryScalar
