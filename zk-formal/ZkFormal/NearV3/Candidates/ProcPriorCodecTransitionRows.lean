import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordZeroRows
import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordIndexRows
import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordKind
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecTransitionRows
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecStepRows ProcPriorCodecRecordStep ProcPriorCodecExtra ProcPriorCodecNativeHash

def Shape (R : Run) (k f g : Nat) (a : Array Nat) : Prop :=
  a[kR]! =1 ∧ a[Codec.g]! =g ∧ a[e7]! =(if g=7 then 1 else 0) ∧
  a[fS]! =(if f=0 then 1 else 0) ∧ a[fR]! =(if f=1 then 1 else 0) ∧
  a[fA]! =(if f=2 then 1 else 0) ∧ a[kidx]! =k ∧
  a[ekl]! =(if k+1=R.n*R.n then 1 else 0) ∧
  a[rend]! =(if f=2 then 1 else 0)*(if g=7 then 1 else 0)

theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vid k f g : Nat) (s out : State)
    (hk : k<R.n*R.n) (hf : f<3) (hg : g<8)
    (h : step I R present gb fwd (instanceCells I R present vid) k f g s=.ok (.yield out)) :
    ∃a,out.1=s.1.push a ∧ Shape R k f g a := by
  obtain ⟨tail,ht,hr⟩ := successful_row I R present gb fwd (instanceCells I R present vid) k f g s out hf hg h
  let a := record I R present (instanceCells I R present vid)
    (baseExtra R.n k f g (b2n I.allowed[k]!) gb[k]!++tail) k f g
  have ha : out.1=s.1.push a := hr
  have hflags : a[act]! =1 ∧ a[kR]! =1 ∧ a[kH]! =0 ∧ a[kZ]! =0 ∧ a[kA]! =0 ∧
      a[kF]! =0 ∧ a[ehp]! =0 ∧ a[fS]! =(if f=0 then 1 else 0) ∧
      a[fR]! =(if f=1 then 1 else 0) ∧ a[fA]! =(if f=2 then 1 else 0) := by
    exact ProcPriorCodecRecordKind.flags I R present vid k f g _ _ _ _ _ tail ht
  have hS : a[fS]! =(if f=0 then 1 else 0) := hflags.2.2.2.2.2.2.2.1
  have hFR : a[fR]! =(if f=1 then 1 else 0) := hflags.2.2.2.2.2.2.2.2.1
  obtain ⟨b,hb,_,hR,_,_,_,hFA,hg',_,h7,hk',_,_,hkl,_⟩ := ProcPriorCodecRecordZeroRows.actual I R present gb fwd vid k f g s out hf hg h
  have he : b=a := Array.push_inj_right.mp (hb.symm.trans ha)
  subst b
  obtain ⟨b,hb,_,_,_,hend,_⟩ := ProcPriorCodecRecordIndexRows.actual I R present gb fwd vid k f g s out hk hf hg h
  have he : b=a := Array.push_inj_right.mp (hb.symm.trans ha)
  subst b
  refine ⟨a,ha,hR,hg',h7,hS,hFR,hFA,hk',hkl,?_⟩
  rw [hend,hFA,h7]
end ZkFormal.NearV3.Candidates.ProcPriorCodecTransitionRows
