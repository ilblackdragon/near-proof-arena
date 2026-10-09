import ZkFormal.NearV3.Candidates.ProcPriorCodecTransitionRows
import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordTwoRows
import ZkFormal.NearV3.Candidates.ProcPriorCodecCarryRows
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordPosition
namespace ZkFormal.NearV3.Candidates.ProcCodecPriorReadCells
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecRecordStep ProcPriorCodecNativeHash

def prior (I : Input) (present : Bool) (k : Nat) : Nat :=
  if present then (ProcActualInput.allowances I.ids I.prev)[k]! else 0

theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vidV k f g : Nat) (s out : State)
    (hk : k<R.n*R.n) (hf : f<3) (hg : g<8)
    (h : step I R present gb fwd (instanceCells I R present vidV) k f g s=.ok (.yield out)) :
    ∃a,out.1=s.1.push a ∧ a[fA]! =(if f=2 then 1 else 0) ∧
      a[e2]! =(if f=2 ∧ g=2 then 1 else 0) ∧ a[kidx]! =k ∧
      (f=2 ∧ g=2 → a[apR]! =prior I present k%16777216 ∧
        a[bigR]! =(if 16777216≤prior I present k then 1 else 0)) := by
  obtain ⟨a,ha,hs⟩:=ProcPriorCodecTransitionRows.actual I R present gb fwd vidV k f g s out hk hf hg h
  obtain ⟨b,hb,_,h2⟩:=ProcPriorCodecRecordTwoRows.actual I R present gb fwd vidV k f g s out hk hf hg h
  have he:b=a:=Array.push_inj_right.mp (hb.symm.trans ha)
  subst b
  refine ⟨a,ha,hs.2.2.2.2.2.1,h2,hs.2.2.2.2.2.2.1,?_⟩
  rintro ⟨rfl,rfl⟩
  obtain ⟨b,hb,hap,hbig,_⟩:=ProcPriorCodecCarryRows.cells I R present gb fwd
    (instanceCells I R present vidV) k 2 s out (by decide) hk (by decide) h
  have he:b=a:=Array.push_inj_right.mp (hb.symm.trans ha)
  subst b
  exact ⟨hap,hbig⟩

theorem position (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (k f g : Nat) (hk : k<R.n*R.n) (hf : f<3) (hg : g<8) :
    let a:=out.rows[5+24*k+8*f+g]!
    a[fA]! =(if f=2 then 1 else 0) ∧ a[e2]! =(if f=2 ∧ g=2 then 1 else 0) ∧
    a[kidx]! =k ∧ (f=2 ∧ g=2 → a[apR]! =prior I present k%16777216 ∧
        a[bigR]! =(if 16777216≤prior I present k then 1 else 0)) := by
  apply ProcCodecGeneratedRecordPosition.property I R present vidV gb fwd out h k f g hk hf hg
    (fun a=>a[fA]! =(if f=2 then 1 else 0) ∧ a[e2]! =(if f=2 ∧ g=2 then 1 else 0) ∧
      a[kidx]! =k ∧ (f=2 ∧ g=2 → a[apR]! =prior I present k%16777216 ∧
        a[bigR]! =(if 16777216≤prior I present k then 1 else 0)))
  intro before after hs
  exact actual I R present gb fwd vidV k f g before after hk hf hg hs
end ZkFormal.NearV3.Candidates.ProcCodecPriorReadCells
