import ZkFormal.NearV3.Candidates.ProcPriorRecordWordIdentity
import ZkFormal.NearV3.Candidates.ProcPriorRecordByteMessage
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordWordLayout
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRecordTable
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}

def base (tr:Trace Fp) (t r:Nat):Nat:=8*(cv tr t r receiver+2*cv tr t r amount)

theorem layout (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (hf:cv tr t r firstLimb=1) (j:Nat) (hj:j<3) :
    r+j<tr.height t ∧ cv tr t (r+j) (ProcPriorVertical4Linear.stage 3)=1 ∧
      cv tr t (r+j) sender+cv tr t (r+j) receiver+cv tr t (r+j) amount=1 ∧
      ProcPriorRecordByteMessage.offsetNat tr t (r+j)=base tr t r+3*j ∧
      (j<2→cv tr t (r+j) topLimb=0) := by
  obtain ⟨hr1,hs1,_,hm1,hfields1⟩:=ProcPriorRecordWordTraversal.limb_next hL hr hs firstLimb midLimb (by simp) hf
  obtain ⟨hr2,hs2,_,ht2,hfields2⟩:=ProcPriorRecordWordTraversal.limb_next hL hr1 hs1 midLimb topLimb (by simp) hm1
  simp only [Nat.add_assoc,Nat.reduceAdd] at hr2 hs2 ht2 hfields2
  have facts (q:Nat) (hq:q<tr.height t) (hsq:cv tr t q (ProcPriorVertical4Linear.stage 3)=1):
      cv tr t q firstLimb+cv tr t q midLimb+cv tr t q topLimb=
        cv tr t q sender+cv tr t q receiver+cv tr t q amount ∧
      cv tr t q sender+cv tr t q receiver+cv tr t q amount≤1:=by
    have hb:=ProcPriorRecordGeometry.words_bound hL hq hsq
    have ha:=ProcPriorRecordSound.flag hL hq hsq act (by simp)
    exact ⟨ProcPriorRecordGeometry.limbs_eq hL hq hsq,by omega⟩
  have f0:=facts r hr hs
  have f1:=facts (r+1) hr1 hs1
  have f2:=facts (r+2) hr2 hs2
  have a1:=hfields1 receiver (by simp)
  have b1:=hfields1 amount (by simp)
  have a2:=(hfields2 receiver (by simp)).trans a1
  have b2:=(hfields2 amount (by simp)).trans b1
  have casesj:j=0 ∨ j=1 ∨ j=2:=by omega
  rcases casesj with rfl|rfl|rfl
  · simp only [Nat.add_zero,Nat.mul_zero]
    refine ⟨hr,hs,by omega,?_,by omega⟩
    unfold ProcPriorRecordByteMessage.offsetNat base
    omega
  · refine ⟨hr1,hs1,by omega,?_,by omega⟩
    unfold ProcPriorRecordByteMessage.offsetNat base
    rw [a1,b1]
    omega
  · refine ⟨hr2,hs2,by omega,?_,by omega⟩
    unfold ProcPriorRecordByteMessage.offsetNat base
    rw [a2,b2]
    omega
end ZkFormal.NearV3.Candidates.ProcPriorRecordWordLayout
