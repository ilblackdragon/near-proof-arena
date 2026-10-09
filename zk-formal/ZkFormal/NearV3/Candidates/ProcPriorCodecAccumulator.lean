import ZkFormal.NearV3.Candidates.ProcPriorCodecCarryTotal
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecAccumulator
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcPriorCodecRecordStep

def preByte (R : Run) (present : Bool) (k g : Nat) : Nat :=
  if ¬present then 0 else (Array.replicate (R.n*R.n) 0)[k]! /256^g%256

def postByte (R : Run) (k g : Nat) : Nat :=
  if g<3 then (R.segs.getD k default).vfin/256^g%256 else 0

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000 in
theorem byte_accumulators (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (k g : Nat) (s out : State) (hg : g<8)
    (h : step I R present gb fwd inst k 2 g s=.ok (.yield out)) :
    out.2.2.1=(if g<3 then s.2.2.1+256^g*preByte R present k g else s.2.2.1) ∧
    out.2.2.2.1=(if g<3 then s.2.2.2.1+256^g*postByte R k g else s.2.2.2.1) ∧
    out.2.2.2.2.1=(if 3≤g ∧ preByte R present k g≠0 then 1 else s.2.2.2.2.1) := by
  have hh : g=0 ∨ g=1 ∨ g=2 ∨ g=3 ∨ g=4 ∨ g=5 ∨ g=6 ∨ g=7 := by omega
  rcases hh with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [step,check,bind,Except.bind,pure,Except.pure] at h
  all_goals repeat first | split at h | cases h
  all_goals repeat first | split at h | cases h
  all_goals try subst out
  all_goals simp_all (config := {maxSteps := 100000}) [preByte,postByte]
  all_goals subst out
  all_goals simp_all
theorem preByte_zero (R : Run) (present : Bool) (k g : Nat) (hk : k<R.n*R.n) :
    preByte R present k g=0 := by
  simp [preByte, getElem!_pos, hk]

theorem byte_native_accumulators (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (k g : Nat) (s out : State) (hg : g<8)
    (hk : k<R.n*R.n)
    (h : step I R present gb fwd inst k 2 g s=.ok (.yield out)) :
    out.2.2.1=s.2.2.1 ∧
    out.2.2.2.1=s.2.2.2.1+256^g*postByte R k g ∧
    out.2.2.2.2.1=s.2.2.2.2.1 := by
  have hh := byte_accumulators I R present gb fwd inst k g s out hg h
  rw [preByte_zero R present k g hk] at hh
  by_cases hg3 : g<3
  · simpa [hg3] using hh
  · simpa [hg3,postByte] using hh
end ZkFormal.NearV3.Candidates.ProcPriorCodecAccumulator
