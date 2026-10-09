import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordStep
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecRecordTotal
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcPriorCodecRecordStep

def endAllowance (I : Input) (R : Run) (present : Bool) (kk cb : Nat) : Nat :=
  let a0s := if present then (ProcActualInput.allowances I.ids I.prev)[kk]! else 0
  let a1 := if a0s≥16777216 then Codec.MA else
    if cb=1 then Codec.MA else a0s%16777216+I.p.maxShardBandwidth/R.n
  a1-b2n I.allowed[kk]!*I.p.base

def Forward (R : Run) (gb : Array Nat) (fwd : List (Nat×Nat)) (kk : Nat) : Prop :=
  ((fwd.find? (·.1==kk)).map (·.2)).getD 0 ≤ (R.segs.getD kk default).wfin+gb[kk]!

set_option maxHeartbeats 2000000 in
theorem step_success (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (kk f gg : Nat) (s : State)
    (ha : f=2 → gg=7 → endAllowance I R present kk s.2.2.2.2.2=R.a2[kk]!)
    (hfwd : f=2 → gg=7 → R.tau=0 → Forward R gb fwd kk) :
    ∃out,step I R present gb fwd inst kk f gg s=.ok (.yield out) := by
  by_cases hf : f=2
  · subst f
    by_cases hg : gg=7
    · subst gg
      have he := ha rfl rfl
      have hf := hfwd rfl rfl
      unfold endAllowance at he
      by_cases ht : R.tau=0
      · have hfw := hf ht
        unfold Forward at hfw
        simp only [List.getD_eq_getElem?_getD] at hfw
        simp [step,he,ht,hfw,check,pure,Except.pure,bind,Except.bind] <;>
          repeat first | split | exact ⟨_,_,_,_,_,_,rfl⟩
      · simp [step,he,ht,check,pure,Except.pure,bind,Except.bind] <;>
          repeat first | split | exact ⟨_,_,_,_,_,_,rfl⟩
    · by_cases h2 : gg=2 <;> by_cases hlow : gg<3 <;>
        by_cases hge : gg≥2 <;> by_cases hhigh : gg≥3
      all_goals simp [step,hg,h2,hlow,hge,hhigh,check,pure,Except.pure,bind,Except.bind] <;>
        repeat first | split | exact ⟨_,_,_,_,_,_,rfl⟩
  · simp [step,hf,check,pure,Except.pure,bind,Except.bind] <;>
      repeat first | split | exact ⟨_,_,_,_,_,_,rfl⟩
end ZkFormal.NearV3.Candidates.ProcPriorCodecRecordTotal
