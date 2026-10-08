import ZkFormal.NearV3.Candidates.ProcActualRun
import ZkFormal.NearV3.Candidates.ProcPriorCodecGen
import ZkFormal.NearV3.Candidates.ProcPreviousStateRegression
namespace ZkFormal.NearV3.Candidates.ProcActualRunFacts
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
set_option maxHeartbeats 400000 in
theorem run_fields (I : Input) (tau : Nat) (R : Run) (h : ActualRun.run I tau=.ok R) :
    R.tau=tau ∧ R.n=I.ids.length ∧ R.base=I.p.base ∧
    R.D=I.p.maxSingleGrant-I.p.base ∧ R.seed=I.seed ∧ R.key=NearSpecV3.leWords I.seed := by
  unfold ActualRun.run at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first
    | cases h
    | split at h
  all_goals exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- The only core semantic change is native prior allowance selection. -/
theorem core_agrees (I : Input)
    (h:ProcActualInput.allowances I.ids I.prev=a0Src I.ids I.prev) :
    ActualRun.coreEv I.ids I.p I.allowed I.raw I.seed I.ash I.prev=
      coreEv I.ids I.p I.allowed I.raw I.seed I.ash I.prev := by
  unfold ActualRun.coreEv coreEv
  rw [h]

/-- Every old replay check is retained when the two prior lookups agree. -/
theorem run_agrees (I : Input) (tau : Nat)
    (h:ProcActualInput.allowances I.ids I.prev=a0Src I.ids I.prev) :
    ActualRun.run I tau=Gen.run I tau := by
  unfold ActualRun.run Gen.run
  simp only [ActualRun.coreEv,coreEv,h]

set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
/-- The accepted-native prior-state regression now replays with the actual
zero allowance instead of the unrelated unknown-shard record's seven. -/
theorem regression_run :
    (match ActualRun.run ProcPreviousStateRegression.input 0 with
      | .error _=>none | .ok R=>some R.a2[0]!)=some 2250000 := by
  decide +kernel

theorem regression_core :
    (match ActualRun.coreEv ProcPreviousStateRegression.input.ids ProcPreviousStateRegression.input.p
      ProcPreviousStateRegression.input.allowed ProcPreviousStateRegression.input.raw
      ProcPreviousStateRegression.input.seed ProcPreviousStateRegression.input.ash
      ProcPreviousStateRegression.input.prev with
      | .error _=>none | .ok o=>some (o.state.take 29))=
      some ([0]++NearSpec.u32 4++NearSpec.u64 0++NearSpec.u64 0++NearSpec.u64 2250000) := by
  decide +kernel

/-- The corrected run actually passes the corrected codec and emits the native
state prefix. This retains original prior bytes, rather than normalizing them. -/
theorem regression_codec :
    (match ActualRun.run ProcPreviousStateRegression.input 0 with
      | .error _=>none
      | .ok R=>match ProcPriorCodecGen.codecRows ProcPreviousStateRegression.input R true 0
          (Array.replicate 4 0) [] with
        | .error _=>none | .ok o=>some (o.post.take 29))=
      some (([0]++NearSpec.u32 4++NearSpec.u64 0++NearSpec.u64 0++NearSpec.u64 2250000).map UInt8.toNat) := by
  decide +kernel

end ZkFormal.NearV3.Candidates.ProcActualRunFacts
