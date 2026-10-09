import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordTotal
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecForwardSuccess
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcPriorCodecRecordStep

private theorem throw_eq {α : Type} (e : String) : (throw e : Except String α)=.error e := rfl

/-- A successful actual main-instance terminal step has passed its forwarding
check; the demand bound is extracted rather than supplied to the row proof. -/
theorem bound (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (k : Nat) (s out : State) (ht : R.tau=0)
    (h : step I R present gb fwd inst k 2 7 s=.ok (.yield out)) :
    ProcPriorCodecRecordTotal.Forward R gb fwd k := by
  unfold ProcPriorCodecRecordTotal.Forward
  apply Classical.byContradiction
  intro hf
  simp only [List.getD_eq_getElem?_getD] at hf
  simp [step,ht,hf,check,bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | split at h | cases h
  all_goals repeat first | split at h | cases h
  all_goals simp_all [throw_eq]
end ZkFormal.NearV3.Candidates.ProcPriorCodecForwardSuccess
