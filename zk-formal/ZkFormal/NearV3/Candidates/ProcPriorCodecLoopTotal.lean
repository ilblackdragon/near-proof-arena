import ZkFormal.NearV3.Candidates.ProcPriorCodecCarryTotal
import ZkFormal.NearV3.Candidates.ProcPriorCodecGen
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecLoopTotal
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
abbrev Acc := Array (Array Nat) × List (Nat×Nat×Nat)

def fieldStep (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (k f : Nat) (s : Acc) : Except String (ForInStep Acc) := do
  let out ← forIn (List.range 8) (s.1,s.2,0,0,0,0)
    (fun gg st=>ProcPriorCodecRecordStep.step I R present gb fwd inst k f gg st)
  pure (.yield (out.1,out.2.1))

def recordStep (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (k : Nat) (s : Acc) : Except String (ForInStep Acc) := do
  let out ← forIn (List.range 3) s (fieldStep I R present gb fwd inst k)
  pure (.yield out)

theorem plain_bytes (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (k f : Nat) (hf : f≠2) (xs : List Nat)
    (s : ProcPriorCodecRecordStep.State) :
    ∃out,forIn xs s (fun gg st=>ProcPriorCodecRecordStep.step I R present gb fwd inst k f gg st)=.ok out := by
  induction xs generalizing s with
  | nil => exact ⟨s,rfl⟩
  | cons gg xs ih =>
    obtain ⟨mid,hm⟩ := ProcPriorCodecRecordTotal.step_success I R present gb fwd inst k f gg s
      (by intro he; exact (hf he).elim) (by intro he; exact (hf he).elim)
    obtain ⟨out,ho⟩ := ih mid
    exact ⟨out,by simpa only [List.forIn_cons,hm,bind,Except.bind] using ho⟩

def Allowance (I : Input) (R : Run) (present : Bool) (k : Nat) : Prop :=
  ProcPriorCodecRecordTotal.endAllowance I R present k (ProcPriorCodecCarryTotal.bit I R present k)=R.a2[k]!

theorem field_success (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (k f : Nat) (s : Acc)
    (ha : Allowance I R present k)
    (hf : R.tau=0 → ProcPriorCodecRecordTotal.Forward R gb fwd k) :
    ∃out,fieldStep I R present gb fwd inst k f s=.ok (.yield out) := by
  have hh : ∃out,forIn (List.range 8) (s.1,s.2,0,0,0,0)
      (fun gg st=>ProcPriorCodecRecordStep.step I R present gb fwd inst k f gg st)=.ok out := by
    by_cases he : f=2
    · subst f
      obtain ⟨out,ho,_⟩ := ProcPriorCodecCarryTotal.bytes_success I R present gb fwd inst k 0 8
        (s.1,s.2,0,0,0,0) (by decide) (by omega) ha hf
      exact ⟨out,by simpa only [List.range_eq_range'] using ho⟩
    · exact plain_bytes I R present gb fwd inst k f he _ _
  obtain ⟨out,ho⟩ := hh
  exact ⟨(out.1,out.2.1),by simp only [fieldStep,ho,bind,Except.bind,pure,Except.pure]⟩

theorem fields_success (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (k : Nat) (fs : List Nat) (s : Acc)
    (ha : Allowance I R present k)
    (hf : R.tau=0 → ProcPriorCodecRecordTotal.Forward R gb fwd k) :
    ∃out,forIn fs s (fieldStep I R present gb fwd inst k)=.ok out := by
  induction fs generalizing s with
  | nil => exact ⟨s,rfl⟩
  | cons f fs ih =>
    obtain ⟨mid,hm⟩ := field_success I R present gb fwd inst k f s ha hf
    obtain ⟨out,ho⟩ := ih mid
    exact ⟨out,by simpa only [List.forIn_cons,hm,bind,Except.bind] using ho⟩

theorem record_success (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (k : Nat) (s : Acc)
    (ha : Allowance I R present k)
    (hf : R.tau=0 → ProcPriorCodecRecordTotal.Forward R gb fwd k) :
    ∃out,recordStep I R present gb fwd inst k s=.ok (.yield out) := by
  obtain ⟨out,ho⟩ := fields_success I R present gb fwd inst k (List.range 3) s ha hf
  exact ⟨out,by simp only [recordStep,ho,bind,Except.bind,pure,Except.pure]⟩

theorem records_success (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (ks : List Nat) (s : Acc)
    (ha : ∀k∈ks,Allowance I R present k)
    (hf : ∀k∈ks,R.tau=0 → ProcPriorCodecRecordTotal.Forward R gb fwd k) :
    ∃out,forIn ks s (recordStep I R present gb fwd inst)=.ok out := by
  induction ks generalizing s with
  | nil => exact ⟨s,rfl⟩
  | cons k ks ih =>
    obtain ⟨mid,hm⟩ := record_success I R present gb fwd inst k s (ha k (by simp)) (hf k (by simp))
    obtain ⟨out,ho⟩ := ih mid (fun j hj=>ha j (by simp [hj])) (fun j hj=>hf j (by simp [hj]))
    exact ⟨out,by simpa only [List.forIn_cons,hm,bind,Except.bind] using ho⟩
/-- Definitional equality with the complete nested records loop in codecRowsCore. -/
theorem records_eq (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (ks : List Nat) (s : Acc) :
    forIn ks s (fun kk acc => do
      let mut rows := acc.1
      let mut cmps := acc.2
      for f in List.range 3 do
        let mut apv := 0
        let mut apostv := 0
        let mut bigv := 0
        let mut cbv := 0
        let recState ← forIn (List.range 8) (rows,cmps,apv,apostv,bigv,cbv)
          (fun gg st => ProcPriorCodecRecordStep.step I R present gb fwd inst kk f gg st)
        rows := recState.1
        cmps := recState.2.1
        apv := recState.2.2.1
        apostv := recState.2.2.2.1
        bigv := recState.2.2.2.2.1
        cbv := recState.2.2.2.2.2
      pure (.yield (rows,cmps))) =
    forIn ks s (recordStep I R present gb fwd inst) := rfl
end ZkFormal.NearV3.Candidates.ProcPriorCodecLoopTotal
