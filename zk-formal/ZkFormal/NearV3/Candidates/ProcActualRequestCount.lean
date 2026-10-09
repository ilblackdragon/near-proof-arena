import ZkFormal.NearV3.Candidates.ProcActualRun
import ZkFormal.NearV3.Candidates.ProcActualConverted
import ZkFormal.NearV3.Candidates.ProcActualNativeBudget
import ZkFormal.NearV3.Sched.Complete.Steps
namespace ZkFormal.NearV3.Candidates.ProcActualRequestCount
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

theorem count_le {α β ε : Type} (xs : List α) (f : α → Array β → Except ε (ForInStep (Array β)))
    (hf : ∀a∈xs,∀b s,f a b=.ok s → ∃b',s=.yield b' ∧ b'.size≤b.size+1)
    (b out : Array β) (h : forIn xs b f=.ok out) : out.size≤b.size+xs.length := by
  induction xs generalizing b with
  | nil => simp only [List.forIn_nil] at h; cases h; simp
  | cons a xs ih =>
    rw [List.forIn_cons] at h
    cases he : f a b with
    | error e => simp only [he,bind,Except.bind] at h; cases h
    | ok s =>
      rcases hf a (by simp) b s he with ⟨next,rfl,hn⟩
      simp only [he,bind,Except.bind] at h
      have ht := ih (fun a ha=>hf a (by simp [ha])) next h
      simp only [List.length_cons]
      omega

theorem step_count (I : Input) (q : RawReq) (cv : Array CReq)
    (out : ForInStep (Array CReq)) (h : ProcActualConverted.step I q cv=.ok out) :
    ∃next,out=.yield next ∧ next.size≤cv.size+1 := by
  unfold ProcActualConverted.step at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals exact ⟨_,rfl,by simp⟩

theorem loop_count (I : Input) (out : Array CReq)
    (h : forIn I.raw #[] (ProcActualConverted.step I)=.ok out) : out.size≤I.raw.length := by
  simpa using count_le I.raw (ProcActualConverted.step I) (fun q _ cv out h=>step_count I q cv out h) #[] out h

set_option maxHeartbeats 400000 in
theorem run_count (I : Input) (tau : Nat) (R : Run) (h : ActualRun.run I tau=.ok R) :
    R.conv.length≤I.raw.length := by
  unfold ActualRun.run at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals apply loop_count I; assumption

/-- Native conversion does not increase the A8 request count. This binds the
same actual generator input to the prepared scheduler request list. -/
theorem prepared_count (sp : NearSpecV3.Scheduler.SchedPub) (hs : SchedPubOk sp)
    (I : Input) (tau : Nat) (R : Run) (h : ActualRun.run I tau=.ok R)
    (hraw : I.raw=(instOf sp).raw) : R.conv.length≤sp.ids.length*sp.ids.length := by
  have hc := run_count I tau R h
  have hb := Complete.instOf_raw_le sp hs
  rw [hraw] at hc
  omega
end ZkFormal.NearV3.Candidates.ProcActualRequestCount
