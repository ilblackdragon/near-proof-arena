import ZkFormal.NearV3.Candidates.ProcNativeRoundExistence
namespace ZkFormal.NearV3.Candidates.ProcNativeLoopExistence
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler ProcNativeGrant ProcNativePush

theorem empty_forIn (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (s : ProcModelStep.Acc) (hs : s.1=[]) (xs : List Nat) :
    forIn xs s (ProcModelStep.step n allowed reqs)=.ok s := by
  cases xs with
  | nil => rfl
  | cons i xs => simp [List.forIn_cons,ProcModelStep.step,hs,bind,Except.bind,pure,Except.pure]

theorem empty_state (n : Nat) (allowed : Array Bool) (reqs : List Req) (fuel : Nat)
    (s : ProcModelStep.Acc) (hs : s.1=[]) (stF : St)
    (h : processLoop n allowed fuel (native s.2.1) (bucketsOf reqs (s.1.map toPM))=some stF) :
    native s.2.1=stF := by
  simp only [hs,List.map_nil,bucketsOf,List.foldl_nil] at h
  cases fuel <;> simpa only [processLoop,Option.some.injEq] using h

set_option maxHeartbeats 1000000 in
/-- Actual native loop success constructs the full event-model loop, using the
same fuel and RNG. No model execution or successful model guard is assumed. -/
theorem loop_exists (n M : Nat) (hM : M≤u64Max) (allowed : Array Bool) (reqs : List Req)
    (hr : ProcPoppedSuccess.GoodRequests reqs) (fuel start : Nat) (s : ProcModelStep.Acc)
    (hs : ProcRoundSuccess.Ready reqs s) (ht : ProcModelTime.Inv s) (hg : Inv n M s.2.1)
    (stF : St)
    (h : processLoop n allowed fuel (native s.2.1) (bucketsOf reqs (s.1.map toPM))=some stF) :
    ∃out,forIn (List.range' start fuel) s (ProcModelStep.step n allowed reqs)=.ok out ∧
      out.1=[] ∧ native out.2.1=stF := by
  induction fuel generalizing start s with
  | zero =>
    by_cases hn : s.1=[]
    · exact ⟨s,rfl,hn,empty_state n allowed reqs 0 s hn stF h⟩
    · have hb := ProcNativeRound.buckets_nonempty reqs s.1 hn
      cases he : bucketsOf reqs (s.1.map toPM) with
      | nil => exact False.elim (hb he)
      | cons b bs => simp [he,processLoop] at h
  | succ fuel ih =>
    by_cases hn : s.1=[]
    · exact ⟨s,empty_forIn n allowed reqs s hn _,hn,empty_state n allowed reqs _ s hn stF h⟩
    · have hb := ProcNativeRound.buckets_nonempty reqs s.1 hn
      rw [ProcNativeRoundExistence.processLoop_succ n allowed fuel _ _ hb] at h
      cases hrn : ProcNativeRound.run n allowed (native s.2.1) (bucketsOf reqs (s.1.map toPM)) with
      | none => simp [hrn] at h
      | some result =>
        simp only [hrn,Option.bind_some] at h
        obtain ⟨next,he,hnr,hresult⟩ := ProcNativeRoundExistence.of_native n M hM allowed reqs hr
          start s hs hn ht.1.1 hg result hrn
        rw [←hresult] at h
        have ht' := ProcModelTime.step_inv n allowed reqs start s ht _ he
        have hg' := ProcNativeState.step_inv n M hM allowed reqs start s hg _ he
        obtain ⟨out,ho,hend,hfinal⟩ := ih (start+1) next hnr ht' hg' h
        refine ⟨out,?_,hend,hfinal⟩
        simpa only [List.range'_succ,List.forIn_cons,he,bind,Except.bind] using ho
end ZkFormal.NearV3.Candidates.ProcNativeLoopExistence
