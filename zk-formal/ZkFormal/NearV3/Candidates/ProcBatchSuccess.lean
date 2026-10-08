import ZkFormal.NearV3.Candidates.ProcLiveLinks
namespace ZkFormal.NearV3.Candidates.ProcBatchSuccess
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler ProcPendingCurrent

def Selected (reqs : List Req) (al : Array Nat) (K : Nat) (vs : List Nat) : Prop :=
  ∀v∈vs,link reqs v<al.size ∧ al[link reqs v]! = K

theorem entry_selected (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (K z v : Nat) (vs : List Nat) (s : ProcModelStep.EntryAcc)
    (hs : Selected reqs s.2.1.al K vs)
    (hd : ∀w∈vs,link reqs v≠link reqs w)
    (out : ForInStep ProcModelStep.EntryAcc)
    (h : ProcModelStep.entryStep n allowed reqs K z v s=.ok out) :
    ExceptLoop.StepInv (fun out=>Selected reqs out.2.1.al K vs) out := by
  have hg := ProcGrantAgreement.entry_grant n allowed reqs K z v s out h
  cases out <;> simp only [ExceptLoop.StepInv] at hg ⊢ <;> rw [hg]
  all_goals
    unfold ProcGrantAgreement.modelGrant
    split
    · intro w hw
      have hh := hs w hw
      refine ⟨by simpa using hh.1,?_⟩
      change (s.2.1.al.set! (link reqs v) _)[link reqs w]! = K
      rw [Array.getElem!_set!_ne _ _ _ _ (hd w hw)]
      exact hh.2
    · exact hs

/-- Constructive success of the complete model entry loop, not a conditional
postcondition. Distinct live links and current allowance bindings suffice. -/
theorem entries_success (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (K z : Nat) (vs : List Nat) (s : ProcModelStep.EntryAcc)
    (hp : Current reqs s.2.1.al s.1)
    (hs : Selected reqs s.2.1.al K vs)
    (hd : (ProcLiveLinks.live reqs s.1 vs).Nodup)
    (hj : ∀v∈vs,v%64+1<64)
    (hi : ∀v∈vs,0<reqs.toArray[v/64]!.incs.getD (v%64) 0) :
    ∃out,forIn vs s (ProcModelStep.entryStep n allowed reqs K z)=.ok out ∧
      Current reqs out.2.1.al out.1 ∧ (ProcLiveLinks.live reqs out.1 []).Nodup := by
  induction vs generalizing s with
  | nil => exact ⟨s,rfl,hp,hd⟩
  | cons v vs ih =>
    have hv := hs v (by simp)
    obtain ⟨next,he⟩ := ProcModelEntrySuccess.entry_success n allowed reqs K z v s
      hv.1 hv.2 (hi v (by simp))
    have hn := ProcLiveLinks.selected_distinct reqs s.1 v vs hd
    have hpc := ProcPendingTransition.entry_current n allowed reqs K z v s hp hv.1 hn.1
      (hj v (by simp)) _ he
    have hsc := entry_selected n allowed reqs K z v vs s
      (fun w hw=>hs w (by simp [hw])) hn.2 _ he
    have hdc := ProcLiveLinks.entry_nodup n allowed reqs K z v vs s (hj v (by simp)) hd _ he
    obtain ⟨out,hout,hpout,hdout⟩ := ih next hpc hsc hdc
      (fun w hw=>hj w (by simp [hw])) (fun w hw=>hi w (by simp [hw]))
    refine ⟨out,?_,hpout,hdout⟩
    simpa only [List.forIn_cons,he,bind,Except.bind] using hout
end ZkFormal.NearV3.Candidates.ProcBatchSuccess
