import ZkFormal.NearV3.Candidates.ProcQsortSorted
namespace ZkFormal.NearV3.Candidates.ProcActualPushLogGuard
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
abbrev Record := Nat×Nat×Nat×Nat

theorem timestamp_injective (xs : List Record) (hs : xs.Pairwise (fun a b=>a.1<b.1))
    (a b : Record) (ha : a∈xs) (hb : b∈xs) (he : a.1=b.1) : a=b := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    have hp := List.pairwise_cons.mp hs
    rcases List.mem_cons.mp ha with rfl|haTail
    · rcases List.mem_cons.mp hb with rfl|hbTail
      · rfl
      · have := hp.1 b hbTail; omega
    · rcases List.mem_cons.mp hb with rfl|hbTail
      · have := hp.1 a haTail; omega
      · exact ih hp.2 haTail hbTail

theorem sort_equal (xs ys : List Record) (hs : xs.Pairwise (fun a b=>a.1<b.1))
    (hp : xs.Perm ys) : sortPush xs=sortPush ys := by
  have hx := ProcQsortPermutation.sortPush_perm xs
  have hy := ProcQsortPermutation.sortPush_perm ys
  apply (hx.trans (hp.trans hy.symm)).eq_of_pairwise ?_
    (ProcQsortSorted.push_sort_order xs) (ProcQsortSorted.push_sort_order ys)
  intro a b ha hb hab hba
  exact timestamp_injective xs hs a b (hx.mem_iff.mp ha)
    (hp.mem_iff.mpr (hy.mem_iff.mp hb)) (by omega)

open NearSpecV3.Scheduler in
theorem replay_push_guard (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (cv : Array CReq) (st : PState) (rs : List Round)
    (hcv : forIn (ProcPreparedSequence.input sp prev).raw #[]
      (ProcActualConverted.step (ProcPreparedSequence.input sp prev))=.ok cv)
    (hproc : ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs)) :
    ∃out,ProcActualReplayFactor.replay (ProcPreparedSequence.input sp prev) cv rs=.ok out ∧
      check (sortPush (ProcActualGeneratedPush.pushes (ProcActualReplayRound.entryAcc out)).toList ==
        sortPush (ProcActualPoppedLog.buckets out).toList) "push log ≠ buckets"=.ok () := by
  obtain ⟨out,hr,ho,hp⟩ := ProcGeneratedTimeOrder.replay_order sp hs prev cv st rs hcv hproc
  refine ⟨out,hr,?_⟩
  have he := sort_equal _ _ ho hp
  simp [he,check,pure,Except.pure]
end ZkFormal.NearV3.Candidates.ProcActualPushLogGuard
