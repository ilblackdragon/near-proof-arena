import ZkFormal.NearV3.Candidates.ProcNativePush
namespace ZkFormal.NearV3.Candidates.ProcNativeBucketReplay
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler ProcRequestPointers ProcNativeGrant ProcNativePush

theorem entries_pushes (n M : Nat) (hM : M≤u64Max) (allowed : Array Bool) (reqs : List Req)
    (K z : Nat) (vs : List Nat) (hv : ∀v∈vs,Valid reqs v)
    (s out : ProcModelStep.EntryAcc) (hs : Inv n M s.2.1)
    (h : forIn vs s (ProcModelStep.entryStep n allowed reqs K z)=.ok out) :
    (ProcPushEntries.pushes K z out.2.2.2).map toPM=
      (ProcPushEntries.pushes K z s.2.2.2).map toPM++
      (runL n allowed reqs K z vs s.2.2.1 (native s.2.1)).2 := by
  induction vs generalizing s with
  | nil => simp only [List.forIn_nil] at h; cases h; simp [runL]
  | cons v vs ih =>
    rw [List.forIn_cons] at h
    cases he : ProcModelStep.entryStep n allowed reqs K z v s with
    | error e => simp only [he,bind,Except.bind] at h; cases h
    | ok next =>
      obtain ⟨next,rfl,ht,hl⟩ := ProcModelEntryShape.entry_shape n allowed reqs K z v s next he
      simp only [he,bind,Except.bind] at h
      have hinv := ProcNativeGrant.entry_inv n M hM allowed reqs K z v s hs _ he
      have hg := ProcGrantAgreement.entry_grant n allowed reqs K z v s _ he
      have hev := ProcEntryEvent.entry_event n allowed reqs K z v s _ he
      simp only [ExceptLoop.StepInv] at hinv hg hev
      rw [ih (fun w hw=>hv w (by simp [hw])) next hinv h,hev]
      simp only [ProcPushEntries.pushes,List.flatMap_append,List.flatMap_cons,
        List.flatMap_nil,List.append_nil,List.map_append,List.append_assoc,runL]
      rw [step_pushes n M hM allowed reqs K z s.2.2.1 v s.2.1 hs (hv v (by simp))]
      rw [ProcNativeBucket.step_state n allowed reqs K z s.2.2.1 v (native s.2.1) (hv v (by simp)),
        grant_native n M hM allowed s.2.1 hs,hg,ht]

theorem bucket_exact (n M : Nat) (hM : M≤u64Max) (allowed : Array Bool) (reqs : List Req)
    (hR : ∀q∈reqs,q.incs.length<64) (K z : Nat) (vs : List Nat)
    (hv : ∀v∈vs,Valid reqs v) (pending : List Push) (st : PState) (t : Nat)
    (out : ProcModelStep.EntryAcc) (hs : Inv n M st)
    (h : forIn vs (pending,st,t,[]) (ProcModelStep.entryStep n allowed reqs K z)=.ok out) :
    processBucket n allowed (vs.map (reqAt reqs)) (native st,bucketsOf reqs (pending.map toPM))=
      (native out.2.1,bucketsOf reqs (out.1.map toPM)) := by
  rw [processBucket_runL n allowed reqs hR K z vs t (native st) (pending.map toPM)]
  have hst := ProcNativeBucket.entries_bucket_state n M hM allowed reqs hR K z vs hv
    (pending,st,t,[]) out hs h (pending.map toPM)
  rw [processBucket_runL n allowed reqs hR K z vs t (native st) (pending.map toPM)] at hst
  have hp := entries_pushes n M hM allowed reqs K z vs hv (pending,st,t,[]) out hs h
  simp only [ProcPushEntries.pushes,List.flatMap_nil,List.map_nil,List.nil_append] at hp
  have hout := ProcPushEntries.entries_pushes n allowed reqs K z vs pending st t out h
  rw [hst,←hp,hout,List.map_append]
  rfl
end ZkFormal.NearV3.Candidates.ProcNativeBucketReplay
