import ZkFormal.NearV3.Candidates.ProcNativeRound
namespace ZkFormal.NearV3.Candidates.ProcNativeRoundExistence
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler ProcNativeGrant ProcNativePush

theorem of_native (n M : Nat) (hM : M≤u64Max) (allowed : Array Bool) (reqs : List Req)
    (hr : ProcPoppedSuccess.GoodRequests reqs) (i : Nat) (s : ProcModelStep.Acc)
    (hs : ProcRoundSuccess.Ready reqs s) (hn : s.1≠[])
    (ht : s.1.Pairwise (fun p q=>p.ts<q.ts)) (hg : Inv n M s.2.1)
    (result : St×List (Nat×List Req))
    (h : ProcNativeRound.run n allowed (native s.2.1) (bucketsOf reqs (s.1.map toPM))=some result) :
    ∃out,ProcModelStep.step n allowed reqs i s=.ok (.yield out) ∧
      ProcRoundSuccess.Ready reqs out ∧
      (native out.2.1,bucketsOf reqs (out.1.map toPM))=result := by
  have hp := (ProcMaxBucket.native_pop reqs s.1 hn ht).1
  let vals := (sortTs (s.1.filter (fun p=>p.key==ProcMaxBucket.maxKey s.1))).map (·.v)
  have hcopy := h
  unfold ProcNativeRound.run at hcopy
  rw [hp] at hcopy
  have hmap : vals.map (reqAt reqs)=
      (sortTs (s.1.filter (fun p=>p.key==ProcMaxBucket.maxKey s.1))).map (fun p=>reqAt reqs p.v) := by
    simp [vals,List.map_map]
  dsimp only at hcopy
  rw [←hmap] at hcopy
  change (match NearSpecV3.shuffle (vals.map (reqAt reqs)) s.2.1.rng with
    | none=>none
    | some (qs,rng)=>some (processBucket n allowed qs
      ({native s.2.1 with rng:=rng},(bucketsOf reqs (s.1.map toPM)).dropLast)))=some result at hcopy
  cases hshuffle : NearSpecV3.shuffle (vals.map (reqAt reqs)) s.2.1.rng with
  | none => rw [hshuffle] at hcopy; cases hcopy
  | some p =>
    rcases p with ⟨qs,rng⟩
    obtain ⟨sh,hsh,hmap⟩ := ProcNativeRound.shuffle_pullback (reqAt reqs) vals s.2.1.rng qs rng hshuffle
    obtain ⟨out,he,hready⟩ := ProcRoundSuccess.step_success n allowed reqs hr i s hs hn sh rng hsh
    have href := ProcNativeRound.step_refines n M hM allowed reqs (fun q hq=>(hr q hq).1)
      i s out hn ht hs.2.2.1 hg he
    exact ⟨out,he,hready,Option.some.inj (href.symm.trans h)⟩

theorem processLoop_succ (n : Nat) (allowed : Array Bool) (fuel : Nat) (st : St)
    (bk : List (Nat×List Req)) (hn : bk≠[]) :
    processLoop n allowed (fuel+1) st bk=
      (ProcNativeRound.run n allowed st bk).bind (fun out=>processLoop n allowed fuel out.1 out.2) := by
  cases bk with
  | nil => contradiction
  | cons b bs =>
    simp only [processLoop,ProcNativeRound.run]
    cases hh : NearSpecV3.shuffle (b::bs).getLast!.2 st.rng <;> simp [hh]
end ZkFormal.NearV3.Candidates.ProcNativeRoundExistence
