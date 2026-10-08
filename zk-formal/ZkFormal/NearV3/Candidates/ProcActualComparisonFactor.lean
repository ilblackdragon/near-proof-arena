import ZkFormal.NearV3.Candidates.ProcActualBucketComparisons
namespace ZkFormal.NearV3.Candidates.ProcActualComparisonFactor
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcActualReplayRound
abbrev Cmps := ProcActualMemoryScan.Cmps

def roundStep (rd : Gen.RoundD) (cs : Cmps) : Except String (ForInStep Cmps) := do
  let mut cmps := cs
  if rd.K != 0 then
    check (rd.K < rd.Kq) "round keys not decreasing"
    cmps := cmps.push (rd.Kq,rd.K+1,if rd.K+1≤rd.Kq then 1 else 0)
  let out ← forIn (List.range rd.entries.toArray.size) cmps (ProcActualBucketComparisons.step rd)
  pure (.yield out)

def finish (I : Input) (tau : Nat) (conv : Array CReq) (stF : PState) (acc : Acc)
    (segs : Array Gen.Seg) (cmps : Cmps) : Except String Run := do
  let n := I.ids.length
  let p := I.p
  let lp := linkPass n p I.allowed (ProcActualInput.allowances I.ids I.prev)
  let key := NearSpecV3.leWords I.seed
  let (_,_,_,_,_,_,_,_,_,_,kpos,_,_,used,rounds,_) := acc
  check (cmps.all fun (x,y,_)=>x<2^29 && y<2^29) "comparison operand ≥ 2^29"
  let D := p.maxSingleGrant-p.base
  check (p.base<2^24 && D<2^24) "params ≥ 2^24"
  return { tau, n, base := p.base, D, seed := I.seed, key, a2 := lp.a2, conv := conv.toList,
           used, rounds := rounds.toList, segs := segs.toList, cmps := cmps.toList,
           kfin := kpos, fin := stF }

theorem afterMemory_eq (I : Input) (tau : Nat) (cv : Array CReq) (st : PState)
    (s : Acc) (gs : Array Gen.Seg) (cs : Cmps) :
    ProcActualSegmentFactor.afterMemory I tau cv st s gs cs =
      (forIn (ProcActualRoundTimes.rounds s) cs roundStep >>= finish I tau cv st s gs) := by
  rfl

theorem round_success (rd : Gen.RoundD) (hg : ProcActualRoundTimes.Good rd)
    (hk : rd.K≠0 → rd.K<rd.Kq) (cs : Cmps) :
    ∃out,roundStep rd cs=.ok (.yield out) := by
  unfold roundStep
  split
  · rename_i h
    have hn : rd.K≠0 := by simpa using h
    have hc : check (rd.K<rd.Kq) "round keys not decreasing"=.ok () := by
      simp [check,hk hn,pure,Except.pure]
    rw [hc]
    simp only [bind,Except.bind,pure,Except.pure]
    obtain ⟨out,ho⟩ := ProcActualBucketComparisons.bucket_success rd hg
      (cs.push (rd.Kq,rd.K+1,if rd.K+1≤rd.Kq then 1 else 0))
    rw [ho]
    exact ⟨out,rfl⟩
  · simp only [bind,Except.bind,pure,Except.pure]
    obtain ⟨out,ho⟩ := ProcActualBucketComparisons.bucket_success rd hg cs
    rw [ho]
    exact ⟨out,rfl⟩

theorem list_success (rs : List Gen.RoundD)
    (hg : ∀rd∈rs,ProcActualRoundTimes.Good rd)
    (hk : ∀rd∈rs,rd.K≠0 → rd.K<rd.Kq) (cs : Cmps) :
    ∃out,forIn rs cs roundStep=.ok out := by
  induction rs generalizing cs with
  | nil => exact ⟨cs,rfl⟩
  | cons rd rs ih =>
    obtain ⟨mid,hm⟩ := round_success rd (hg rd (by simp)) (hk rd (by simp)) cs
    obtain ⟨out,ho⟩ := ih (fun r hr=>hg r (by simp [hr])) (fun r hr=>hk r (by simp [hr])) mid
    refine ⟨out,?_⟩
    simpa only [List.forIn_cons,hm,bind,Except.bind] using ho

theorem array_success (rs : Array Gen.RoundD)
    (hg : ∀rd∈rs.toList,ProcActualRoundTimes.Good rd)
    (hk : ∀rd∈rs.toList,rd.K≠0 → rd.K<rd.Kq) (cs : Cmps) :
    ∃out,forIn rs cs roundStep=.ok out := by
  simpa only [Array.forIn_toList] using list_success rs.toList hg hk cs
open NearSpecV3.Scheduler in
theorem prepared_reduction (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (cv : Array CReq) (st : PState) (rs : List Round)
    (hcv : forIn (ProcPreparedSequence.input sp prev).raw #[]
      (ProcActualConverted.step (ProcPreparedSequence.input sp prev))=.ok cv)
    (hproc : ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs))
    (s : Acc) (hr : ProcActualReplayFactor.replay (ProcPreparedSequence.input sp prev) cv rs=.ok s)
    (hk : ∀rd∈(ProcActualRoundTimes.rounds s).toList,rd.K≠0 → rd.K<rd.Kq)
    (tau : Nat) (gs : Array Gen.Seg) (cs : Cmps) :
    ∃out,ProcActualSegmentFactor.afterMemory (ProcPreparedSequence.input sp prev) tau cv st s gs cs =
      finish (ProcPreparedSequence.input sp prev) tau cv st s gs out := by
  have hg := ProcActualRoundTimes.replay_good sp hs prev cv st rs hcv hproc s hr
  obtain ⟨out,ho⟩ := array_success (ProcActualRoundTimes.rounds s) hg hk cs
  refine ⟨out,?_⟩
  rw [afterMemory_eq,ho]
  rfl
open NearSpecV3.Scheduler in
theorem suffix_reduction (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (tau : Nat) (cv : Array CReq) (st : PState) (rs : List Round)
    (hcv : forIn (ProcPreparedSequence.input sp prev).raw #[]
      (ProcActualConverted.step (ProcPreparedSequence.input sp prev))=.ok cv)
    (hproc : ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs))
    (hk : ∀s,ProcActualReplayFactor.replay (ProcPreparedSequence.input sp prev) cv rs=.ok s →
      ∀rd∈(ProcActualRoundTimes.rounds s).toList,rd.K≠0 → rd.K<rd.Kq) :
    ∃s gs cs,ProcActualReplayFactor.replay (ProcPreparedSequence.input sp prev) cv rs=.ok s ∧
      ProcActualRoundFactor.runRestRounds (ProcPreparedSequence.input sp prev) tau cv st rs =
      finish (ProcPreparedSequence.input sp prev) tau cv st s gs cs := by
  obtain ⟨s,gs,cs,hr,he⟩ := ProcActualAfterMemoryReduction.prepared_reduction sp hs prev tau cv st rs hcv hproc
  obtain ⟨out,ho⟩ := prepared_reduction sp hs prev cv st rs hcv hproc s hr (hk s hr) tau gs cs
  exact ⟨s,gs,out,hr,he.trans ho⟩
end ZkFormal.NearV3.Candidates.ProcActualComparisonFactor
