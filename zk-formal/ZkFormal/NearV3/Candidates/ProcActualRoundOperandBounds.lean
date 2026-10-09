import ZkFormal.NearV3.Candidates.ProcActualParameterGuard
import ZkFormal.NearV3.Candidates.ProcActualMemoryOperandBounds
namespace ZkFormal.NearV3.Candidates.ProcActualRoundOperandBounds
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcActualMemoryOperandBounds
abbrev Cmps := ProcActualMemoryScan.Cmps

theorem entry_time (rd : Gen.RoundD) (hg : ProcActualRoundTimes.Good rd)
    (i : Nat) (hi : i<rd.entries.toArray.size) : rd.entries.toArray[i]!.ts<rd.T := by
  have hm : rd.entries.toArray[i]∈rd.entries := by simpa using Array.getElem_mem hi
  simpa only [getElem!_pos rd.entries.toArray i hi] using hg.2 _ hm

theorem bucket_step_bound (B : Nat) (rd : Gen.RoundD) (hg : ProcActualRoundTimes.Good rd)
    (hT : rd.T<B) (i : Nat) (hi : i<rd.entries.length) (cs out : Cmps)
    (hc : Bounded B cs) (h : ProcActualBucketComparisons.step rd i cs=.ok (.yield out)) :
    Bounded B out := by
  have ht := entry_time rd hg i (by simpa using hi)
  have hcxt : (if i+1=rd.entries.toArray.size then rd.T else rd.entries.toArray[i+1]!.ts)<B := by
    split
    · exact hT
    · apply Nat.lt_trans (entry_time rd hg (i+1) (by simpa using (show i+1<rd.entries.length by simp only [List.size_toArray] at *; omega))) hT
  unfold ProcActualBucketComparisons.step at h
  dsimp only at h
  rw [ProcActualRoundTimes.good_checks rd hg i hi] at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  cases h
  exact push_bound B cs _ _ _ hc hcxt (by omega)

theorem bucket_loop_bound (B : Nat) (rd : Gen.RoundD) (hg : ProcActualRoundTimes.Good rd)
    (hT : rd.T<B) (xs : List Nat) (hx : ∀i∈xs,i<rd.entries.length)
    (cs out : Cmps) (hc : Bounded B cs)
    (h : forIn xs cs (ProcActualBucketComparisons.step rd)=.ok out) : Bounded B out := by
  induction xs generalizing cs with
  | nil => simp only [List.forIn_nil] at h; cases h; exact hc
  | cons i xs ih =>
    obtain ⟨mid,hm⟩ := ProcActualBucketComparisons.step_success rd hg i (hx i (by simp)) cs
    simp only [List.forIn_cons,hm,bind,Except.bind] at h
    exact ih (fun j hj=>hx j (by simp [hj])) mid
      (bucket_step_bound B rd hg hT i (hx i (by simp)) cs mid hc hm) h

theorem bucket_bound (B : Nat) (rd : Gen.RoundD) (hg : ProcActualRoundTimes.Good rd)
    (hT : rd.T<B) (cs out : Cmps) (hc : Bounded B cs)
    (h : forIn (List.range rd.entries.toArray.size) cs (ProcActualBucketComparisons.step rd)=.ok out) :
    Bounded B out := by
  apply bucket_loop_bound B rd hg hT _ _ cs out hc h
  simp only [List.size_toArray,List.mem_range]
  exact fun i hi=>hi
theorem bucket_yield_bound (B : Nat) (rd : Gen.RoundD) (hg : ProcActualRoundTimes.Good rd)
    (hT : rd.T<B) (cs out : Cmps) (hc : Bounded B cs)
    (h : (do
      let out ← forIn (List.range rd.entries.toArray.size) cs (ProcActualBucketComparisons.step rd)
      pure (.yield out) : Except String (ForInStep Cmps))=.ok (.yield out)) : Bounded B out := by
  cases he : forIn (List.range rd.entries.toArray.size) cs (ProcActualBucketComparisons.step rd) with
  | error e => simp only [he,bind,Except.bind] at h; cases h
  | ok next =>
    simp only [he,bind,Except.bind,pure,Except.pure] at h
    cases h
    exact bucket_bound B rd hg hT cs out hc he

theorem round_bound (B : Nat) (rd : Gen.RoundD) (hg : ProcActualRoundTimes.Good rd)
    (hT : rd.T<B) (hK : rd.K≠0 → rd.K<rd.Kq ∧ rd.Kq<B)
    (cs out : Cmps) (hc : Bounded B cs)
    (h : ProcActualComparisonFactor.roundStep rd cs=.ok (.yield out)) : Bounded B out := by
  unfold ProcActualComparisonFactor.roundStep at h
  split at h
  · rename_i hn
    have hk := hK (by simpa using hn)
    have hcheck : check (rd.K<rd.Kq) "round keys not decreasing"=.ok () := by
      simp [check,hk.1,pure,Except.pure]
    rw [hcheck] at h
    simp only [bind,Except.bind] at h
    exact bucket_yield_bound B rd hg hT _ out
      (push_bound B cs rd.Kq (rd.K+1) _ hc hk.2 (by omega)) h
  · exact bucket_yield_bound B rd hg hT cs out hc h

theorem rounds_bound (B : Nat) (rs : List Gen.RoundD)
    (hg : ∀rd∈rs,ProcActualRoundTimes.Good rd)
    (hT : ∀rd∈rs,rd.T<B)
    (hK : ∀rd∈rs,rd.K≠0 → rd.K<rd.Kq ∧ rd.Kq<B)
    (cs out : Cmps) (hc : Bounded B cs)
    (h : forIn rs cs ProcActualComparisonFactor.roundStep=.ok out) : Bounded B out := by
  induction rs generalizing cs with
  | nil => simp only [List.forIn_nil] at h; cases h; exact hc
  | cons rd rs ih =>
    obtain ⟨mid,hm⟩ := ProcActualComparisonFactor.round_success rd (hg rd (by simp))
      (fun hn=>(hK rd (by simp) hn).1) cs
    simp only [List.forIn_cons,hm,bind,Except.bind] at h
    exact ih (fun r hr=>hg r (by simp [hr])) (fun r hr=>hT r (by simp [hr]))
      (fun r hr=>hK r (by simp [hr])) mid
      (round_bound B rd (hg rd (by simp)) (hT rd (by simp)) (hK rd (by simp)) cs mid hc hm) h
open NearSpecV3.Scheduler ProcActualReplayRound in
theorem afterMemory_success (sp : SchedPub) (hs : SchedPubOk sp) (prev : NearSpec.Bandwidth.State)
    (tau : Nat) (cv : Array CReq) (st : PState) (s : Acc) (gs : Array Gen.Seg) (cs : Cmps)
    (hg : ProcActualRoundTimes.AllGood s)
    (hT : ∀rd∈(ProcActualRoundTimes.rounds s).toList,rd.T<2^29)
    (hK : ∀rd∈(ProcActualRoundTimes.rounds s).toList,rd.K≠0 → rd.K<rd.Kq ∧ rd.Kq<2^29)
    (hc : Bounded (2^29) cs) :
    ∃r,ProcActualSegmentFactor.afterMemory (ProcPreparedSequence.input sp prev) tau cv st s gs cs=.ok r := by
  obtain ⟨out,ho⟩ := ProcActualComparisonFactor.array_success (ProcActualRoundTimes.rounds s) hg
    (fun rd hr hn=>(hK rd hr hn).1) cs
  have hb : Bounded (2^29) out := by
    apply rounds_bound (2^29) (ProcActualRoundTimes.rounds s).toList hg hT hK cs out hc
    simpa only [Array.forIn_toList] using ho
  refine ⟨ProcActualParameterGuard.result (ProcPreparedSequence.input sp prev) tau cv st s gs out,?_⟩
  rw [ProcActualComparisonFactor.afterMemory_eq,ho]
  change ProcActualComparisonFactor.finish _ _ _ _ _ _ _ = _
  rw [ProcActualParameterGuard.finish_eq sp hs,operand_check out hb]
  rfl
end ZkFormal.NearV3.Candidates.ProcActualRoundOperandBounds
