import ZkFormal.NearV3.Candidates.ProcActualReplayMemory
import ZkFormal.NearV3.Candidates.ProcActualReplayAllowance
import ZkFormal.NearV3.Candidates.ProcActualParameterGuard
import ZkFormal.NearV3.Sched.Link.EntryInc
namespace ZkFormal.NearV3.Candidates.ProcActualMemoryValues
open NearSpecV3.Scheduler
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcActualReplayEntry

def Values (B : Nat) (logs : Array (Array Gen.MOp)) : Prop :=
  ∀ops∈logs.toList,∀o∈ops.toList,o.op=OP_GRANT → o.vin<B ∧ o.inc<B

def Inv (B : Nat) (s : Acc) : Prop :=
  ProcActualReplayAllowance.Bounded (B-1) s.1 ∧
  ProcActualReplayAllowance.Bounded (B-1) s.2.1 ∧
  ProcActualReplayAllowance.Bounded (B-1) s.2.2.1 ∧
  Values B s.2.2.2.2.1 ∧ Values B s.2.2.2.2.2.1 ∧ Values B s.2.2.2.2.2.2.1

def Increments (B : Nat) (cv : Array CReq) : Prop := ∀c∈cv.toList,∀(j : Nat),c.incs[j]!<B

theorem modify_values (B : Nat) (logs : Array (Array Gen.MOp)) (i : Nat) (o : Gen.MOp)
    (h : Values B logs) (ho : o.op=OP_GRANT → o.vin<B ∧ o.inc<B) :
    Values B (logs.modify i (·.push o)) := by
  intro ops hm
  obtain ⟨j,hj,he⟩ := List.getElem_of_mem hm
  have hj' : j<logs.size := by simpa using hj
  have h0 := h _ (Array.getElem_mem_toList hj')
  subst ops
  simp only [Array.getElem_toList,Array.getElem_modify]
  split
  · intro x hx
    simp only [Array.toList_push,List.mem_append,List.mem_singleton] at hx
    rcases hx with hx|rfl
    · exact h0 x hx
    · exact ho
  · exact h0

set_option maxHeartbeats 1000000 in
theorem step_values (I : Input) (cv : Array CReq) (rd : Round) (sh : List Nat)
    (T x B : Nat) (s out : Acc) (hB : 0<B) (hs : Inv B s) (hi : Increments B cv)
    (h : step I cv rd sh T x s=.ok (.yield out)) : Inv B out := by
  rcases s with ⟨sb,rb,aa,gg,ol,os,orr,ps,used,gi,es⟩
  have hinc (cid j : Nat) : cv[cid]!.incs[j]!<B := by
    by_cases hc : cid<cv.size
    · rw [getElem!_pos cv cid hc]
      exact hi _ (Array.getElem_mem_toList hc) j
    · rw [getElem!_neg cv cid hc]
      change ([] : List Nat)[j]!<B
      simpa using hB
  unfold step at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals
    refine ⟨ProcActualReplayAllowance.set_bound _ _ hs.1 _ _
        (ProcActualReplayAllowance.decrease_bound _ _ hs.1 _ _ _),
      ProcActualReplayAllowance.set_bound _ _ hs.2.1 _ _
        (ProcActualReplayAllowance.decrease_bound _ _ hs.2.1 _ _ _),
      ProcActualReplayAllowance.set_bound _ _ hs.2.2.1 _ _
        (ProcActualReplayAllowance.decrease_bound _ _ hs.2.2.1 _ _ _),?_,?_,?_⟩
    all_goals apply modify_values
    all_goals try first | exact hs.2.2.2.1 | exact hs.2.2.2.2.1 | exact hs.2.2.2.2.2
    all_goals intro _; constructor
    all_goals first | exact hinc _ _ | have hb := hs.1 cv[sh[x]!/64]!.s; dsimp only at *; omega | have hb := hs.2.1 cv[sh[x]!/64]!.r; dsimp only at *; omega | have hb := hs.2.2.1 cv[sh[x]!/64]!.link; dsimp only at *; omega

theorem loop_values (I : Input) (cv : Array CReq) (rd : Round) (sh xs : List Nat)
    (T B : Nat) (s out : Acc) (hB : 0<B) (hs : Inv B s) (hi : Increments B cv)
    (h : forIn xs s (step I cv rd sh T)=.ok out) : Inv B out := by
  induction xs generalizing s with
  | nil => simp only [List.forIn_nil] at h; cases h; exact hs
  | cons x xs ih =>
    rw [List.forIn_cons] at h
    cases he : step I cv rd sh T x s with
    | error e => simp only [he,bind,Except.bind] at h; cases h
    | ok next =>
      obtain ⟨next,rfl,_,_,_⟩ := ProcActualEntryTransition.step_effect I cv rd sh T x s next
        (NearSpecV3.Rng.ofSeed I.seed) he
      simp only [he,bind,Except.bind] at h
      exact ih next (step_values I cv rd sh T x B s next hB hs hi he) h

theorem converted_step (I : Input) (q : RawReq) (cv : Array CReq)
    (hb : I.p.base<2^24) (hd : I.p.maxSingleGrant-I.p.base<2^24)
    (hc : Increments (2^29) cv) (out : ForInStep (Array CReq))
    (h : ProcActualConverted.step I q cv=.ok out) :
    ExceptLoop.StepInv (Increments (2^29)) out := by
  unfold ProcActualConverted.step at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals first
    | exact hc
    | intro c hm j
      simp only [Array.toList_push,List.mem_append,List.mem_singleton] at hm
      rcases hm with hm|rfl
      · exact hc c hm j
      · have hh := incsOf_getD_lt I.p q.bm hb hd j
        have he : (incsOf I.p q.bm)[j]! = (incsOf I.p q.bm).getD j 0 := by
          simp only [getElem!_def,List.getD_eq_getElem?_getD]
          split <;> simp_all
        change (incsOf I.p q.bm)[j]!<2^29
        rw [he]
        omega

theorem converted_values (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (cv : Array CReq)
    (hcv : forIn (ProcPreparedSequence.input sp prev).raw #[]
      (ProcActualConverted.step (ProcPreparedSequence.input sp prev))=.ok cv) :
    Increments (2^29) cv := by
  obtain ⟨hb,hd⟩ := ProcActualParameterGuard.bounds sp.params sp.ids.length hs.params
  exact ExceptLoop.invariant _ _ (Increments (2^29))
    (fun q _ cv hc out ho=>converted_step _ q cv hb hd hc out ho) #[] cv
    (by simp [Increments]) hcv

open ProcActualReplayRound in
set_option maxHeartbeats 800000 in
theorem round_values (I : Input) (cv : Array CReq) (key : List Nat) (rd : Round)
    (B : Nat) (s out : ProcActualReplayRound.Acc) (hB : 0<B)
    (hs : Inv B (entryAcc s)) (hi : Increments B cv)
    (h : ProcActualReplayRound.step I cv key rd s=.ok (.yield out)) : Inv B (entryAcc out) := by
  rcases s with ⟨sb,rb,aa,gg,ol,os,orr,ps,bs,tm,kp,kq,zq,used,rs,gi⟩
  unfold ProcActualReplayRound.step at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals
    have he : forIn (List.range rd.bucket.length) (sb,rb,aa,gg,ol,os,orr,ps,used,gi,#[])
        (step I cv rd ?sh tm)=.ok ?next := by assumption
    have hh := loop_values I cv rd _ _ tm B _ _ hB hs hi he
    exact hh

theorem rounds_values (I : Input) (cv : Array CReq) (key : List Nat) (rs : List Round)
    (B : Nat) (s out : ProcActualReplayRound.Acc) (hB : 0<B)
    (hs : Inv B (ProcActualReplayRound.entryAcc s)) (hi : Increments B cv)
    (h : forIn rs s (ProcActualReplayRound.step I cv key)=.ok out) :
    Inv B (ProcActualReplayRound.entryAcc out) := by
  induction rs generalizing s with
  | nil => simp only [List.forIn_nil] at h; cases h; exact hs
  | cons rd rs ih =>
    rw [List.forIn_cons] at h
    cases he : ProcActualReplayRound.step I cv key rd s with
    | error e => simp only [he,bind,Except.bind] at h; cases h
    | ok next =>
      obtain ⟨next,rfl⟩ := ProcActualRoundTransition.step_yields I cv key rd s next he
      simp only [he,bind,Except.bind] at h
      exact ih next (round_values I cv key rd B s next hB hs hi he) h

theorem empty_values (B n : Nat) : Values B (Array.replicate n #[]) := by
  intro ops hm
  have he : ops=#[] := (by simpa using hm : n≠0 ∧ ops=#[]).2
  subst ops
  simp

theorem reads_values (B : Nat) (aa gg : Array Nat) (cs : List CReq)
    (s out : Array (Array Gen.MOp)) (hs : Values B s)
    (h : forIn cs s (ProcActualReplayFactor.readStep aa gg)=.ok out) : Values B out := by
  apply ExceptLoop.invariant cs _ (Values B) _ s out hs h
  intro c hm a ha next hn
  simp only [ProcActualReplayFactor.readStep,Except.ok.injEq] at hn
  subst next
  exact modify_values B a c.link _ ha (by intro h; cases h)

theorem initial_values (I : Input) (cv : Array CReq) (ops : Array (Array Gen.MOp))
    (hp : Params.calculate Config.pv86 I.ids.length=some I.p)
    (ho : Values (2^29) ops) :
    Inv (2^29) (ProcActualReplayRound.entryAcc (ProcActualReplayInitial.initial I cv ops)) := by
  have hb : ∀(xs : List Nat) (i : Nat),
      ((xs.toArray.map fun c=>I.p.maxShardBandwidth-I.p.base*c)[i]!)≤2^29-1 := by
    intro xs i
    simp only [getElem!_def,Array.getElem?_map]
    split
    · next h =>
      simp only [Option.map_eq_some_iff] at h
      rcases h with ⟨c,hc,rfl⟩
      have hh := Nat.sub_le I.p.maxShardBandwidth (I.p.base*c)
      have hm : I.p.maxShardBandwidth=4500000 := by rw [lp_calc hp]
      omega
    · exact Nat.zero_le _
  refine ⟨?_,?_,?_,ho,empty_values _ _,empty_values _ _⟩
  · exact hb _
  · exact hb _
  · intro i
    have hh := ProcActualReplayAllowance.link_bound I.ids.length I.p I.allowed
      (ProcActualInput.allowances I.ids I.prev) i
    have hm : I.p.maxAllowance=4500000 := by rw [lp_calc hp]
    change (linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev)).a2[i]!≤2^29-1
    omega

theorem replay_values (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (cv : Array CReq) (rs : List Round)
    (out : ProcActualReplayRound.Acc)
    (hcv : forIn (ProcPreparedSequence.input sp prev).raw #[]
      (ProcActualConverted.step (ProcPreparedSequence.input sp prev))=.ok cv)
    (hr : ProcActualReplayFactor.replay (ProcPreparedSequence.input sp prev) cv rs=.ok out) :
    Inv (2^29) (ProcActualReplayRound.entryAcc out) := by
  let I := ProcPreparedSequence.input sp prev
  let lp := linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev)
  obtain ⟨ops,hop⟩ := ProcActualReplayTotal.reads_array lp.a2 lp.g2 cv (Array.replicate (I.ids.length*I.ids.length) #[])
  have hv : Values (2^29) ops := reads_values _ lp.a2 lp.g2 cv.toList _ ops (empty_values _ _)
    (by simpa only [Array.forIn_toList] using hop)
  change (forIn cv _ (ProcActualReplayFactor.readStep lp.a2 lp.g2) >>= fun ops =>
    forIn rs (ProcActualReplayInitial.initial I cv ops)
      (ProcActualReplayRound.step I cv (NearSpecV3.leWords sp.seed)))=.ok out at hr
  rw [hop] at hr
  exact rounds_values I cv _ rs _ _ out (by decide)
    (initial_values I cv ops hs.params hv) (converted_values sp hs prev cv hcv) hr
end ZkFormal.NearV3.Candidates.ProcActualMemoryValues
