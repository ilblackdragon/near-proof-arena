import ZkFormal.NearV3.Candidates.ProcActualSegments
import ZkFormal.NearV3.Candidates.ProcActualAfterMemoryReduction
namespace ZkFormal.NearV3.Candidates.ProcActualMemoryFinal
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcActualReplayEntry

def lastValue (f : Gen.MOp → Nat) (v0 : Nat) (ops : Array Gen.MOp) : Nat :=
  match ops.toList.getLast? with | some o=>f o | none=>v0

def Ends (f : Gen.MOp → Nat) (v0 cur : Array Nat) (logs : Array (Array Gen.MOp)) : Prop :=
  logs.size=cur.size ∧ ∀i, i<logs.size → lastValue f v0[i]! logs[i]! = cur[i]!

theorem push_last (f : Gen.MOp → Nat) (v0 : Nat) (ops : Array Gen.MOp) (o : Gen.MOp) :
    lastValue f v0 (ops.push o)=f o := by simp [lastValue]

theorem modify_ends (f : Gen.MOp → Nat) (v0 cur : Array Nat)
    (logs : Array (Array Gen.MOp)) (h : Ends f v0 cur logs) (i v : Nat) (o : Gen.MOp)
    (ho : f o=v) : Ends f v0 (cur.set! i v) (logs.modify i (·.push o)) := by
  constructor
  · simpa using h.1
  · intro j hj
    have hj' : j<logs.size := by simpa using hj
    have hc : j<cur.size := by rw [←h.1]; exact hj'
    by_cases hij : i=j
    · subst j
      rw [Array.getElem!_set!_self cur i v hc,
        getElem!_pos (logs.modify i (·.push o)) i (by simpa using hj'),Array.getElem_modify_self]
      exact (push_last _ _ _ _).trans ho
    · rw [Array.getElem!_set!_ne cur i j v hij,
        getElem!_pos (logs.modify i (·.push o)) j (by simpa using hj'),Array.getElem_modify_of_ne hij]
      simpa only [getElem!_pos logs j hj'] using h.2 j hj'

def Inv (v0 w0 s0 r0 : Array Nat) (s : Acc) : Prop :=
  Ends Gen.MOp.v v0 s.2.2.1 s.2.2.2.2.1 ∧
  Ends Gen.MOp.w w0 s.2.2.2.1 s.2.2.2.2.1 ∧
  Ends Gen.MOp.v s0 s.1 s.2.2.2.2.2.1 ∧
  Ends Gen.MOp.v r0 s.2.1 s.2.2.2.2.2.2.1

set_option maxHeartbeats 1000000 in
theorem step_final (I : Input) (cv : Array CReq) (rd : Round) (sh : List Nat)
    (T x : Nat) (v0 w0 s0 r0 : Array Nat) (s out : Acc) (hs : Inv v0 w0 s0 r0 s)
    (h : step I cv rd sh T x s=.ok (.yield out)) : Inv v0 w0 s0 r0 out := by
  rcases s with ⟨sb,rb,aa,gg,ol,os,orr,ps,used,gi,es⟩
  unfold step at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals exact ⟨modify_ends _ _ _ _ hs.1 _ _ _ rfl,
    modify_ends _ _ _ _ hs.2.1 _ _ _ rfl,modify_ends _ _ _ _ hs.2.2.1 _ _ _ rfl,
    modify_ends _ _ _ _ hs.2.2.2 _ _ _ rfl⟩

theorem loop_final (I : Input) (cv : Array CReq) (rd : Round) (sh xs : List Nat)
    (T : Nat) (v0 w0 s0 r0 : Array Nat) (s out : Acc) (hs : Inv v0 w0 s0 r0 s)
    (h : forIn xs s (step I cv rd sh T)=.ok out) : Inv v0 w0 s0 r0 out := by
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
      exact ih next (step_final I cv rd sh T x v0 w0 s0 r0 s next hs he) h

open ProcActualReplayRound in
set_option maxHeartbeats 800000 in
theorem round_final (I : Input) (cv : Array CReq) (key : List Nat) (rd : Round)
    (v0 w0 s0 r0 : Array Nat) (s out : ProcActualReplayRound.Acc)
    (hs : Inv v0 w0 s0 r0 (entryAcc s))
    (h : ProcActualReplayRound.step I cv key rd s=.ok (.yield out)) :
    Inv v0 w0 s0 r0 (entryAcc out) := by
  rcases s with ⟨sb,rb,aa,gg,ol,os,orr,ps,bs,tm,kp,kq,zq,used,rs,gi⟩
  unfold ProcActualReplayRound.step at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals
    have he : forIn (List.range rd.bucket.length) (sb,rb,aa,gg,ol,os,orr,ps,used,gi,#[])
        (step I cv rd ?sh tm)=.ok ?next := by assumption
    have hh := loop_final I cv rd _ _ tm v0 w0 s0 r0 _ _ hs he
    exact hh

theorem rounds_final (I : Input) (cv : Array CReq) (key : List Nat) (rs : List Round)
    (v0 w0 s0 r0 : Array Nat) (s out : ProcActualReplayRound.Acc)
    (hs : Inv v0 w0 s0 r0 (ProcActualReplayRound.entryAcc s))
    (h : forIn rs s (ProcActualReplayRound.step I cv key)=.ok out) :
    Inv v0 w0 s0 r0 (ProcActualReplayRound.entryAcc out) := by
  induction rs generalizing s with
  | nil => simp only [List.forIn_nil] at h; cases h; exact hs
  | cons rd rs ih =>
    rw [List.forIn_cons] at h
    cases he : ProcActualReplayRound.step I cv key rd s with
    | error e => simp only [he,bind,Except.bind] at h; cases h
    | ok next =>
      obtain ⟨next,rfl⟩ := ProcActualRoundTransition.step_yields I cv key rd s next he
      simp only [he,bind,Except.bind] at h
      exact ih next (round_final I cv key rd v0 w0 s0 r0 s next hs he) h

theorem empty_ends (f : Gen.MOp → Nat) (v0 : Array Nat) (n : Nat) (hn : n=v0.size) :
    Ends f v0 v0 (Array.replicate n #[]) := by
  constructor
  · simpa using hn
  · intro i hi
    simp only [Array.size_replicate] at hi
    rw [getElem!_pos (Array.replicate n (#[] : Array Gen.MOp)) i (by simpa using hi)]
    simp [lastValue]

theorem set_self (a : Array Nat) (i : Nat) : a.set! i a[i]! = a := by
  by_cases hi : i<a.size
  · simp [Array.set!_eq_setIfInBounds,Array.setIfInBounds,hi]
  · simp [Array.set!_eq_setIfInBounds,Array.setIfInBounds,hi]

theorem reads_final (aa gg : Array Nat) (cs : List CReq)
    (s out : Array (Array Gen.MOp)) (hs : Ends Gen.MOp.v aa aa s ∧ Ends Gen.MOp.w gg gg s)
    (h : forIn cs s (ProcActualReplayFactor.readStep aa gg)=.ok out) :
    Ends Gen.MOp.v aa aa out ∧ Ends Gen.MOp.w gg gg out := by
  apply ExceptLoop.invariant cs _ (fun s=>Ends Gen.MOp.v aa aa s ∧ Ends Gen.MOp.w gg gg s) _ s out hs h
  intro c hm a ha next hn
  simp only [ProcActualReplayFactor.readStep,Except.ok.injEq] at hn
  subst next
  constructor
  · have hh := modify_ends Gen.MOp.v aa aa a ha.1 c.link aa[c.link]!
      ⟨c.cid+1,OP_READ,aa[c.link]!,aa[c.link]!,gg[c.link]!,gg[c.link]!,0,false,false,false⟩ rfl
    simpa only [set_self] using hh
  · have hh := modify_ends Gen.MOp.w gg gg a ha.2 c.link gg[c.link]!
      ⟨c.cid+1,OP_READ,aa[c.link]!,aa[c.link]!,gg[c.link]!,gg[c.link]!,0,false,false,false⟩ rfl
    simpa only [set_self] using hh

def ReplayInv (I : Input) (s : ProcActualReplayRound.Acc) : Prop :=
  let lp := linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev)
  Inv lp.a2 lp.g2 lp.sb lp.rb (ProcActualReplayRound.entryAcc s)

theorem replay_final (I : Input) (cv : Array CReq) (rs : List Round)
    (out : ProcActualReplayRound.Acc)
    (hr : ProcActualReplayFactor.replay I cv rs=.ok out) : ReplayInv I out := by
  let lp := linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev)
  obtain ⟨ops,hop⟩ := ProcActualReplayTotal.reads_array lp.a2 lp.g2 cv (Array.replicate (I.ids.length*I.ids.length) #[])
  have hv := reads_final lp.a2 lp.g2 cv.toList _ ops
    ⟨empty_ends _ _ (I.ids.length*I.ids.length) (by simp [lp,linkPass]),empty_ends _ _ (I.ids.length*I.ids.length) (by simp [lp,linkPass])⟩
    (by simpa only [Array.forIn_toList] using hop)
  change (forIn cv _ (ProcActualReplayFactor.readStep lp.a2 lp.g2) >>= fun ops =>
    forIn rs (ProcActualReplayInitial.initial I cv ops)
      (ProcActualReplayRound.step I cv (NearSpecV3.leWords I.seed)))=.ok out at hr
  rw [hop] at hr
  exact rounds_final I cv _ rs lp.a2 lp.g2 lp.sb lp.rb (ProcActualReplayInitial.initial I cv ops) out
    ⟨hv.1,hv.2,empty_ends _ _ _ (by simp [lp,linkPass]),empty_ends _ _ _ (by simp [lp,linkPass])⟩ hr

/-- The actual link segment's endpoint equals the replay arrays, for every
valid current-layout link. Original initial values remain the empty-log default. -/
theorem link_final (I : Input) (tau : Nat) (cv : Array CReq) (rs : List Round)
    (out : ProcActualReplayRound.Acc) (i : Nat)
    (hi : i<out.2.2.2.2.1.size)
    (hr : ProcActualReplayFactor.replay I cv rs=.ok out) :
    (ProcActualSegments.make I tau out 0 i).vfin=out.2.2.1[i]! ∧
    (ProcActualSegments.make I tau out 0 i).wfin=out.2.2.2.1[i]! := by
  have h := replay_final I cv rs out hr
  exact ⟨h.1.2 i hi,h.2.1.2 i hi⟩

/-- Replay state alignment identifies the memory endpoint with model-final grants. -/
theorem aligned_link_final (I : Input) (tau : Nat) (cv : Array CReq) (rs : List Round)
    (out : ProcActualReplayRound.Acc) (st : PState) (t i : Nat)
    (hi : i<out.2.2.2.2.1.size)
    (hr : ProcActualReplayFactor.replay I cv rs=.ok out)
    (ha : ProcActualRoundTransition.Aligned (NearSpecV3.leWords I.seed) cv out st t) :
    (ProcActualSegments.make I tau out 0 i).vfin=st.al[i]! ∧
    (ProcActualSegments.make I tau out 0 i).wfin=st.g[i]! := by
  have hh := link_final I tau cv rs out i hi hr
  have hva := congrArg PState.al ha.1
  have hvg := congrArg PState.g ha.1
  change out.2.2.1=st.al at hva
  change out.2.2.2.1=st.g at hvg
  simpa only [hva,hvg] using hh

theorem processed_link_final (I : Input) (tau : Nat) (cv : Array CReq) (rs : List Round)
    (out : ProcActualReplayRound.Acc) (st : PState) (t i : Nat)
    (hi : i<I.ids.length*I.ids.length)
    (hp : ProcActualInput.process I=.ok (st,rs))
    (hr : ProcActualReplayFactor.replay I cv rs=.ok out)
    (ha : ProcActualRoundTransition.Aligned (NearSpecV3.leWords I.seed) cv out st t) :
    (ProcActualSegments.make I tau out 0 i).vfin=st.al[i]! ∧
    (ProcActualSegments.make I tau out 0 i).wfin=st.g[i]! := by
  have hv := replay_final I cv rs out hr
  have he := congrArg PState.al ha.1
  change out.2.2.1=st.al at he
  have hsize := hv.1.1
  change out.2.2.2.2.1.size=out.2.2.1.size at hsize
  rw [he,ProcActualAllowanceShape.actual_process_shape I st rs hp] at hsize
  exact aligned_link_final I tau cv rs out st t i (by omega) hr ha

open NearSpecV3.Scheduler in
theorem prepared_link_final (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (tau : Nat) (cv : Array CReq) (rs : List Round)
    (out : ProcActualReplayRound.Acc) (st : PState) (i : Nat)
    (hi : i<sp.ids.length*sp.ids.length)
    (hcv : forIn (ProcPreparedSequence.input sp prev).raw #[]
      (ProcActualConverted.step (ProcPreparedSequence.input sp prev))=.ok cv)
    (hp : ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs))
    (hr : ProcActualReplayFactor.replay (ProcPreparedSequence.input sp prev) cv rs=.ok out) :
    (ProcActualSegments.make (ProcPreparedSequence.input sp prev) tau out 0 i).vfin=st.al[i]! ∧
    (ProcActualSegments.make (ProcPreparedSequence.input sp prev) tau out 0 i).wfin=st.g[i]! := by
  obtain ⟨out',last,hr',ha,_⟩ := ProcActualReplayTotal.prepared_replay sp hs prev cv st rs hcv hp
  have he := Except.ok.inj (hr'.symm.trans hr)
  subst out'
  exact processed_link_final _ tau cv rs out st last i hi hp hr ha

theorem append_records (f : Nat → Gen.Seg) (xs : List Nat) (gs out : Array Gen.Seg)
    (h : forIn xs gs (ProcActualSegments.appendStep f)=.ok out) :
    out.toList=gs.toList++xs.map f := by
  induction xs generalizing gs with
  | nil => simp only [List.forIn_nil] at h; cases h; simp
  | cons i xs ih =>
    simp only [List.forIn_cons,ProcActualSegments.appendStep,bind,Except.bind] at h
    rw [ih _ h]
    simp [List.append_assoc]

theorem build_records (I : Input) (tau : Nat) (s : ProcActualReplayRound.Acc) (gs : Array Gen.Seg)
    (h : ProcActualSegments.build I tau s=.ok gs) :
    gs.toList=(List.range (I.ids.length*I.ids.length)).map (ProcActualSegments.make I tau s 0) ++
      (List.range I.ids.length).map (ProcActualSegments.make I tau s 1) ++
      (List.range I.ids.length).map (ProcActualSegments.make I tau s 2) := by
  unfold ProcActualSegments.build at h
  cases ha : forIn (List.range (I.ids.length*I.ids.length)) #[]
      (ProcActualSegments.appendStep (ProcActualSegments.make I tau s 0)) with
  | error e => simp only [ha,bind,Except.bind] at h; cases h
  | ok a =>
    simp only [ha,bind,Except.bind] at h
    cases hb : forIn (List.range I.ids.length) a
        (ProcActualSegments.appendStep (ProcActualSegments.make I tau s 1)) with
    | error e => simp only [hb] at h; cases h
    | ok b =>
      simp only [hb] at h
      rw [append_records _ _ _ _ h,append_records _ _ _ _ hb,append_records _ _ _ _ ha]
      simp

theorem build_link (I : Input) (tau : Nat) (s : ProcActualReplayRound.Acc) (gs : Array Gen.Seg)
    (h : ProcActualSegments.build I tau s=.ok gs) (i : Nat) (hi : i<I.ids.length*I.ids.length) :
    gs.toList.getD i default=ProcActualSegments.make I tau s 0 i := by
  rw [build_records I tau s gs h]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simpa using (by omega : i<I.ids.length*I.ids.length+I.ids.length)),
    List.getElem?_append_left (by simpa using hi)]
  simp [hi]

/-- Successful suffix execution retains the segment list built before comparison checks. -/
theorem afterMemory_segments (I : Input) (tau : Nat) (cv : Array CReq) (st : PState)
    (s : ProcActualReplayRound.Acc) (gs : Array Gen.Seg) (cs : ProcActualMemoryScan.Cmps) (R : Run)
    (h : ProcActualSegmentFactor.afterMemory I tau cv st s gs cs=.ok R) : R.segs=gs.toList := by
  unfold ProcActualSegmentFactor.afterMemory at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals rfl

open NearSpecV3.Scheduler in
theorem suffix_link_final (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (tau : Nat) (cv : Array CReq) (rs : List Round)
    (st : PState) (R : Run) (i : Nat) (hi : i<sp.ids.length*sp.ids.length)
    (hcv : forIn (ProcPreparedSequence.input sp prev).raw #[]
      (ProcActualConverted.step (ProcPreparedSequence.input sp prev))=.ok cv)
    (hp : ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs))
    (hr : ProcActualRoundFactor.runRestRounds (ProcPreparedSequence.input sp prev) tau cv st rs=.ok R) :
    (R.segs.getD i default).vfin=st.al[i]! ∧ (R.segs.getD i default).wfin=st.g[i]! := by
  obtain ⟨out,last,hout,_,_⟩ := ProcActualReplayTotal.prepared_replay sp hs prev cv st rs hcv hp
  obtain ⟨a,ha,hpush⟩ := ProcActualPushLogGuard.replay_push_guard sp hs prev cv st rs hcv hp
  have he := Except.ok.inj (ha.symm.trans hout)
  subst a
  have hm := ProcActualReplayMemory.replay_memory sp hs prev cv rs out hcv hout
  obtain ⟨a,last,ha,halign,hfinal⟩ := ProcActualReplayTotal.prepared_replay sp hs prev cv st rs hcv hp
  have he := Except.ok.inj (ha.symm.trans hout)
  subst a
  obtain ⟨gs,cs,hfinish,hbuild,_⟩ := ProcActualAfterMemoryReduction.finish_reduction
    _ tau cv st out hpush hfinal hm
  rw [ProcActualReplayFactor.rest_eq,hout] at hr
  change ProcActualReplayFactor.finish _ tau cv st out=.ok R at hr
  rw [hfinish] at hr
  rw [afterMemory_segments _ tau cv st out gs cs R hr,build_link _ tau out gs hbuild i hi]
  exact prepared_link_final sp hs prev tau cv rs out st i hi hcv hp hout

open NearSpecV3.Scheduler in
theorem run_link_final (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (tau : Nat) (cv : Array CReq) (rs : List Round)
    (st : PState) (ev : Ev) (R : Run) (i : Nat) (hi : i<sp.ids.length*sp.ids.length)
    (hprefix : ProcActualPrefix.runPrefix (ProcPreparedSequence.input sp prev)=.ok (cv,st,rs,ev))
    (hr : ActualRun.run (ProcPreparedSequence.input sp prev) tau=.ok R) :
    (R.segs.getD i default).vfin=st.al[i]! ∧ (R.segs.getD i default).wfin=st.g[i]! := by
  obtain ⟨hc,hp⟩ := ProcActualAfterMemoryReduction.prefix_facts _ cv st rs ev hprefix
  rw [ProcActualRunFactor.run_of_prefix _ tau cv st rs ev hprefix,
    ProcActualEntryFactor.rest_eq,ProcActualRoundFactor.rest_eq] at hr
  exact suffix_link_final sp hs prev tau cv rs st R i hi hc hp hr
end ZkFormal.NearV3.Candidates.ProcActualMemoryFinal
