import ZkFormal.NearV3.Candidates.ProcActualGrantMemory
namespace ZkFormal.NearV3.Candidates.ProcActualReplayMemory
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcActualReplayRound
open ProcMemoryTimeInvariant

def Memory (s : Acc) : Prop :=
  ProcActualGrantMemory.LogsBefore (time s) (entryAcc s) ∧ 0<time s

set_option maxHeartbeats 800000 in
theorem round_memory (I : Input) (cv : Array CReq) (key : List Nat) (rd : Round)
    (s out : Acc) (hs : Memory s) (h : step I cv key rd s=.ok (.yield out)) : Memory out := by
  rcases s with ⟨sb,rb,aa,gg,ol,os,orr,ps,bs,tm,kp,kq,zq,used,rs,gi⟩
  unfold step at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals
    have he : forIn (List.range rd.bucket.length) (sb,rb,aa,gg,ol,os,orr,ps,used,gi,#[])
        (ProcActualReplayEntry.step I cv rd ?sh tm)=.ok ?next := by assumption
    have hm := ProcActualGrantMemory.loop_logs I cv rd _ tm 0 rd.bucket.length _ _
      (by simpa only [Nat.add_zero,time,entryAcc] using hs.1) (by simpa only [Nat.add_zero,time,entryAcc] using hs.2)
      (by simpa only [List.range_eq_range',entryAcc] using he)
    refine ⟨?_,?_⟩
    · simpa only [Memory,time,entryAcc,ProcActualGrantMemory.LogsBefore,Nat.add_zero] using hm
    · have ht := hs.2
      change 0<tm at ht
      change 0<tm+rd.bucket.length
      omega

theorem loop_memory (I : Input) (cv : Array CReq) (key : List Nat) (rs : List Round)
    (s out : Acc) (hs : Memory s) (h : forIn rs s (step I cv key)=.ok out) : Memory out := by
  induction rs generalizing s with
  | nil => simp only [List.forIn_nil] at h; cases h; exact hs
  | cons rd rs ih =>
    rw [List.forIn_cons] at h
    cases he : step I cv key rd s with
    | error e => simp only [he,bind,Except.bind] at h; cases h
    | ok next =>
      obtain ⟨next,rfl⟩ := ProcActualRoundTransition.step_yields I cv key rd s next he
      simp only [he,bind,Except.bind] at h
      exact ih next (round_memory I cv key rd s next hs he) h

theorem initial_memory (I : Input) (cv : Array CReq) (ops : Array (Array Gen.MOp))
    (h : AllBefore T0 ops) : Memory (ProcActualReplayInitial.initial I cv ops) := by
  exact ⟨⟨h,empty_logs _ _,empty_logs _ _⟩,by change 0<T0; decide⟩

open NearSpecV3.Scheduler in
theorem replay_memory (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (cv : Array CReq) (rs : List Round) (out : Acc)
    (hcv : forIn (ProcPreparedSequence.input sp prev).raw #[]
      (ProcActualConverted.step (ProcPreparedSequence.input sp prev))=.ok cv)
    (hr : ProcActualReplayFactor.replay (ProcPreparedSequence.input sp prev) cv rs=.ok out) :
    Memory out := by
  let I := ProcPreparedSequence.input sp prev
  let lp := linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev)
  obtain ⟨ops,hop,hb⟩ := ProcActualReadMemory.prepared_reads sp hs prev cv hcv
  change (forIn cv _ (ProcActualReplayFactor.readStep lp.a2 lp.g2) >>= fun ops =>
    forIn rs (ProcActualReplayInitial.initial I cv ops) (step I cv (NearSpecV3.leWords sp.seed)))=.ok out at hr
  rw [hop] at hr
  exact loop_memory I cv _ rs _ out (initial_memory I cv ops hb) hr
theorem selected_ordered (t : Nat) (logs : Array (Array Gen.MOp)) (h : AllBefore t logs) (i : Nat) :
    Ordered logs[i]! := by
  by_cases hi : i<logs.size
  · rw [getElem!_pos logs i hi]
    exact (h _ (Array.getElem_mem_toList hi)).1
  · rw [getElem!_neg logs i hi]
    change Ordered #[]
    simp [Ordered]

def Scans (logs : Array (Array Gen.MOp)) : Prop :=
  ∀(i : Nat) (cs : Array (Nat×Nat×Nat)),∃out,forIn logs[i]!.toList (0,cs) scanStep=.ok out

theorem memory_scans (s : Acc) (h : Memory s) :
    Scans s.2.2.2.2.1 ∧ Scans s.2.2.2.2.2.1 ∧ Scans s.2.2.2.2.2.2.1 := by
  have applyScan : ∀logs,AllBefore (time s) logs → Scans logs := by
    intro logs hb i cs
    exact ordered_scan _ cs (selected_ordered _ logs hb i)
  exact ⟨applyScan _ h.1.1,applyScan _ h.1.2.1,applyScan _ h.1.2.2⟩
end ZkFormal.NearV3.Candidates.ProcActualReplayMemory
