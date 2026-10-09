import ZkFormal.NearV3.Candidates.ProcActualMemoryChainEntry
namespace ZkFormal.NearV3.Candidates.ProcActualMemoryChainReplay
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcActualReplayEntry ProcActualMemoryChainEntry
theorem entries (I : Input) (cv : Array CReq) (rd : Round) (sh xs : List Nat)
    (T : Nat) (v0 w0 s0 r0 : Array Nat) (s out : Acc) (hs : Inv I v0 w0 s0 r0 s)
    (hf : ProcActualMemoryFinal.Inv v0 w0 s0 r0 s)
    (h : forIn xs s (step I cv rd sh T)=.ok out) : Inv I v0 w0 s0 r0 out := by
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
      exact ih next (entry I cv rd sh T x v0 w0 s0 r0 s next hs hf he)
        (ProcActualMemoryFinal.step_final I cv rd sh T x v0 w0 s0 r0 s next hf he) h

open ProcActualReplayRound in
set_option maxHeartbeats 800000 in
theorem round (I : Input) (cv : Array CReq) (key : List Nat) (rd : Round)
    (v0 w0 s0 r0 : Array Nat) (s out : ProcActualReplayRound.Acc)
    (hs : Inv I v0 w0 s0 r0 (entryAcc s))
    (hf : ProcActualMemoryFinal.Inv v0 w0 s0 r0 (entryAcc s))
    (h : ProcActualReplayRound.step I cv key rd s=.ok (.yield out)) :
    Inv I v0 w0 s0 r0 (entryAcc out) := by
  rcases s with ⟨sb,rb,aa,gg,ol,os,orr,ps,bs,tm,kp,kq,zq,used,rs,gi⟩
  unfold ProcActualReplayRound.step at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals
    have he : forIn (List.range rd.bucket.length) (sb,rb,aa,gg,ol,os,orr,ps,used,gi,#[])
        (step I cv rd ?sh tm)=.ok ?next := by assumption
    have hh := entries I cv rd _ _ tm v0 w0 s0 r0 _ _ hs hf he
    exact hh

theorem rounds (I : Input) (cv : Array CReq) (key : List Nat) (rs : List Round)
    (v0 w0 s0 r0 : Array Nat) (s out : ProcActualReplayRound.Acc)
    (hs : Inv I v0 w0 s0 r0 (ProcActualReplayRound.entryAcc s))
    (hf : ProcActualMemoryFinal.Inv v0 w0 s0 r0 (ProcActualReplayRound.entryAcc s))
    (h : forIn rs s (ProcActualReplayRound.step I cv key)=.ok out) :
    Inv I v0 w0 s0 r0 (ProcActualReplayRound.entryAcc out) := by
  induction rs generalizing s with
  | nil => simp only [List.forIn_nil] at h; cases h; exact hs
  | cons rd rs ih =>
    rw [List.forIn_cons] at h
    cases he : ProcActualReplayRound.step I cv key rd s with
    | error e => simp only [he,bind,Except.bind] at h; cases h
    | ok next =>
      obtain ⟨next,rfl⟩ := ProcActualRoundTransition.step_yields I cv key rd s next he
      simp only [he,bind,Except.bind] at h
      exact ih next (round I cv key rd v0 w0 s0 r0 s next hs hf he)
        (ProcActualMemoryFinal.round_final I cv key rd v0 w0 s0 r0 s next hf he) h

theorem replay (I : Input) (cv : Array CReq) (rs : List Round)
    (out : ProcActualReplayRound.Acc)
    (hr:ProcActualReplayFactor.replay I cv rs=.ok out) :
    let lp:=linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev)
    Inv I lp.a2 lp.g2 lp.sb lp.rb (ProcActualReplayRound.entryAcc out) := by
  let lp:=linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev)
  obtain ⟨ops,hop⟩:=ProcActualReplayTotal.reads_array lp.a2 lp.g2 cv
    (Array.replicate (I.ids.length*I.ids.length) #[])
  have hv:=ProcActualMemoryChainReads.reads (linkSeg I lp.a2 lp.g2) lp.a2 lp.g2
    (fun _=>rfl) (fun _=>rfl) cv.toList _ ops
    (ProcActualMemoryChainReads.empty _ _ _ (I.ids.length*I.ids.length)
      (by simp [lp,linkPass]) (by simp [lp,linkPass]))
    (by simpa only [Array.forIn_toList] using hop)
  change (forIn cv _ (ProcActualReplayFactor.readStep lp.a2 lp.g2) >>= fun ops=>
    forIn rs (ProcActualReplayInitial.initial I cv ops)
      (ProcActualReplayRound.step I cv (NearSpecV3.leWords I.seed)))=.ok out at hr
  rw [hop] at hr
  apply rounds I cv _ rs lp.a2 lp.g2 lp.sb lp.rb (ProcActualReplayInitial.initial I cv ops) out ?_ ?_ hr
  · exact ⟨hv.1,ProcActualMemoryChains.empty _ _,ProcActualMemoryChains.empty _ _⟩
  · exact ⟨hv.2.1,hv.2.2,
      ProcActualMemoryFinal.empty_ends _ _ _ (by simp [lp,linkPass]),
      ProcActualMemoryFinal.empty_ends _ _ _ (by simp [lp,linkPass])⟩
end ZkFormal.NearV3.Candidates.ProcActualMemoryChainReplay
