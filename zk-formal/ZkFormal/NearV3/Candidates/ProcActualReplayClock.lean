import ZkFormal.NearV3.Candidates.ProcActualGeneratedPush
namespace ZkFormal.NearV3.Candidates.ProcActualReplayClock
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcActualReplayRound

def Clock (s : Acc) : Prop := time s=T0+ProcActualEntryTransition.cursor (entryAcc s)

set_option maxHeartbeats 800000 in
theorem round_clock (I : Input) (cv : Array CReq) (key : List Nat) (rd : Round)
    (s out : Acc) (hc : Clock s) (h : step I cv key rd s=.ok (.yield out)) : Clock out := by
  rcases s with ⟨sb,rb,aa,gg,ol,os,orr,ps,bs,tm,kp,kq,zq,used,rs,gi⟩
  change tm=T0+gi at hc
  unfold step at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals
    have he := ProcActualEntryTransition.loop_effect I cv rd ?sh tm
      (List.range rd.bucket.length) (sb,rb,aa,gg,ol,os,orr,ps,used,gi,#[]) ?next
      (ZkFormal.Chacha.rngAt key kp) (by assumption)
    simp only [List.length_range,ProcActualEntryTransition.cursor] at he
    dsimp only [Clock,time,entryAcc,ProcActualEntryTransition.cursor]
    rw [he.2.1]
    omega

theorem loop_clock (I : Input) (cv : Array CReq) (key : List Nat) (rs : List Round)
    (s out : Acc) (hc : Clock s) (h : forIn rs s (step I cv key)=.ok out) : Clock out := by
  induction rs generalizing s with
  | nil => simp only [List.forIn_nil] at h; cases h; exact hc
  | cons rd rs ih =>
    rw [List.forIn_cons] at h
    cases he : step I cv key rd s with
    | error e => simp only [he,bind,Except.bind] at h; cases h
    | ok next =>
      obtain ⟨next,rfl⟩ := ProcActualRoundTransition.step_yields I cv key rd s next he
      simp only [he,bind,Except.bind] at h
      exact ih next (round_clock I cv key rd s next hc he) h

theorem initial_clock (I : Input) (cv : Array CReq) (ops : Array (Array Gen.MOp)) :
    Clock (ProcActualReplayInitial.initial I cv ops) := by
  simp [Clock,time,entryAcc,ProcActualEntryTransition.cursor,ProcActualReplayInitial.initial]

theorem replay_clock (I : Input) (cv : Array CReq) (rs : List Round) (out : Acc)
    (h : ProcActualReplayFactor.replay I cv rs=.ok out) : Clock out := by
  let lp := linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev)
  obtain ⟨ops,hop⟩ := ProcActualReplayTotal.reads_array lp.a2 lp.g2 cv
    (Array.replicate (I.ids.length*I.ids.length) #[])
  change (forIn cv _ (ProcActualReplayFactor.readStep lp.a2 lp.g2) >>= fun ops =>
    forIn rs (ProcActualReplayInitial.initial I cv ops) (step I cv (NearSpecV3.leWords I.seed)))=.ok out at h
  rw [hop] at h
  exact loop_clock I cv _ rs _ out (initial_clock I cv ops) h
end ZkFormal.NearV3.Candidates.ProcActualReplayClock
