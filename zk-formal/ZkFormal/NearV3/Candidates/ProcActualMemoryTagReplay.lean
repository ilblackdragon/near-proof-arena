import ZkFormal.NearV3.Candidates.ProcActualMemoryTags
namespace ZkFormal.NearV3.Candidates.ProcActualMemoryTagReplay
open NearSpecV3.Scheduler ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcActualReplayEntry ProcActualMemoryTags

open ProcActualReplayRound in
set_option maxHeartbeats 800000 in
theorem round (I : Input) (cv : Array CReq) (key : List Nat) (rd : Round)
    (s out : ProcActualReplayRound.Acc) (hs:Inv (entryAcc s))
    (h:ProcActualReplayRound.step I cv key rd s=.ok (.yield out)) : Inv (entryAcc out) := by
  rcases s with ⟨sb,rb,aa,gg,ol,os,orr,ps,bs,tm,kp,kq,zq,used,rs,gi⟩
  unfold ProcActualReplayRound.step at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals
    have he:forIn (List.range rd.bucket.length) (sb,rb,aa,gg,ol,os,orr,ps,used,gi,#[])
        (step I cv rd ?sh tm)=.ok ?next := by assumption
    have hh:=entries I cv rd _ _ tm _ _ hs he
    exact hh

theorem rounds (I : Input) (cv : Array CReq) (key : List Nat) (rs : List Round)
    (s out : ProcActualReplayRound.Acc) (hs:Inv (ProcActualReplayRound.entryAcc s))
    (h:forIn rs s (ProcActualReplayRound.step I cv key)=.ok out) : Inv (ProcActualReplayRound.entryAcc out) := by
  induction rs generalizing s with
  | nil=>simp only [List.forIn_nil] at h;cases h;exact hs
  | cons rd rs ih=>
    rw [List.forIn_cons] at h
    cases he:ProcActualReplayRound.step I cv key rd s with
    | error e=>simp only [he,bind,Except.bind] at h;cases h
    | ok next=>
      obtain ⟨next,rfl⟩:=ProcActualRoundTransition.step_yields I cv key rd s next he
      simp only [he,bind,Except.bind] at h
      exact ih next (round I cv key rd s next hs he) h

theorem empty (n : Nat) : Logs (Array.replicate n #[]) := by
  intro ops hm
  have he:ops=#[] := (by simpa using hm : n≠0 ∧ ops=#[]).2
  subst ops
  simp

theorem reads (aa gg : Array Nat) (cs : List CReq) (s out : Array (Array Gen.MOp))
    (hs:Logs s) (h:forIn cs s (ProcActualReplayFactor.readStep aa gg)=.ok out) : Logs out := by
  apply ExceptLoop.invariant cs _ Logs _ s out hs h
  intro c hm a ha next hn
  simp only [ProcActualReplayFactor.readStep,Except.ok.injEq] at hn
  subst next
  exact modify a c.link _ ha (by simp [OpTag,OP_READ,OP_GRANT])

private theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α→Except ε β} {out : β}
    (h:x >>= f=.ok out) : ∃v,x=.ok v ∧ f v=.ok out := by
  cases x with
  | error e=>cases h
  | ok v=>exact ⟨v,rfl,h⟩

theorem replay (I : Input) (cv : Array CReq) (rs : List Round) (out : ProcActualReplayRound.Acc)
    (h:ProcActualReplayFactor.replay I cv rs=.ok out) : Inv (ProcActualReplayRound.entryAcc out) := by
  unfold ProcActualReplayFactor.replay at h
  obtain ⟨ops,hop,h⟩:=bind_ok h
  rw [←Array.forIn_toList] at hop
  have ho:=reads _ _ cv.toList _ ops (empty _) hop
  apply rounds I cv _ rs _ out ?_ h
  exact ⟨ho,empty _,empty _⟩
end ZkFormal.NearV3.Candidates.ProcActualMemoryTagReplay
