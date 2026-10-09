import ZkFormal.NearV3.Candidates.ProcPriorCodecNativeTotal
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecForwardBound
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

def Demands (R : Run) (gb : Array Nat) (fwd : List (Nat×Nat)) : Prop :=
  ∀d∈fwd,d.2≤(R.segs.getD d.1 default).wfin+gb[d.1]!

theorem lookup_bound (R : Run) (gb : Array Nat) (fwd : List (Nat×Nat))
    (h : Demands R gb fwd) (k : Nat) : ProcPriorCodecRecordTotal.Forward R gb fwd k := by
  induction fwd with
  | nil => simp [ProcPriorCodecRecordTotal.Forward]
  | cons d ds ih =>
    have hd := h d (by simp)
    have hs := ih (fun e he=>h e (by simp [he]))
    by_cases hk : d.1=k
    · subst k
      simpa [ProcPriorCodecRecordTotal.Forward,List.find?_cons] using hd
    · simpa [ProcPriorCodecRecordTotal.Forward,List.find?_cons,hk] using hs

open NearSpec NearSpecV3 in
/-- Each concrete forwarding demand is checked at the same sender-major link
index used by the native scheduler; unknown layout IDs produce no demand. -/
theorem native_links (ctx : ApplyCtx) (refunds : List Receipt) (R : Run) (gb : Array Nat)
    (h : ∀o,Scheduler.indexOf ctx.layout.shardIds ctx.own=some o →
      ∀d∈fwdSizes ctx refunds,∀r,Scheduler.indexOf ctx.layout.shardIds d.1=some r →
        d.2≤(R.segs.getD (o*ctx.layout.shardIds.length+r) default).wfin+
          gb[o*ctx.layout.shardIds.length+r]!) :
    Demands R gb (fwdLinks ctx refunds) := by
  unfold fwdLinks
  dsimp only
  split
  · simp [Demands]
  · rename_i o ho
    intro d hd
    obtain ⟨e,he,hm⟩ := List.mem_filterMap.mp hd
    cases hi : Scheduler.indexOf ctx.layout.shardIds e.1 with
    | none => simp [hi] at hm
    | some r =>
      simp only [hi,Option.map_some,Option.some.injEq] at hm
      subst d
      exact h o ho e he r hi

open NearSpecV3.Scheduler in
theorem decoded_codec (sp : SchedPub) (hs : SchedPubOk sp)
    (old : Option NearSpec.Bytes) (prev : NearSpec.Bandwidth.State)
    (hd : ProcActualCore.decodePrevious old=some prev) (tau : Nat) (R : Run)
    (hr : ActualRun.run (ProcPreparedSequence.input sp prev) tau=.ok R)
    (vid : Nat) (gb : Array Nat) (fwd : List (Nat×Nat))
    (hf : R.tau=0 → Demands R gb fwd) :
    ∃out,ProcPriorCodecGen.codecRows (ProcPreparedSequence.input sp prev) R old.isSome vid gb fwd=.ok out :=
  ProcPriorCodecNativeTotal.decoded_codec_success sp hs old prev hd tau R hr vid gb fwd
    (fun k _ hz=>lookup_bound R gb fwd (hf hz) k)
end ZkFormal.NearV3.Candidates.ProcPriorCodecForwardBound
