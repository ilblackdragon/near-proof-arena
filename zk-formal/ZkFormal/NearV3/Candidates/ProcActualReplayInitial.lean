import ZkFormal.NearV3.Candidates.ProcActualPreparedReplay
namespace ZkFormal.NearV3.Candidates.ProcActualReplayInitial
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open NearSpecV3.Scheduler
open ProcActualReplayRound ProcActualRoundTransition

/-- The round-loop accumulator after conversion reads; those reads only change opsL. -/
def initial (I : Input) (cv : Array CReq) (opsL : Array (Array Gen.MOp)) : Acc :=
  let lp := linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev)
  (lp.sb,lp.rb,lp.a2,lp.g2,opsL,Array.replicate I.ids.length #[],
    Array.replicate I.ids.length #[],
    cv.map (fun c => (c.cid,c.key,if c.key=0 then 1 else 0,c.cid*64)),
    #[],T0,0,Proc.KSENT,0,cv.map (fun c => Array.replicate c.incs.length false),#[],0)

theorem initial_aligned (I : Input) (cv : Array CReq) (opsL : Array (Array Gen.MOp)) :
    Aligned (NearSpecV3.leWords I.seed) cv (initial I cv opsL)
      (ProcActualInput.initial I) cv.size := by
  simp [Aligned,initial,ProcActualReplayRound.entryAcc,ProcActualReplayRound.position,
    ProcActualReplayEntry.state,ProcActualEntryTransition.cursor,ProcActualInput.initial,
    ZkFormal.Chacha.ofSeed_eq]

theorem initialized_replay (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (cv : Array CReq) (st : PState) (rs : List Round)
    (hcv : forIn (ProcPreparedSequence.input sp prev).raw #[]
      (ProcActualConverted.step (ProcPreparedSequence.input sp prev))=.ok cv)
    (hproc : ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs))
    (opsL : Array (Array Gen.MOp)) :
    ∃out last,forIn rs (initial (ProcPreparedSequence.input sp prev) cv opsL)
      (step (ProcPreparedSequence.input sp prev) cv (NearSpecV3.leWords sp.seed))=.ok out ∧
      Aligned (NearSpecV3.leWords sp.seed) cv out st last := by
  exact ProcActualPreparedReplay.prepared_replay sp hs prev cv st rs hcv hproc _
    (initial_aligned (ProcPreparedSequence.input sp prev) cv opsL)
end ZkFormal.NearV3.Candidates.ProcActualReplayInitial
