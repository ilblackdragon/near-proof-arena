import ZkFormal.NearV3.Candidates.ProcActualReplayFactor
namespace ZkFormal.NearV3.Candidates.ProcActualReplayTotal
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler
open ProcActualReplayRound ProcActualRoundTransition ProcActualReplayFactor

theorem reads_list (aa gg : Array Nat) (cs : List CReq) (ops : Array (Array Gen.MOp)) :
    ∃out,forIn cs ops (readStep aa gg)=.ok out := by
  induction cs generalizing ops with
  | nil => exact ⟨ops,rfl⟩
  | cons c cs ih =>
    simpa only [List.forIn_cons,readStep,bind,Except.bind] using
      ih (ops.modify c.link (·.push
        ⟨c.cid+1,OP_READ,aa[c.link]!,aa[c.link]!,gg[c.link]!,gg[c.link]!,0,false,false,false⟩))

theorem reads_array (aa gg : Array Nat) (cv : Array CReq) (ops : Array (Array Gen.MOp)) :
    ∃out,forIn cv ops (readStep aa gg)=.ok out := by
  simpa only [Array.forIn_toList] using reads_list aa gg cv.toList ops

theorem prepared_replay (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (cv : Array CReq) (st : PState) (rs : List Round)
    (hcv : forIn (ProcPreparedSequence.input sp prev).raw #[]
      (ProcActualConverted.step (ProcPreparedSequence.input sp prev))=.ok cv)
    (hproc : ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs)) :
    ∃out last,replay (ProcPreparedSequence.input sp prev) cv rs=.ok out ∧
      Aligned (NearSpecV3.leWords sp.seed) cv out st last ∧
      ProcActualFinalStateGuards.checks out st=.ok () := by
  let I := ProcPreparedSequence.input sp prev
  let lp := linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev)
  obtain ⟨ops,hop⟩ := reads_array lp.a2 lp.g2 cv (Array.replicate (I.ids.length*I.ids.length) #[])
  obtain ⟨out,last,hr,ha,hcheck⟩ := ProcActualFinalStateGuards.initialized_checks sp hs prev cv st rs hcv hproc ops
  refine ⟨out,last,?_,ha,hcheck⟩
  change (forIn cv _ (readStep lp.a2 lp.g2) >>= fun ops =>
    forIn rs (ProcActualReplayInitial.initial I cv ops) (step I cv (NearSpecV3.leWords sp.seed)))=.ok out
  rw [hop]
  exact hr

theorem prepared_reduction (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (tau : Nat) (cv : Array CReq) (st : PState) (rs : List Round)
    (hcv : forIn (ProcPreparedSequence.input sp prev).raw #[]
      (ProcActualConverted.step (ProcPreparedSequence.input sp prev))=.ok cv)
    (hproc : ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs)) :
    ∃out,ProcActualRoundFactor.runRestRounds (ProcPreparedSequence.input sp prev) tau cv st rs=
      finish (ProcPreparedSequence.input sp prev) tau cv st out ∧
      ProcActualFinalStateGuards.checks out st=.ok () := by
  obtain ⟨out,last,hr,ha,hcheck⟩ := prepared_replay sp hs prev cv st rs hcv hproc
  refine ⟨out,?_,hcheck⟩
  rw [rest_eq,hr]
  rfl
end ZkFormal.NearV3.Candidates.ProcActualReplayTotal
