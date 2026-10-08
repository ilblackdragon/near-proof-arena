import ZkFormal.NearV3.Candidates.ProcActualOutputAgreement
import ZkFormal.NearV3.Candidates.ProcActualReplayBoundaryGuards
namespace ZkFormal.NearV3.Candidates.ProcActualPrefix
open NearSpec NearSpecV3 NearSpecV3.Scheduler ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

/-- Exact operations of ActualRun.run through the seed-length check. The later
replay, memory sorting and comparison checks are not included here. -/
def runPrefix (I : Input) : Except String (Array CReq × PState × List Round × Ev) := do
  let n := I.ids.length
  let p := I.p
  let lp := linkPass n p I.allowed (ProcActualInput.allowances I.ids I.prev)
  -- converted requests
  let mut conv : Array CReq := #[]
  for q in I.raw do
    let bits := setBits q.bm
    if bits.isEmpty then continue
    Gen.check (q.bm.length == 5) "bitmap length ≠ 5"
    Gen.check (q.s < n && q.r < n) "shard index"
    let link := q.s * n + q.r
    conv := conv.push ⟨conv.size, q.s, q.r, link, q.bm, bits, incsOf p q.bm, lp.a2[link]!⟩
  let reqs := convRaw p n I.raw
  Gen.check (reqs == conv.toList.map fun c => ⟨c.link, c.incs⟩) "convRaw differs"
  let R := conv.size
  Gen.check (R < 65536) "too many requests"
  let st0 : PState := ⟨lp.sb, lp.rb, lp.a2, lp.g2, Rng.ofSeed I.seed⟩
  let fuel := 1 + (reqs.map (·.incs.length)).sum
  let (stF, mrounds) ← processEv n I.allowed reqs st0 fuel
  -- the end-to-end model
  let ev ← ActualRun.coreEv I.ids p I.allowed I.raw I.seed I.ash I.prev
  Gen.check (ev.rounds.length == mrounds.length) "coreEv rounds differ"
  for (a, b) in ev.rounds.zip mrounds do
    Gen.check (a.key == b.key && a.z == b.z && a.shuffled == b.shuffled &&
      a.steps.map (fun s => (s.t, s.v, s.ok, s.aOut)) == b.steps.map (fun s => (s.t, s.v, s.ok, s.aOut)))
      "coreEv round differs"
  let key := leWords I.seed
  Gen.check (key.length == 8) "seed length"
  return (conv,stF,mrounds,ev)

/-- Prepared conversion and successful native execution discharge every check
before the replay stage, preserving native output agreement. -/
theorem prepared_prefix {cb : Bytes} {hint : Hint} {p : Prep} (hp : prepD0 cb hint=.ok p)
    (sp : SchedPub) (hsp : sp∈p.sched) (ctx : ApplyCtx) (hpub : schedPub ctx=some sp)
    (oldBytes : Option Bytes) (out : Output) (hcore : runCore sp oldBytes=some out) :
    ∃prev cv st rs ev,ProcActualCore.decodePrevious oldBytes=some prev ∧
      runPrefix (ProcPreparedSequence.input sp prev)=.ok (cv,st,rs,ev) ∧
      ev.state=out.state ∧ ev.granted=out.granted.map Prod.snd := by
  have hs := prepD0_sched hp sp hsp
  obtain ⟨prev,st,rs,hprev,hproc,hout⟩ :=
    ProcActualNativeResult.scheduled_process_output ctx sp hs hpub oldBytes out hcore
  let I := ProcPreparedSequence.input sp prev
  obtain ⟨cv,hcv,hexact,hcheck,hcount,hbound⟩ := ProcActualPreparedConversion.prepared_conversion hp sp hsp prev
  obtain ⟨ev,hev⟩ := ProcActualCoreTotal.core_exists I st rs hproc
  have hround := ProcActualCoreReplay.checked_core_rounds I st rs ev hproc hev
  have hseed := ProcActualReplayBoundaryGuards.prepared_seed_guard hp sp hsp
  refine ⟨prev,cv,st,rs,ev,hprev,?_,?_,?_⟩
  · unfold runPrefix
    change (do
      let conv ← forIn I.raw #[] (ProcActualConverted.step I)
      Gen.check (convRaw I.p I.ids.length I.raw==ProcActualConversionExact.view conv) "convRaw differs"
      Gen.check (conv.size<65536) "too many requests"
      let (stF,mrounds) ← ProcActualInput.process I
      let ev ← ActualRun.coreEv I.ids I.p I.allowed I.raw I.seed I.ash I.prev
      Gen.check (ev.rounds.length==mrounds.length) "coreEv rounds differ"
      forIn (ev.rounds.zip mrounds) () (fun (ab : Round × Round) (_ : Unit) => ProcActualCoreReplay.roundCheck ab.1 ab.2)
      Gen.check ((leWords I.seed).length==8) "seed length"
      pure (conv,stF,mrounds,ev))=.ok _
    change Gen.check ((leWords I.seed).length==8) "seed length"=.ok () at hseed
    dsimp only [I] at hev hseed ⊢
    simp only [hcv,hcheck,hcount,hproc,hev,hround.1,hround.2,hseed,bind,Except.bind,pure,Except.pure]
  · exact ProcActualStateAgreement.scheduled_state ctx sp hs hpub oldBytes out hcore prev hprev ev hev
  · rw [ProcActualOutputAgreement.core_granted sp hs (ProcActualPublic.schedPub_fields ctx sp hpub).1 prev st rs ev hproc hev,hout]
end ZkFormal.NearV3.Candidates.ProcActualPrefix
