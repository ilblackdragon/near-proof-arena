import ZkFormal.NearV3.Candidates.ProcNativeMainCodecLocal
import ZkFormal.NearV3.Candidates.ProcCodecPresencePhysical
namespace ZkFormal.NearV3.Candidates.ProcNativeMainPresence
open NearSpec NearSpecV3 NearSpecV3.Scheduler
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Assembly

/-- Presence conservation on the same native read and corrected codec witness.
Raw parser local validity and its prior-allowance joins are separate obligations. -/
theorem native_main {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (ctx : ApplyCtx) (sp : SchedPub)
    (hsp : sp∈p.sched) (hpub : schedPub ctx=some sp)
    (t : PTrie) (receipts : List Receipt) (out : MainOut)
    (hchunk : applyNewChunk prims ctx t receipts=.ok out) (vid : Nat) :
    ∃old prev R gd result,
      readKey t keyBwState "bandwidth scheduler state"=.ok old ∧
      ProcActualCore.decodePrevious old=some prev ∧
      ActualRun.run (ProcPreparedSequence.input sp prev) 0=.ok R ∧
      ProcPriorCodecGen.codecRows (ProcPreparedSequence.input sp prev) R old.isSome vid gd
        (fwdLinks ctx out.outgoing)=.ok result ∧
      (∀(traceTime : Nat) (pub : List Fp),
        TableLocal ProcPriorCodecActual.table (SchedHeight.trace result.rows codecPad) traceTime pub) ∧
      ∀(traceTime : Nat) (pub msg : List Fp),
        tableBusCount ProcPriorCodecActual.table.interactions (SchedHeight.trace result.rows codecPad)
          traceTime pub B_SPOST true msg =
        tableBusCount (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
          (ProcPriorRawGen.trace prev vid old.isSome) traceTime pub B_SPOST false msg := by
  obtain ⟨old,prev,R,gd,result,hread,hprev,hr,hcodec,hlocal⟩ :=
    ProcNativeMainCodecLocal.native_main hp ctx sp hsp hpub t receipts out hchunk vid
  refine ⟨old,prev,R,gd,result,hread,hprev,hr,hcodec,hlocal,?_⟩
  intro traceTime pub msg
  exact ProcCodecPresencePhysical.main_balance _ R old.isSome vid gd _ result hcodec
    (ProcActualRunProjection.run_fields _ 0 R hr).1 prev traceTime pub msg
end ZkFormal.NearV3.Candidates.ProcNativeMainPresence
