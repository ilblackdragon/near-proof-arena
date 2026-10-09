import ZkFormal.NearV3.Candidates.ProcNativeMainCodecWitness
import ZkFormal.NearV3.Candidates.ProcCodecNativeLocal
namespace ZkFormal.NearV3.Candidates.ProcNativeMainCodecLocal
open NearSpec NearSpecV3 NearSpecV3.Scheduler
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Assembly

/-- An accepted native main chunk constructs corrected Codec rows satisfying
all local constraints at every physical row. Native execution supplies the
same prefix, replay, distribution and forwarding witnesses used in the proof. -/
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
      ∀(traceTime : Nat) (pub : List Fp),
        ZkFormal.Near.TableLocal ProcPriorCodecActual.table
          (SchedHeight.trace result.rows codecPad) traceTime pub := by
  obtain ⟨old,prev,cv,st,rs,ev,R,gd,sord,rord,result,hread,hprev,hprefix,hr,hgd,hcodec⟩ :=
    ProcNativeMainCodecWitness.native_main hp ctx sp hsp hpub t receipts out hchunk vid
  have hs := prepD0_sched hp sp hsp
  have ha := (ProcActualPublic.schedPub_fields ctx sp hpub).1
  have ht : R.tau<ZkFormal.Algebra.P := by
    rw [(ProcActualRunProjection.run_fields (ProcPreparedSequence.input sp prev) 0 R hr).1]
    decide +kernel
  refine ⟨old,prev,R,gd,result,hread,hprev,hr,hcodec,?_⟩
  intro traceTime pub
  exact ProcCodecNativeLocal.table sp hs ha prev 0 cv rs st ev R gd sord rord hprefix hr hgd
    old.isSome vid (fwdLinks ctx out.outgoing) result hcodec ht traceTime pub
end ZkFormal.NearV3.Candidates.ProcNativeMainCodecLocal
