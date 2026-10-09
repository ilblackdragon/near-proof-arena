import ZkFormal.NearV3.Candidates.ProcNativeMainCodecWitness
import ZkFormal.NearV3.Candidates.ProcNativeNonmainCodecLocal
import ZkFormal.NearV3.Candidates.ProcCodecNativeLocal
import ZkFormal.NearV3.Candidates.ProcCodecComparisonValidNative
namespace ZkFormal.NearV3.Candidates.ProcNativeCodecComparisonWitness
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
      (∀q∈result.cmps, Sched.Complete.CmpOk q) ∧
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
  refine ⟨old,prev,R,gd,result,hread,hprev,hr,hcodec,?_,?_⟩
  · exact ProcCodecComparisonValidNative.native sp hs ha prev 0 cv rs st ev R gd sord rord hprefix hr hgd old.isSome vid (fwdLinks ctx out.outgoing) result hcodec
  intro traceTime pub
  exact ProcCodecNativeLocal.table sp hs ha prev 0 cv rs st ev R gd sord rord hprefix hr hgd
    old.isSome vid (fwdLinks ctx out.outgoing) result hcodec ht traceTime pub
theorem missing_chunk {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (sp : SchedPub) (tau : Nat)
    (hindex : p.sched[tau]?=some sp) (ht : tau≠0)
    (ctx : ApplyCtx) (hpub : schedPub ctx=some sp)
    (pre post : PTrie) (hchunk : applyMissingChunk prims ctx pre=.ok post) (vid : Nat) :
    ∃old prev R gd result,
      readKey pre keyBwState "bandwidth scheduler state"=.ok old ∧
      ProcActualCore.decodePrevious old=some prev ∧
      ActualRun.run (ProcPreparedSequence.input sp prev) tau=.ok R ∧
      ProcPriorCodecGen.codecRows (ProcPreparedSequence.input sp prev) R old.isSome vid gd []=.ok result ∧
      (∀q∈result.cmps, Sched.Complete.CmpOk q) ∧
      ∀(traceTime : Nat) (pub : List Fp),
        ZkFormal.Near.TableLocal ProcPriorCodecActual.table
          (SchedHeight.trace result.rows codecPad) traceTime pub := by
  unfold applyMissingChunk at hchunk
  obtain ⟨_,_,hchunk⟩ := ReexecV3D0.bind_ok' hchunk
  obtain ⟨⟨mid,so⟩,hstep,_⟩ := ReexecV3D0.bind_ok' hchunk
  obtain ⟨old,sp',nativeOut,hread,hpub',hcore,_,_⟩ := schedStep_complete hstep
  have he := Option.some.inj (hpub'.symm.trans hpub)
  subst sp'
  obtain ⟨prev,cv,st,rs,ev,R,gd,sord,rord,result,hprev,hprefix,hr,hgd,hcodec,hlocal⟩ :=
    ProcNativeNonmainCodecLocal.native_nonmain hp sp tau hindex ht ctx hpub old nativeOut hcore vid []
  have hs := prepD0_sched hp sp (List.mem_iff_getElem?.mpr ⟨tau,hindex⟩)
  have ha := (ProcActualPublic.schedPub_fields ctx sp hpub).1
  exact ⟨old,prev,R,gd,result,hread,hprev,hr,hcodec,
    ProcCodecComparisonValidNative.native sp hs ha prev tau cv rs st ev R gd sord rord
      hprefix hr hgd old.isSome vid [] result hcodec,hlocal⟩
end ZkFormal.NearV3.Candidates.ProcNativeCodecComparisonWitness
