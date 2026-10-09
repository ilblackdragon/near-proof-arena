import ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordAssembly
import ZkFormal.NearV3.Candidates.ProcCodecRecordAdditionResidual
namespace ZkFormal.NearV3.Candidates.ProcCodecNativeAdditionsResidual
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec NearSpecV3.Scheduler

theorem table_of_additions (sp : SchedPub) (hs : SchedPubOk sp)
    (ha : sp.allowed.size=sp.ids.length*sp.ids.length)
    (prev : NearSpec.Bandwidth.State) (tauV : Nat) (cv : Array CReq) (rs : List Round)
    (st : PState) (ev : Ev) (R : Run) (gd : Array Nat) (sord rord : List Nat)
    (hprefix : ProcActualPrefix.runPrefix (ProcPreparedSequence.input sp prev)=.ok (cv,st,rs,ev))
    (hr : ActualRun.run (ProcPreparedSequence.input sp prev) tauV=.ok R)
    (hg : distributeEv sp.ids.length sp.allowed st.sb st.rb
      (linkPass sp.ids.length sp.params sp.allowed (ProcActualInput.allowances sp.ids prev)).cntS
      (linkPass sp.ids.length sp.params sp.allowed (ProcActualInput.allowances sp.ids prev)).cntR
        =.ok (gd,sord,rord))
    (present : Bool) (vid : Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (hcodec : ProcPriorCodecGen.codecRows (ProcPreparedSequence.input sp prev)
      R present vid gd fwd=.ok out) (ht : R.tau<P) (t : Nat) (pub : List Fp)
    (hadd : ∀r,r<out.rows.size→∀e∈ProcPriorCodecActual.additions,
      e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0) :
    ZkFormal.Near.TableLocal ProcPriorCodecActual.table (SchedHeight.trace out.rows codecPad) t pub := by
  let I := ProcPreparedSequence.input sp prev
  have hn := (ProcActualRunProjection.run_fields I tauV R hr).2.1
  have hn1 : 0<R.n := by
    have hh : 1≤R.n := by simpa [hn,I,ProcPreparedSequence.input] using hs.n1
    omega
  have hn64 : R.n≤64 := by simpa [hn,I,ProcPreparedSequence.input] using hs.n64
  have hparam : Params.calculate Config.pv86 I.ids.length=some I.p := by
    simpa [I,ProcPreparedSequence.input] using hs.params
  apply ProcCodecRecordAdditionResidual.table_of_remaining I R present vid gd fwd out hcodec hparam hn1 hn64 ht t pub
  intro r hrange e he
  rcases List.mem_append.mp he with he|he
  · exact ProcCodecGeneratedRecordAssembly.active sp hs ha prev tauV cv rs st ev R gd sord rord hprefix hr hg present vid fwd out hcodec r hrange e he
  · exact hadd r hrange e he
end ZkFormal.NearV3.Candidates.ProcCodecNativeAdditionsResidual
