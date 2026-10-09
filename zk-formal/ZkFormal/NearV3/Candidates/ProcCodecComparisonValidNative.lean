import ZkFormal.NearV3.Candidates.ProcCodecComparisonValidTotal
import ZkFormal.NearV3.Candidates.ProcPriorCodecGrantCap
namespace ZkFormal.NearV3.Candidates.ProcCodecComparisonValidNative
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler
open ZkFormal.NearV3.Assembly.CodecDigest
open ZkFormal.NearV3.Sched.Complete
theorem native (sp : SchedPub) (hs : SchedPubOk sp)
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
    (hgen:ProcPriorCodecGen.codecRows (ProcPreparedSequence.input sp prev) R present vid gd fwd=.ok out) :
    ∀q∈out.cmps,CmpOk q := by
  apply ProcCodecComparisonValidTotal.generated _ R present vid gd fwd out ?_ ?_ hgen
  · change sp.params.maxShardBandwidth≤4500000
    rw [pv86_maxShard hs.params]; exact Nat.le_refl _
  · intro k hk
    have hn := (ProcActualRunProjection.run_fields (ProcPreparedSequence.input sp prev) tauV R hr).2.1
    have hk' : k<sp.ids.length*sp.ids.length := by simpa only [hn, ProcPreparedSequence.input] using hk
    exact ProcPriorCodecGrantCap.native sp hs ha prev tauV cv rs st ev R gd sord rord hprefix hr hg k hk'
end ZkFormal.NearV3.Candidates.ProcCodecComparisonValidNative
