import ZkFormal.NearV3.Candidates.ProcPriorCodecForwardPayloadLocal
import ZkFormal.NearV3.Candidates.ProcPriorCodecForwardRange
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecForwardPayloadNative
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec NearSpecV3.Scheduler
open ProcPriorCodecRecordStep ProcPriorCodecNativeHash

/-- All forwarding payload equations on actual record rows of the same
native scheduler/distribution witness. The three-byte range is derived. -/
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
    (k : Nat) (hk : k<sp.ids.length*sp.ids.length)
    (present : Bool) (fwd : List (Nat×Nat)) (vidV f gg : Nat) (s out : State)
    (hf : f<3) (hgg : gg<8)
    (hstep : step (ProcPreparedSequence.input sp prev) R present gd fwd
      (instanceCells (ProcPreparedSequence.input sp prev) R present vidV) k f gg s=.ok (.yield out))
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∃a,out.1=s.1.push a ∧ ∀e∈(cRec.drop 60).take 3,e.evalWith
      (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0 := by
  have hfields := ProcActualRunProjection.run_fields (ProcPreparedSequence.input sp prev) tauV R hr
  have hkR : k<R.n*R.n := by simpa [hfields.2.1,ProcPreparedSequence.input] using hk
  apply ProcPriorCodecForwardPayloadLocal.actual (ProcPreparedSequence.input sp prev) R present gd fwd
    vidV k f gg s out hkR hf hgg hstep _ nxt first last trans
  intro hf2 hgg7 ht
  subst f gg
  have htV : tauV=0 := hfields.1.symm.trans ht
  subst tauV
  exact ProcPriorCodecForwardRange.native sp hs ha prev cv rs st ev R gd sord rord
    hprefix hr hg k hk present fwd (instanceCells (ProcPreparedSequence.input sp prev) R present vidV) s out hstep
end ZkFormal.NearV3.Candidates.ProcPriorCodecForwardPayloadNative
