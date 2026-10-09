import ZkFormal.NearV3.Candidates.ProcPriorCodecForwardPayloadNative
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordConstraints
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedBits
namespace ZkFormal.NearV3.Candidates.ProcCodecGeneratedForwardPayload
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec NearSpecV3.Scheduler

def equations : List Expr := (cRec.drop 60).take 3

theorem subset : ∀e∈equations,e∈cRec := by
  intro e he
  exact List.mem_of_mem_drop (List.mem_of_mem_take he)

/-- The native forwarding equations hold at every actual generated row,
including header and digest suffix rows. -/
theorem active (sp : SchedPub) (hs : SchedPubOk sp)
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
      R present vid gd fwd=.ok out) (r : Nat) (hrange : r<out.rows.size) :
    ∀e∈equations,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0 := by
  apply ProcCodecGeneratedRecordConstraints.generated (ProcPreparedSequence.input sp prev)
    R present vid gd fwd out hcodec equations subset
    (if r+1<out.rows.size then fun c=>Fp.ofNat out.rows[r+1]![c]! else fun _=>0)
    (if r=0 then 1 else 0) 0 1 ?_ out.rows[r]! (by simp [hrange])
  intro k f g hk hf hgg s result hstep
  have hn := (ProcActualRunProjection.run_fields (ProcPreparedSequence.input sp prev) tauV R hr).2.1
  have hk' : k<sp.ids.length*sp.ids.length := by
    simpa [hn,ProcPreparedSequence.input] using hk
  exact ProcPriorCodecForwardPayloadNative.native sp hs ha prev tauV cv rs st ev R gd sord rord
    hprefix hr hg k hk' present fwd vid f g s result hf hgg hstep _ _ _ _

/-- The same equations hold under the actual log22 physical trace evaluator.
The trace capacity follows from prepared shard bounds. -/
theorem physical (sp : SchedPub) (hs : SchedPubOk sp)
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
      R present vid gd fwd=.ok out) (t r : Nat) (hrange : r<out.rows.size) (pub : List Fp) :
    ∀e∈equations,e.eval (SchedHeight.trace out.rows codecPad) t r pub=0 := by
  have hn := (ProcActualRunProjection.run_fields (ProcPreparedSequence.input sp prev) tauV R hr).2.1
  have hn64 : R.n≤64 := by simpa [hn,ProcPreparedSequence.input] using hs.n64
  have hcap := (ProcCodecGeneratedBits.capacity (ProcPreparedSequence.input sp prev)
    R present vid gd fwd out hcodec hn64).2
  intro e he
  have hp : e.pubBound=0 := (by decide +kernel : ∀e∈equations,e.pubBound=0) e he
  rw [ProcCodecPhysicalRows.generated_eval out.rows hcap t r hrange pub e hp]
  exact active sp hs ha prev tauV cv rs st ev R gd sord rord hprefix hr hg
    present vid fwd out hcodec r hrange e he
end ZkFormal.NearV3.Candidates.ProcCodecGeneratedForwardPayload
