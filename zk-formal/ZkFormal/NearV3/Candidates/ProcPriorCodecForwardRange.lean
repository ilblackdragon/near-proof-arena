import ZkFormal.NearV3.Candidates.ProcPriorCodecGrantCap
import ZkFormal.NearV3.Candidates.ProcPriorCodecForwardSuccess
import ZkFormal.NearV3.Candidates.ProcActualRunProjection
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecForwardRange
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler
open ProcPriorCodecRecordStep

/-- Actual native execution and the same distribution witness discharge the
three-byte forwarding range required by Codec serialization. -/
theorem native (sp : SchedPub) (hs : SchedPubOk sp)
    (ha : sp.allowed.size=sp.ids.length*sp.ids.length)
    (prev : NearSpec.Bandwidth.State) (cv : Array CReq) (rs : List Round)
    (st : PState) (ev : Ev) (R : Run) (gd : Array Nat) (sord rord : List Nat)
    (hprefix : ProcActualPrefix.runPrefix (ProcPreparedSequence.input sp prev)=.ok (cv,st,rs,ev))
    (hr : ActualRun.run (ProcPreparedSequence.input sp prev) 0=.ok R)
    (hg : distributeEv sp.ids.length sp.allowed st.sb st.rb
      (linkPass sp.ids.length sp.params sp.allowed (ProcActualInput.allowances sp.ids prev)).cntS
      (linkPass sp.ids.length sp.params sp.allowed (ProcActualInput.allowances sp.ids prev)).cntR
        =.ok (gd,sord,rord))
    (k : Nat) (hk : k<sp.ids.length*sp.ids.length)
    (present : Bool) (fwd inst : List (Nat×Nat)) (s out : State)
    (hstep : step (ProcPreparedSequence.input sp prev) R present gd fwd inst k 2 7 s=.ok (.yield out)) :
    ((fwd.find? (·.1==k)).map Prod.snd).getD 0<16777216 := by
  have ht : R.tau=0 := (ProcActualRunProjection.run_fields _ 0 R hr).1
  have hb := ProcPriorCodecForwardSuccess.bound (ProcPreparedSequence.input sp prev) R present gd fwd inst k s out ht hstep
  have hc := ProcPriorCodecGrantCap.native sp hs ha prev 0 cv rs st ev R gd sord rord hprefix hr hg k hk
  unfold ProcPriorCodecRecordTotal.Forward at hb
  change ((fwd.find? (·.1==k)).map (fun x=>x.2)).getD 0<16777216
  omega
end ZkFormal.NearV3.Candidates.ProcPriorCodecForwardRange
