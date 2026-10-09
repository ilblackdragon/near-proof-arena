import ZkFormal.NearV3.Candidates.ProcessRepairRecordByteSource
import ZkFormal.NearV3.Candidates.ProcPriorRecordWordLayout
namespace ZkFormal.NearV3.Candidates.ProcessRepairRecordWordSources
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.V2
open ZkFormal.NearV3.Sched ProcPriorRecordTable
open ProcPriorRoutedRawSource (raw)

theorem bytes {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀msg,pubCount AP pub 75 true msg=0)
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 3)=1)
    (hf:cv (raw tr) 0 r firstLimb=1) :
    ∀j,j<8→∃q,q<tr.height 0 ∧ cv (raw tr) 0 q (ProcPriorVertical4Linear.stage 2)=1 ∧
      cv (raw tr) 0 q ProcPriorRawFrame.rec=1 ∧ cv (raw tr) 0 q ProcPriorRawFrame.act=1 ∧
      cv (raw tr) 0 q ProcPriorRawFrame.tau=cv (raw tr) 0 r tau ∧
      cv (raw tr) 0 q ProcPriorRawFrame.record=cv (raw tr) 0 r record ∧
      cv (raw tr) 0 q ProcPriorRawFrame.offset=ProcPriorRecordWordLayout.base (raw tr) 0 r+j ∧
      cv (raw tr) 0 q ProcPriorRawFrame.byte=cv (raw tr) 0 (r+j/3) (byte0+j%3) := by
  intro j hj
  have hv:=ProcessRepairRawBytes.overlay_local view
  have hj3:j/3<3:=by omega
  obtain ⟨hrj,hsj,hwj,hoff,htop⟩:=ProcPriorRecordWordLayout.layout hv hr hs hf (j/3) hj3
  have ht:j%3=2→cv (raw tr) 0 (r+j/3) topLimb=0:=by
    intro he;exact htop (by omega)
  obtain ⟨q,hq,hstage,hrec,hact,htau,hrecord,hoffset,hbyte⟩:=ProcessRepairRecordByteSource.source view hpub hrj
    (Nat.mod_lt _ (by decide)) hsj hwj ht
  have hid:=ProcPriorRecordWordIdentity.limb_identity hv hr hs hf (j/3) hj3
  refine ⟨q,hq,hstage,hrec,hact,htau.trans hid.1,hrecord.trans hid.2,?_,hbyte⟩
  rw [hoffset,hoff]
  omega
end ZkFormal.NearV3.Candidates.ProcessRepairRecordWordSources
