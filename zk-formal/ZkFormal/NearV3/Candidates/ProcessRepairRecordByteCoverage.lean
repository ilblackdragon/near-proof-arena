import ZkFormal.NearV3.Candidates.ProcessRepairRecordByteReceiver
import ZkFormal.NearV3.Candidates.ProcPriorRecordByteActivity
namespace ZkFormal.NearV3.Candidates.ProcessRepairRecordByteCoverage
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.V2
open ZkFormal.NearV3.Sched ProcPriorRecordTable ProcPriorRecordPhysicalBytes
open ProcPriorRoutedRawSource (raw)

theorem matched {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠75)
    {t r:Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i:Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=75) (hs:i.send=true)
    (hm:i.multNat tr t r pub≠0):
    ∃q j,q<tr.height 0 ∧ j<3 ∧ cv (raw tr) 0 q (ProcPriorVertical4Linear.stage 3)=1 ∧
      cv (raw tr) 0 q sender+cv (raw tr) 0 q receiver+cv (raw tr) 0 q amount=1 ∧
      (j=2→cv (raw tr) 0 q topLimb=0) ∧
      ProcPriorRecordByteMessage.offsetNat (raw tr) 0 q+j<24 ∧
      [Fp.ofNat (cv (raw tr) 0 q tau),Fp.ofNat (cv (raw tr) 0 q record),
       Fp.ofNat (ProcPriorRecordByteMessage.offsetNat (raw tr) 0 q+j),
       Fp.ofNat (cv (raw tr) 0 q (byte0+j))]=i.msgVal tr t r pub := by
  obtain ⟨q,j,hq,hj,hjm,hmsg⟩:=ProcessRepairRecordByteReceiver.matched view hpub ht hr hi hb hs hm
  rw [mult] at hjm
  have hL:=ProcessRepairRawBytes.overlay_local view
  obtain ⟨hst,hw,htop⟩:=ProcPriorRecordByteActivity.flags hL hq hj hjm
  rw [message,ProcPriorRecordByteMessage.message _ _ _ _ _ hj] at hmsg
  exact ⟨q,j,hq,hj,hst,hw,htop,ProcPriorRecordByteMessage.offset_bound hL hq hst j hj htop,hmsg⟩
end ZkFormal.NearV3.Candidates.ProcessRepairRecordByteCoverage
