import ZkFormal.NearV3.Candidates.ProcessRepairFamilyWrite
import ZkFormal.NearV3.Candidates.ProcessRepairTrieViews
import ZkFormal.NearV3.Candidates.ProcPriorRoutedWriteStamp
namespace ZkFormal.NearV3.Candidates.ProcessRepairWriteStamp
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorMemoryTable ProcPriorVerticalLastWrite
open ProcPriorCodecFamilyLastWrite (memory)
open ProcPriorRoutedWriteStamp
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
theorem consumer_stamp {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀msg,pubCount AP pub 67 true msg=0)
    {t r:Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i:Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=67) (hs:i.send=false)
    (hm:i.multNat tr t r pub≠0) :
    (i.msgVal tr t r pub)[2]!.toNat+1<2^29 := by
  obtain ⟨q,hq,hstage,hgate,hmsg,_⟩:=ProcessRepairFamilyWrite.family_write_source view hpub ht hr hi hb hs hm
  have hh:tr.height 0≤2^22:=Nat.pow_le_pow_right (by decide) (ProcessRepairTrieViews.value_local view).log_le
  have hv:=ProcessRepairRawBytes.overlay_local view
  have ha:=(ProcPriorRecordGeometry.write_shape hv hq hstage hgate).1
  have hbound:=ProcPriorRecordOrdinal.ordinal_le_row hv q hq hstage ha
  have he:=congrArg (fun xs:List Fp=>xs[2]!.toNat) hmsg
  change cv (ProcPriorRoutedRawSource.raw tr) 0 q ProcPriorRecordTable.record=
    (i.msgVal tr t r pub)[2]!.toNat at he
  omega

/-- The write-stamp range required by the shared comparator is authenticated
for every live stage0 WRITE row of the actual installed family. -/
theorem write_stamp {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀msg,pubCount AP pub 67 true msg=0)
    {r:Nat} (hr:r<tr.height 0) (ha:Live (memory tr) 0 r)
    (hq:cv (memory tr) 0 r query=0) :cv (memory tr) 0 r stamp+1<2^29 := by
  have ht:0<AP.tables.length := by rw [view.length];decide +kernel
  have hi:write∈AP.tables[0]!.interactions := by rw [view.wires];exact write_member
  have hh:=consumer_stamp view hpub ht hr hi (show write.bus=67 from rfl)
    (show write.send=false from rfl) (write_live ha hq)
  rw [write_message] at hh
  exact hh
end ZkFormal.NearV3.Candidates.ProcessRepairWriteStamp
