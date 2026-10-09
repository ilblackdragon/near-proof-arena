import ZkFormal.NearV3.Candidates.ProcPriorRoutedRecordIndices
import ZkFormal.NearV3.Candidates.ProcPriorRecordEndpoint
import ZkFormal.NearV3.Candidates.ProcPriorRoutedIdBound
import ZkFormal.NearV3.Candidates.ProcessRepairIdBound
namespace ZkFormal.NearV3.Candidates.ProcessRepairRecordIndices
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRecordTable ProcPriorRoutedRecordIndices
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
theorem endpoint64 {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (ha:ProcPriorIdSoundBound.PublicSendBound AP tr pub 64)
    (h70:∀msg,pubCount AP pub 70 true msg=0) (h72:∀msg,pubCount AP pub 72 true msg=0)
    (b:Bool) {r:Nat} (hr:r<tr.height 0)
    (hs:cv (recordTrace tr) 0 r (ProcPriorVertical4Linear.stage 3)=1)
    (hc:cv (recordTrace tr) 0 r (col b)=1) (ht:cv (recordTrace tr) 0 r topLimb=1)
    (hf:cv (recordTrace tr) 0 r (found b)=1) :cv (recordTrace tr) 0 r (index b)<64 := by
  have ht0:0<AP.tables.length := by rw [view.length];decide +kernel
  have hi:endpoint b∈AP.tables[0]!.interactions := by rw [view.wires];exact member b
  have hfound:((endpoint b).msgVal tr 0 r pub)[2]! =Fp.ofNat 1 := by
    rw [message]
    have hcell:(recordTrace tr).cell 0 r (found b)=Fp.ofNat 1 := by rw [←hf];exact (Fp.ofNat_toNat _).symm
    cases b <;> exact hcell
  have hb:=ProcessRepairIdBound.result_bound view 64 h70 ha h72 ht0 hr hi
    (show (endpoint b).bus=72 by cases b <;> rfl) (show (endpoint b).send=false by cases b <;> rfl)
    (live b hs hc ht) hfound
  rw [message] at hb
  cases b <;> exact hb

theorem write_indices {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (ha:ProcPriorIdSoundBound.PublicSendBound AP tr pub 64)
    (h70:∀msg,pubCount AP pub 70 true msg=0) (h72:∀msg,pubCount AP pub 72 true msg=0)
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (recordTrace tr) 0 r (ProcPriorVertical4Linear.stage 3)=1)
    (hw:cv (recordTrace tr) 0 r writeGate=1) :
    cv (recordTrace tr) 0 r senderIndex<64 ∧ cv (recordTrace tr) 0 r receiverIndex<64 := by
  have ht0:0<AP.tables.length := by rw [view.length];decide +kernel
  have hv:=ProcessRepairRawBytes.overlay_local view
  obtain ⟨hac,hsen,hrecv,hamt,hfirst,hmid,htop,hsf,hrf⟩:=ProcPriorRecordGeometry.write_shape hv hr hs hw
  obtain ⟨s,hsr,hss,hsc,hst,hsfound,hsindex⟩:=ProcPriorRecordEndpoint.sender_origin hv r hr hs hac (by omega) hsen
  obtain ⟨v,hvr,hvs,hvc,hvt,hvfound,hvindex⟩:=ProcPriorRecordEndpoint.receiver_origin hv r hr hs hac hamt
  have hsbound:=endpoint64 view ha h70 h72 true (show s<tr.height 0 by omega) hss hsc hst (hsfound.trans hsf)
  have hvbound:=endpoint64 view ha h70 h72 false (show v<tr.height 0 by omega) hvs hvc hvt (hvfound.trans hrf)
  change cv (recordTrace tr) 0 s senderIndex=cv (recordTrace tr) 0 r senderIndex at hsindex
  change cv (recordTrace tr) 0 v receiverIndex=cv (recordTrace tr) 0 r receiverIndex at hvindex
  change cv (recordTrace tr) 0 s senderIndex<64 at hsbound
  change cv (recordTrace tr) 0 v receiverIndex<64 at hvbound
  omega
end ZkFormal.NearV3.Candidates.ProcessRepairRecordIndices
