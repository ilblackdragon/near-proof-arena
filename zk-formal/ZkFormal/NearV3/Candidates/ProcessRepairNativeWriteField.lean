import ZkFormal.NearV3.Candidates.ProcessRepairNativeWord
import ZkFormal.NearV3.Candidates.ProcPriorRecordBackwardBoundary
namespace ZkFormal.NearV3.Candidates.ProcessRepairNativeWriteField
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRecordTable
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}
set_option maxRecDepth 32768

theorem selected_allowance (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (hf:cv tr t r firstLimb=1) (ha:cv tr t (r+2) amount=1)
    (link:NearSpec.Bandwidth.LinkAllowance) :
    ProcPriorRecordNativeField.selected tr t r link=link.allowance := by
  obtain ⟨hr1,hs1,_,hm1,hf1⟩:=ProcPriorRecordWordTraversal.limb_next hL hr hs firstLimb midLimb (by simp) hf
  obtain ⟨_,_,_,_,hf2⟩:=ProcPriorRecordWordTraversal.limb_next hL hr1 hs1 midLimb topLimb (by simp) hm1
  have h1:=hf1 amount (by simp)
  have h2:=hf2 amount (by simp)
  simp only [Nat.add_assoc,Nat.reduceAdd] at h2
  have hb:=ProcPriorRecordGeometry.words_bound hL hr hs
  have hab:=ProcPriorRecordSound.flag hL hr hs act (by simp)
  have ham:cv tr t r amount=1:=by omega
  have hsend:cv tr t r sender=0:=by omega
  have hrecv:cv tr t r receiver=0:=by omega
  simp [ProcPriorRecordNativeField.selected,hsend,hrecv]
end ZkFormal.NearV3.Candidates.ProcessRepairNativeWriteField
