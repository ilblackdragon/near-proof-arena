import ZkFormal.NearV3.Candidates.ProcPriorRecordByteMessage
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordLastByte
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRecordTable

theorem shape {tr:Trace Fp} {t r j:Nat} {pub:List Fp}
    (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (hw:cv tr t r sender+cv tr t r receiver+cv tr t r amount=1)
    (hj:j<3) (ht:j=2→cv tr t r topLimb=0)
    (ho:ProcPriorRecordByteMessage.offsetNat tr t r+j=23):
    cv tr t r amount=1 ∧ cv tr t r topLimb=1 ∧ j=1 := by
  have hl:=ProcPriorRecordGeometry.limbs_eq hL hr hs
  unfold ProcPriorRecordByteMessage.offsetNat at ho
  by_cases ht2:j=2
  · have hz:=ht ht2
    omega
  · omega
end ZkFormal.NearV3.Candidates.ProcPriorRecordLastByte
