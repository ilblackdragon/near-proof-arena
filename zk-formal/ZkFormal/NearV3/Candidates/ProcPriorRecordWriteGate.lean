import ZkFormal.NearV3.Candidates.ProcPriorRecordOrdinal
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordWriteGate
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRecordTable

theorem enabled {tr:Trace Fp} {t r:Nat} {pub:List Fp}
    (hL:ProcPriorVerticalMemorySound.LocalV tr t pub) (hr:r<tr.height t)
    (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (ha:cv tr t r amount=1) (ht:cv tr t r topLimb=1)
    (hf:cv tr t r senderFound=1) (hg:cv tr t r receiverFound=1):cv tr t r writeGate=1:=by
  obtain ⟨q,hq⟩:=ProcPriorRecordOrdinal.zdvd hL hr hs
    (sub (c writeGate) (.mul (.mul (.mul (c amount) (c topLimb)) (c senderFound)) (c receiverFound)))
    (by simp [constraints])
  change zev (tenv tr t r pub) (sub (c writeGate) (.mul (.mul (.mul (c amount) (c topLimb)) (c senderFound)) (c receiverFound)))=2013265921*q at hq
  zs hq [ha,ht,hf,hg]
  have hb:=ProcPriorRecordSound.flag hL hr hs writeGate (by simp)
  omega
end ZkFormal.NearV3.Candidates.ProcPriorRecordWriteGate
