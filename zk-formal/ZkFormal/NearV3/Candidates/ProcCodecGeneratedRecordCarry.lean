import ZkFormal.NearV3.Candidates.ProcCodecRecordCarry
import ZkFormal.NearV3.Candidates.ProcCodecPhysicalRecordGroups
namespace ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordCarry
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec

theorem active (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (r : Nat) (hr : r<out.rows.size) :
    ∀e∈(cRec.drop 35).take 6,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0 := by
  apply ProcCodecPhysicalRecordGroups.active_of_records I R present vid gb fwd out h _
    (fun e he=>List.mem_of_mem_drop (List.mem_of_mem_take he)) ?_ r hr
  intro k f g hk hf hg
  simpa only [ProcCodecRecordCarry.equations_eq] using
    ProcCodecRecordCarry.active I R present vid gb fwd out h k f g hk hf hg
end ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordCarry
