import ZkFormal.NearV3.Candidates.ProcPriorCodecAssignments
import ZkFormal.NearV3.Candidates.SchedSetAllRange
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecAssignmentReads
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments SchedSetAll SchedSetAllRange

/-- Actual record helper arrays expose the sender-ID bytes. The suffix premise
only forbids a later column assignment from clobbering this register. -/
theorem record_id (I : Input) (present : Bool) (n kk gg p bpo bpr : Nat)
    (inst extra : List (Nat×Nat)) (i : Nat) (hi:i<8)
    (he:∀a∈extra,a.1≠prbit i) :
    (recordRow I present n kk 0 gg p bpo bpr inst extra)[prbit i]! =
      (bytesLE (I.ids.getD (kk/n) 0) 8).getD (gg+i) 0 := by
  unfold recordRow
  rw [SchedSetAll.cell _ _ _ (by unfold Codec.width prbit; omega)]
  rw [SchedSetAll.append,lookup_miss _ _ _ he,SchedSetAll.append]
  simp only [ite_true]
  change lookup (block 79 8 (fun j=>(bytesLE (I.ids.getD (kk/n) 0) 8).getD (gg+j) 0))
    (79+i) _ = _
  rw [lookup_block,if_pos (by omega)]
  congr 2
  omega

end ZkFormal.NearV3.Candidates.ProcPriorCodecAssignmentReads
