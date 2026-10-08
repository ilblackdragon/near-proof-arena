import ZkFormal.NearV3.Candidates.NativeQueueFinalMessages

namespace ZkFormal.NearV3.Candidates.QueueKeyRepair
open NearSpec NearSpecV3 ZkFormal.Near Qv Qv.Candidates Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Near.Dsl

def sample : Walk := ⟨.delayed,0,0,0,none,0,0,false,false⟩

/-- The old queue packet list contains START and shifts native key positions. -/
theorem old_mismatch : sample.keyWordMessages ≠
    RcptE.keyMsgs (walkId 0 0) (keyDelayedIdx++[SYM_END]) := by decide

/-- The intended queue key contract is exactly the native walk contract. -/
def keyMessages (w : Walk) : List Msg :=
  RcptE.keyMsgs (walkId w.tau w.slot) (nibbles w.kind.bytes++[SYM_END])

theorem query_keys (w : Walk) (shards : List Nat) :
    keyMessages w=RcptE.keyMsgs
      (Rcpt.Candidates.NodePostUpdate.queueLookupQuery shards w).wid
      ((Rcpt.Candidates.NodePostUpdate.queueLookupQuery shards w).key++[SYM_END]) := rfl

open CombinedTable

/-- Preserve all other interactions, remove START, and number key symbols
from zero as required by the native walk table. -/
def interactions : List Interaction := CombinedTable.interactions.take 5 ++
  [send B_KEYNIB (c walk) [wid,smul 2 (c wp),nibble 4,k 0],
   send B_KEYNIB (c walk) [wid,.add (smul 2 (c wp)) (k 1),nibble 0,k 0],
   send B_KEYNIB (c wl) [wid,.add (smul 2 (c wp)) (k 2),k SYM_END,k 1]] ++
  CombinedTable.interactions.drop 9

def table : Air.Table := {CombinedTable.table with interactions:=interactions}

theorem constraints_unchanged : table.constraints=CombinedTable.table.constraints := rfl

theorem table_wf : table.wf ⟨[table],64,30⟩ 6=true := by decide +kernel

end ZkFormal.NearV3.Candidates.QueueKeyRepair
