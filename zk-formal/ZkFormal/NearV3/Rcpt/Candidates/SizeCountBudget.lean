import ZkFormal.NearV3.Rcpt.Candidates.SizeCountTables
import ZkFormal.NearV3.Rcpt.Candidates.SourceCurrentSize

namespace ZkFormal.NearV3.Rcpt.Candidates.SizeCount
open ZkFormal.Size ZkFormal.Size.V3 ZkFormal.NearV3

def shapes : List TShape :=
  ((wiredSourceShapes 2 ++ [qvCombinedReserve]).set 2 (shapeOf 2 nodeTable)).set 4
    (shapeOf 2 valTable) |>.set 21 (shapeOf 2 sizeTable)

def bytes : Nat := sizeOfWeq (partitionParams 2) shapes

set_option maxRecDepth 32768 in
theorem source_shapes_unchanged :
    shapeOf 2 (sourceTable (DedupPartitionTable.leftTable DedupPartitionTable.sourceCarryBus))=
      shapeOf 2 (DedupPartitionTable.leftTable DedupPartitionTable.sourceCarryBus) ∧
    shapeOf 2 (sourceTable (DedupPartitionTable.rightTable DedupPartitionTable.sourceCarryBus))=
      shapeOf 2 (DedupPartitionTable.rightTable DedupPartitionTable.sourceCarryBus) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem bytes_eq : bytes=8361570 := by decide +kernel

theorem size_delta : bytes=wiredReservedSize+2496 := by
  rw [bytes_eq,wiredReservedSize_eq]

theorem margin : bytes+27038=8388608 := by rw [bytes_eq]

/- Arity becomes three on SIZE without adding another interaction or bus. -/
set_option maxRecDepth 32768 in
theorem message_arities :
    (nodeTable.interactions.filter (fun i => i.bus=B_SIZE)).map (fun i => i.msg.length)=[3] ∧
    (valTable.interactions.filter (fun i => i.bus=B_SIZE)).map (fun i => i.msg.length)=[3] ∧
    (sizeTable.interactions.filter (fun i => i.bus=B_SIZE)).map (fun i => i.msg.length)=[3] := by
  decide +kernel

end ZkFormal.NearV3.Rcpt.Candidates.SizeCount
