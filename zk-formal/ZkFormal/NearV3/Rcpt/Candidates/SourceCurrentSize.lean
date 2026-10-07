import ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
import ZkFormal.NearV3.Rcpt.Candidates.SourceSize
import ZkFormal.NearV3.Rcpt.Candidates.DedupTable

/-! Current candidate shape accounting, not protocol admission. Source shapes are
read from the actual candidate AIR. QV parser37 is transcribed from the independently
kernel-checked QV lane (8463ced1/9f596fd8); combined52 reserves fifteen unimplemented
walk/control columns and additional auxiliary/quotient/final columns. -/
namespace ZkFormal.NearV3.Rcpt.Candidates
open ZkFormal.Size ZkFormal.Size.V3

def currentSourceShapes (g : Nat) : List TShape :=
  let sha := { shapeOf g shaT with maxLog := 23 }
  let src := shapeOf g (DedupTable.table 23)
  [sha, sha] ++ trieS g ++ chachaT.map (shapeOf g) ++ schedS g ++
    (rcptS g).set 4 src ++ [src] ++ v1S g

def qvParserShape : TShape := sh 37 3 6 3 22

def qvCombinedReserve : TShape := sh 52 8 6 8 22

def currentSourceSize : Nat := sizeOfWeq (partitionParams 2) (currentSourceShapes 2)

def currentParserSize : Nat :=
  sizeOfWeq (partitionParams 2) (currentSourceShapes 2 ++ [qvParserShape])

def currentReservedSize : Nat :=
  sizeOfWeq (partitionParams 2) (currentSourceShapes 2 ++ [qvCombinedReserve])

/-- Carry-table shapes include the additional endpoint interactions and gating degrees.
Bus64 is reserved for source carry; integrated AIR bus-count/disjointness proofs remain open. -/
def wiredSourceShapes (g : Nat) : List TShape :=
  let sha := { shapeOf g shaT with maxLog := 23 }
  let left := shapeOf g (DedupPartitionTable.leftTable DedupPartitionTable.sourceCarryBus)
  let right := shapeOf g (DedupPartitionTable.rightTable DedupPartitionTable.sourceCarryBus)
  [sha, sha] ++ trieS g ++ chachaT.map (shapeOf g) ++ schedS g ++
    (rcptS g).set 4 left ++ [right] ++ v1S g

def wiredReservedSize : Nat :=
  sizeOfWeq (partitionParams 2) (wiredSourceShapes 2 ++ [qvCombinedReserve])

set_option maxRecDepth 32768 in
theorem source_shape_g2 : shapeOf 2 (DedupTable.table 23) = sh 57 3 5 3 23 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem left_shape_g2 : shapeOf 2 (DedupPartitionTable.leftTable DedupPartitionTable.sourceCarryBus) = sh 57 4 7 4 23 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem right_shape_g2 : shapeOf 2 (DedupPartitionTable.rightTable DedupPartitionTable.sourceCarryBus) = sh 57 3 5 3 23 := by
  decide +kernel

set_option maxRecDepth 32768 in
/-- Generated running-product degree remains below the unchanged blowup16 ceiling. -/
theorem carry_degrees_fit :
    (DedupPartitionTable.leftTable DedupPartitionTable.sourceCarryBus).degree 2 = 8 ∧
    (DedupPartitionTable.rightTable DedupPartitionTable.sourceCarryBus).degree 2 = 6 ∧
    (DedupPartitionTable.leftTable DedupPartitionTable.sourceCarryBus).degree 2 ≤ 2 ^ (partitionParams 2).logBlowup ∧
    (DedupPartitionTable.rightTable DedupPartitionTable.sourceCarryBus).degree 2 ≤ 2 ^ (partitionParams 2).logBlowup := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Includes source carry interactions and the provisional combined queue reserve.
This is a shape-model equality, not an admission or completeness theorem. -/
theorem wiredReservedSize_eq : wiredReservedSize = 8347010 := by decide +kernel

theorem wiredReservedSize_margin : wiredReservedSize + 41598 = 8388608 := by
  rw [wiredReservedSize_eq]

end ZkFormal.NearV3.Rcpt.Candidates
