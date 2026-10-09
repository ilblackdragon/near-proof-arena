import ZkFormal.NearV3.Candidates.ProcDistShardRow
import ZkFormal.NearV3.Candidates.ProcDistShardCells
import ZkFormal.NearV3.Candidates.ProcDistShardScalarCells
import ZkFormal.NearV3.Candidates.ProcDistShardRange
import ZkFormal.NearV3.Candidates.ProcDistShardAverageCells
import ZkFormal.NearV3.Candidates.ProcDistShardAverage
import ZkFormal.NearV3.Candidates.ProcDistShardOutputCells
import ZkFormal.NearV3.Candidates.ProcDistShardOutput
import ZkFormal.NearV3.Candidates.ProcDistShardControlCells
import ZkFormal.NearV3.Candidates.ProcDistShardGrid
import ZkFormal.NearV3.Candidates.ProcDistIndexTest

/-- info: 'ZkFormal.NearV3.Candidates.ProcDistShardRow.emitted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcDistShardRow.emitted

/-- info: 'ZkFormal.NearV3.Candidates.ProcDistShardCells.core_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcDistShardCells.core_cell

/-- info: 'ZkFormal.NearV3.Candidates.ProcDistShardCells.quotient_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcDistShardCells.quotient_bits

/-- info: 'ZkFormal.NearV3.Candidates.ProcDistShardCells.remainder_bits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcDistShardCells.remainder_bits

/-- info: 'ZkFormal.NearV3.Candidates.ProcDistShardCells.complement_bits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcDistShardCells.complement_bits

/-- info: 'ZkFormal.NearV3.Candidates.ProcDistShardScalarCells.unused_quotient_bits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcDistShardScalarCells.unused_quotient_bits

/-- info: 'ZkFormal.NearV3.Candidates.ProcDistShardScalarCells.unused_remainder_bits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcDistShardScalarCells.unused_remainder_bits

/-- info: 'ZkFormal.NearV3.Candidates.ProcDistShardScalarCells.quotients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcDistShardScalarCells.quotients

/-- info: 'ZkFormal.NearV3.Candidates.ProcDistShardRange.bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcDistShardRange.bounds

/-- info: 'ZkFormal.NearV3.Candidates.ProcDistShardRange.physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcDistShardRange.physical

/-- info: 'ZkFormal.NearV3.Candidates.ProcDistShardAverageCells.fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcDistShardAverageCells.fields

/-- info: 'ZkFormal.NearV3.Candidates.ProcDistShardAverage.division' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcDistShardAverage.division

/-- info: 'ZkFormal.NearV3.Candidates.ProcDistShardAverage.complement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcDistShardAverage.complement

/-- info: 'ZkFormal.NearV3.Candidates.ProcDistShardAverage.bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcDistShardAverage.bits

/-- info: 'ZkFormal.NearV3.Candidates.ProcDistShardAverage.physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcDistShardAverage.physical

/-- info: 'ZkFormal.NearV3.Candidates.ProcDistShardOutputCells.fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcDistShardOutputCells.fields

/-- info: 'ZkFormal.NearV3.Candidates.ProcDistShardOutput.physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcDistShardOutput.physical

/-- info: 'ZkFormal.NearV3.Candidates.ProcDistShardControlCells.fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcDistShardControlCells.fields

/-- info: 'ZkFormal.NearV3.Candidates.ProcDistShardGrid.frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcDistShardGrid.frame

/-- info: 'ZkFormal.NearV3.Candidates.ProcDistShardGrid.physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcDistShardGrid.physical

/-- info: 'ZkFormal.NearV3.Candidates.ProcDistIndexTest.inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcDistIndexTest.inverse

/-- info: 'ZkFormal.NearV3.Candidates.ProcDistIndexTest.annihilate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcDistIndexTest.annihilate
