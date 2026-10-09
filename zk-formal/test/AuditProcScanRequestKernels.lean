import ZkFormal.NearV3.Candidates.ProcScanRequestFactor
import ZkFormal.NearV3.Candidates.ProcScanRequestArithmetic
import ZkFormal.NearV3.Candidates.ProcScanBitmapArithmetic
import ZkFormal.NearV3.Candidates.ProcScanRequestCells
import ZkFormal.NearV3.Candidates.ProcScanRequestBitCells
import ZkFormal.NearV3.Candidates.ProcScanRequestRange
import ZkFormal.NearV3.Candidates.ProcScanConvertedShape

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestFactor.native_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestFactor.native_eq

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestFactor.step_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestFactor.step_eq

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestArithmetic.position' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestArithmetic.position

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestArithmetic.coordinate_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestArithmetic.coordinate_bounds

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestArithmetic.quotient_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestArithmetic.quotient_bound

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestArithmetic.native_D' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestArithmetic.native_D

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestArithmetic.remainder_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestArithmetic.remainder_bounds

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestArithmetic.quotient_remainder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestArithmetic.quotient_remainder

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestArithmetic.y_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestArithmetic.y_test

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestArithmetic.y_annihilate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestArithmetic.y_annihilate

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestArithmetic.key_test' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestArithmetic.key_test

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestArithmetic.key_annihilate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestArithmetic.key_annihilate

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanBitmapArithmetic.b2n_mod2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanBitmapArithmetic.b2n_mod2

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanBitmapArithmetic.getBit_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanBitmapArithmetic.getBit_eq

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanBitmapArithmetic.byte_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanBitmapArithmetic.byte_pair

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanBitmapArithmetic.two_bits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanBitmapArithmetic.two_bits

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanBitmapArithmetic.coordinate_next' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanBitmapArithmetic.coordinate_next

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanBitmapArithmetic.byte_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanBitmapArithmetic.byte_bound

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanBitmapArithmetic.native_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanBitmapArithmetic.native_pair

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestCells.controls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestCells.controls

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestCells.payload' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestCells.payload

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestCells.progress' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestCells.progress

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestCells.quotients' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestCells.quotients

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestCells.flags' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestCells.flags

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestBitCells.quotients' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestBitCells.quotients

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestBitCells.remainders' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestBitCells.remainders

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestRange.num_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestRange.num_bits

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestRange.range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestRange.range

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanConvertedShape.step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanConvertedShape.step

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanConvertedShape.loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanConvertedShape.loop

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanConvertedShape.actual' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanConvertedShape.actual

