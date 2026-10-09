import ZkFormal.NearV3.Candidates.ProcScanRequestByteCells
import ZkFormal.NearV3.Candidates.ProcScanByteTransition
import ZkFormal.NearV3.Candidates.ProcScanRequestRegisters

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestByteCells.first_byte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestByteCells.first_byte

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestByteCells.following_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestByteCells.following_bytes

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanByteTransition.stays' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanByteTransition.stays

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanByteTransition.rotates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanByteTransition.rotates

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanByteTransition.exhausted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanByteTransition.exhausted

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanByteTransition.consumes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanByteTransition.consumes

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestRegisters.mapped' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestRegisters.mapped

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestRegisters.cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestRegisters.cell

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestRegisters.rotates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestRegisters.rotates

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestRegisters.stays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestRegisters.stays
