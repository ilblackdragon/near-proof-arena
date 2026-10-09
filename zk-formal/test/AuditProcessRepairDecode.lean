import ZkFormal.NearV3.Candidates.ProcessRepairLengthSource
import ZkFormal.NearV3.Candidates.ProcessRepairLengthView
import ZkFormal.NearV3.Candidates.ProcessRepairRawFrameBytes
import ZkFormal.NearV3.Candidates.ProcessRepairHeaderZeros
import ZkFormal.NearV3.Candidates.ProcessRepairHeaderDecode
import ZkFormal.NearV3.Candidates.ProcessRepairAuthenticatedHeader
import ZkFormal.NearV3.Candidates.ProcessRepairRawLength
import ZkFormal.NearV3.Candidates.ProcessRepairNativeDecode

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairLengthSource.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairLengthSource.source

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairLengthSource.header' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairLengthSource.header

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairLengthView.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairLengthView.source

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairRawFrameBytes.byte_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairRawFrameBytes.byte_at

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairHeaderZeros.zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairHeaderZeros.zeros

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairHeaderDecode.count_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairHeaderDecode.count_bytes

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairAuthenticatedHeader.count_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairAuthenticatedHeader.count_bytes

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairRawLength.exact_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairRawLength.exact_length

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairRawLength.bytes_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairRawLength.bytes_eq

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairNativeDecode.decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairNativeDecode.decode
