import ZkFormal.NearV3.Candidates.ProcessRepairBalance
import ZkFormal.NearV3.Candidates.ProcessRepairParent
import ZkFormal.NearV3.Candidates.ProcessRepairVParent
import ZkFormal.NearV3.Candidates.ProcessRepairRawBytes
import ZkFormal.NearV3.Candidates.ProcessRepairValueBytes

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairBalance.inventory' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairBalance.inventory

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairBalance.go' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairBalance.go

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairBalance.count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairBalance.count

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairBalance.balance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairBalance.balance

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairParent.balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairParent.balance

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairVParent.balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairVParent.balance

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairRawBytes.overlay_local' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairRawBytes.overlay_local

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairRawBytes.byte_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairRawBytes.byte_source

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairValueBytes.raw_byte' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairValueBytes.raw_byte

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairValueBytes.raw_byte_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairValueBytes.raw_byte_index

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairValueBytes.raw_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairValueBytes.raw_view
