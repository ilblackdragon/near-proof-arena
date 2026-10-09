import ZkFormal.NearV3.Candidates.ProcessRepairSourceView
import ZkFormal.NearV3.Candidates.ProcessRepairSourceByteTag
import ZkFormal.NearV3.Candidates.ProcessRepairVbytesIdBound
import ZkFormal.NearV3.Candidates.ProcessRepairAccountByteTag
import ZkFormal.NearV3.Candidates.ProcessRepairFusedForestBytes
import ZkFormal.NearV3.Candidates.ProcessRepairGlobalForestBytes
import ZkFormal.NearV3.Candidates.ProcessRepairForestDigest
import ZkFormal.NearV3.Candidates.ProcessRepairForestRequests
import ZkFormal.NearV3.Candidates.ProcessRepairHeadHash
import ZkFormal.NearV3.Candidates.ProcessRepairKidHash
import ZkFormal.NearV3.Candidates.ProcessRepairValueHash
import ZkFormal.NearV3.Candidates.ProcessRepairNodeBytes
import ZkFormal.NearV3.Candidates.ProcessRepairForestEncoding
import ZkFormal.NearV3.Candidates.ProcessRepairValueRange

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairSourceView.local_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairSourceView.local_source

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairSourceView.cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairSourceView.cells

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairSourceByteTag.local_logical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairSourceByteTag.local_logical

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairSourceByteTag.bytes_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairSourceByteTag.bytes_count

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairSourceByteTag.tag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairSourceByteTag.tag

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairVbytesIdBound.sender_id' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairVbytesIdBound.sender_id

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairAccountByteTag.tag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairAccountByteTag.tag

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairFusedForestBytes.provider' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairFusedForestBytes.provider

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairGlobalForestBytes.provider' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairGlobalForestBytes.provider

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairForestDigest.node_digest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairForestDigest.node_digest

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairForestDigest.value_digest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairForestDigest.value_digest

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairForestRequests.head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairForestRequests.head

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairForestRequests.node_routed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairForestRequests.node_routed

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairForestRequests.node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairForestRequests.node

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairHeadHash.head_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairHeadHash.head_hash

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairHeadHash.public_pre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairHeadHash.public_pre

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairKidHash.kid_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairKidHash.kid_hash

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairValueHash.value_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairValueHash.value_hash

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairNodeBytes.bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairNodeBytes.bytes

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairForestEncoding.encoding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairForestEncoding.encoding

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairValueRange.revealed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairValueRange.revealed

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairValueRange.bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairValueRange.bytes
