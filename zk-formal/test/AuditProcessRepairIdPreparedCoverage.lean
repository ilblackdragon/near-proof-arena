import ZkFormal.NearV3.Candidates.ProcessRepairIdPublicReceiver
import ZkFormal.NearV3.Candidates.ProcessRepairIdPublicFlags
import ZkFormal.NearV3.Candidates.ProcessRepairIdPreparedSend
import ZkFormal.NearV3.Candidates.ProcessRepairIdPreparedCoverage

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairIdPublicReceiver.raw_receivers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairIdPublicReceiver.raw_receivers

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairIdPublicReceiver.receiver_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairIdPublicReceiver.receiver_eq

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairIdPublicReceiver.other_tables' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairIdPublicReceiver.other_tables

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairIdPublicReceiver.matched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairIdPublicReceiver.matched

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairIdPublicFlags.flags' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairIdPublicFlags.flags

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairIdPreparedSend.header_n' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairIdPreparedSend.header_n

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairIdPreparedSend.sender' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairIdPreparedSend.sender

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairIdPreparedCoverage.coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairIdPreparedCoverage.coverage
