import ZkFormal.NearV3.Candidates.ProcessRepairRecordWriteSummary
import ZkFormal.NearV3.Candidates.ProcessRepairFamilyWrite
import ZkFormal.NearV3.Candidates.ProcessRepairRecordReceivedSummary

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairRecordWriteSummary.write_summary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairRecordWriteSummary.write_summary

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairFamilyWrite.family_write_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairFamilyWrite.family_write_source

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairRecordReceivedSummary.received_summary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairRecordReceivedSummary.received_summary
