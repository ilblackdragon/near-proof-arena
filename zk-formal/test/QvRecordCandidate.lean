import ZkFormal.NearV3.Qv.Candidates.RecordTraffic
import ZkFormal.NearV3.Qv.Candidates.RecordLocal

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.terminal_record_transfer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.terminal_record_transfer
/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.interior_record_transfer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.interior_record_transfer
/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.padding_record_local' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.padding_record_local
/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.Record.rows_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.Record.rows_length
/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.Record.local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.Record.local
/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.Record.markers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.Record.markers
/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.Record.placed_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.Record.placed_local

open NearSpec ZkFormal.NearV3.Qv.Candidates.ValueGen
private def boundaryRecords : List Record :=
  [⟨1,0,2,.empty (u64 300)⟩,⟨2,0,1,.empty (u64 9)⟩]
private def mixedRecords : List Record :=
  [⟨1,0,2,.empty (u64 300)⟩,⟨2,0,1,.buffer [⟨u64 99,u64 3⟩]⟩,
   ⟨3,1,1,.raw []⟩,⟨4,2,1,.raw [0,255,7]⟩]
#guard checkRows (recordsRows boundaryRecords) 5
#guard checkFieldRows (recordsRows boundaryRecords) 5
#guard checkRows (recordsRows mixedRecords) 6
#guard checkFieldRows (recordsRows mixedRecords) 6
-- Corrupt a record-start marker at a real cross-record boundary.
#guard !(checkRows ((recordsRows boundaryRecords).modify 16 (fun r => r.set 1 0)) 5)
#guard !(checkFieldRows ((recordsRows boundaryRecords).modify 16 (fun r => r.set 1 0)) 5)

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.recordsRows_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.recordsRows_length
/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.recordsCell_first' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.recordsCell_first
/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.recordsTrace_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.recordsTrace_local

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.Record.byteMessages' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.Record.byteMessages

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.Record.size_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.Record.size_bytes

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.records_byteMessages' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.records_byteMessages

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.recordsSize_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.recordsSize_exact

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.recordsSize_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.recordsSize_le

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.records_table_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.records_table_local
