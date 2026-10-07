import ZkFormal.NearV3.Qv.Candidates.RecordTrafficContract
import ZkFormal.NearV3.Qv.Candidates.RecordShardTraffic
import ZkFormal.NearV3.Qv.Candidates.RecordProviders
import ZkFormal.NearV3.Qv.Candidates.RecordBusMessages
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

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.eval_nat_row' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.eval_nat_row

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.interaction_nat_fragment' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.interaction_nat_fragment

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.rowTraffic_nat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.rowTraffic_nat

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.parser_nat_bits_row' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.parser_nat_bits_row

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.records_rowTraffic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.records_rowTraffic

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.records_field_traffic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.records_field_traffic

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.recordsTraffic_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.recordsTraffic_bytes

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.natRowTraffic_qvc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.natRowTraffic_qvc

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.Record.firstFields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.Record.firstFields

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.Record.first_filter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.Record.first_filter

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.Record.provider_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.Record.provider_messages

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.recordsTraffic_providers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.recordsTraffic_providers

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.qsh_natTraffic_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.qsh_natTraffic_perm

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.bufferRows_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.bufferRows_counts

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.Record.shard_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.Record.shard_messages

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.Record.count_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.Record.count_messages

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.recordsTraffic_shards' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.recordsTraffic_shards

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.recordsTraffic_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.recordsTraffic_canonical

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.records_canonical_traffic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.records_canonical_traffic
