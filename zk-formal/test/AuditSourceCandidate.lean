import ZkFormal.NearV3.Rcpt.Candidates.RawWitnessBudget
import ZkFormal.NearV3.Rcpt.Candidates.SourceCount
import ZkFormal.NearV3.Rcpt.Candidates.SourceSizeCheck
import ZkFormal.NearV3.Rcpt.Candidates.SourceEncodingBudget

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.encoded_paths_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.encoded_paths_bound

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.occurrence_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.occurrence_bounds

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.unique_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.unique_bounds

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.budget_values' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.budget_values

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.occurrence_capacity' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.occurrence_capacity

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.unique_capacity' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.unique_capacity

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.unique_total_sha_budget' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.unique_total_sha_budget

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.partitionSize_g2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.partitionSize_g2

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.partitionSize_g2_margin' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.partitionSize_g2_margin

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.selectedSources_sublist' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.selectedSources_sublist

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.selectedSources_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.selectedSources_lookup

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.selectedSources_keys_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.selectedSources_keys_nodup

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.encoded_entries_paths_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.encoded_entries_paths_le

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.selected_pathCount_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.selected_pathCount_le

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.selected_path_budget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.selected_path_budget

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.pReceipt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.pReceipt_le

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.pChunkInner_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.pChunkInner_le

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.pPathItem_consumption' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.pPathItem_consumption

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.pEntries_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.pEntries_cost

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.decodeStateWitness_path_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.decodeStateWitness_path_bytes

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.relD0a_selected_path_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.relD0a_selected_path_budget

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.selectedSources_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.selectedSources_count

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.sourceBlock_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.sourceBlock_count

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.usedProofs_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.usedProofs_count
