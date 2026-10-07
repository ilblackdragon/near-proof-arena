import ZkFormal.NearV3.Rcpt.Candidates.DedupSha
import ZkFormal.NearV3.Rcpt.Candidates.DedupCounters
import ZkFormal.NearV3.Rcpt.Candidates.PartitionCapacity
import ZkFormal.NearV3.Rcpt.Candidates.PreparedMetadata
import ZkFormal.NearV3.Rcpt.Candidates.DedupRender
import ZkFormal.NearV3.Rcpt.Candidates.SourceSize22
import ZkFormal.NearV3.Rcpt.Candidates.OrderedSources
import ZkFormal.NearV3.Rcpt.Candidates.PreparedVerified
import ZkFormal.NearV3.Rcpt.Candidates.SourceRepetition
import ZkFormal.NearV3.Rcpt.Candidates.PreparedSourceCount
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

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.preparedSourceLists_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.preparedSourceLists_count

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.prepClaim_source_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.prepClaim_source_count

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.prepD0_source_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.prepD0_source_count

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.sourceDup_repeated' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.sourceDup_repeated

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.repeated_receipts_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.repeated_receipts_empty

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.sourceRepeated_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.sourceRepeated_length

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.sourceRootsConsistent_of_verified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.sourceRootsConsistent_of_verified

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.sourceRootsConsistent_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.sourceRootsConsistent_iff

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.sources_verified_of_computed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.sources_verified_of_computed

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.slotSources_verified' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.slotSources_verified

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.preparedSourceLists_verified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.preparedSourceLists_verified

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.preparedSourceLists_roots_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.preparedSourceLists_roots_consistent

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.slotSources_authenticated' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.slotSources_authenticated

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.preparedSourceLists_authenticated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.preparedSourceLists_authenticated

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.sourceMetadataConsistent_of_authenticated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.sourceMetadataConsistent_of_authenticated

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.preparedSourceLists_metadata_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.preparedSourceLists_metadata_consistent

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.orderedSources_keys_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.orderedSources_keys_nodup

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.orderedSources_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.orderedSources_perm

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.orderedSources_pathCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.orderedSources_pathCount

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.raw_ordered_path_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.raw_ordered_path_budget

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.relD0a_prepared_metadata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.relD0a_prepared_metadata

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.relD0a_prepared_claim_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.relD0a_prepared_claim_metadata

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.R_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.R_eq

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.R_accounting' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.R_accounting

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.R_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.R_bound

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.duplicate_header_only' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.duplicate_header_only

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.rows_capacity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.rows_capacity

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.log23_not_wf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.log23_not_wf

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.computed_perm_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.computed_perm_selected

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.raw_computed_path_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.raw_computed_path_budget

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.firstSourceIndices_keys_nodup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.firstSourceIndices_keys_nodup

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.firstSourceEntries_raw_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.firstSourceEntries_raw_budget

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.selected_paths' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.selected_paths

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.relD0a_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.relD0a_inputs

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.relD0a_row_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.relD0a_row_bound

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.relD0a_work_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.relD0a_work_bounds

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.message_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.message_count

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.nextQ_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.nextQ_bound

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.computed_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.computed_end

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.duplicate_counter_stays' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.duplicate_counter_stays

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.relD0a_counter_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.relD0a_counter_bound

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.splitTrace_reconstruct' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.splitTrace_reconstruct

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.source_partition_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.source_partition_capacity

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.splitBudget_reconstruct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.splitBudget_reconstruct

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.source_sha_partition_capacity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.source_sha_partition_capacity

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.global_sha_partition_capacity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.global_sha_partition_capacity

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.bounded_preimage_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.bounded_preimage_rows

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.block_payload_widths' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.block_payload_widths

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.sourceWeights_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.sourceWeights_exact

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.relD0a_sha_partition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.relD0a_sha_partition
