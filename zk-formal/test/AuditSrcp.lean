import ZkFormal.NearV3.Rcpt.Link.CheckSources
import ZkFormal.NearV3.Rcpt.Link.WitnessSources
import ZkFormal.NearV3.Rcpt.Render.Srcp.ProofInputWf
import ZkFormal.NearV3.Rcpt.Link.SourceDuplicate
import ZkFormal.NearV3.Rcpt.Link.SourceVerify
import ZkFormal.NearV3.Rcpt.Link.SourceHashes
import ZkFormal.NearV3.Rcpt.Render.Srcp.TrafficProof
import ZkFormal.NearV3.Rcpt.Render.Srcp.TrafficBlock
import ZkFormal.NearV3.Rcpt.Render.Srcp.LocalProof
import ZkFormal.NearV3.Rcpt.Extract.Srcp.Proof
import ZkFormal.NearV3.Rcpt.Link.SourceHash
import ZkFormal.NearV3.Rcpt.Link.SourceNonempty

/-! Guard the recovered source-proof extraction and digest-byte reconstruction. -/

/-- info: 'ZkFormal.NearV3.SrcpProof.segFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.segFacts

/-- info: 'ZkFormal.NearV3.SrcpProof.segShape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.segShape

/-- info: 'ZkFormal.NearV3.SrcpProof.rootTraffic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.rootTraffic

/-- info: 'ZkFormal.NearV3.SrcpProof.segRowT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.segRowT

/-- info: 'ZkFormal.NearV3.SrcpProof.leaf_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.leaf_bytes

/-- info: 'ZkFormal.NearV3.SrcpProof.path_accumulator_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.path_accumulator_bytes

/-- info: 'ZkFormal.NearV3.sourceBlocks_has_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.sourceBlocks_has_new

/-- info: 'ZkFormal.NearV3.new_slot_filter_nonempty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.new_slot_filter_nonempty

/-- info: 'ZkFormal.NearV3.source_shuffle_nonempty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.source_shuffle_nonempty

/-- info: 'ZkFormal.NearV3.SrcpProof.leaf_bytes_traffic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.leaf_bytes_traffic

/-- info: 'ZkFormal.NearV3.SrcpProof.leaf_digest_traffic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.leaf_digest_traffic

/-- info: 'ZkFormal.NearV3.SrcpProof.path_digest_traffic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.path_digest_traffic

/-- info: 'ZkFormal.NearV3.SrcpProof.pathItem_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.pathItem_bytes

/-- info: 'ZkFormal.NearV3.SrcpProof.pathItem_traffic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.pathItem_traffic

/-- info: 'ZkFormal.NearV3.SrcpProof.counter_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.counter_bound

/-- info: 'ZkFormal.NearV3.SrcpProof.counter_id_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.counter_id_lt

/-- info: 'ZkFormal.NearV3.SrcpProof.pathItem_traffic_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.pathItem_traffic_closed

/-- info: 'ZkFormal.NearV3.SrcpProof.active_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.active_end

/-- info: 'ZkFormal.NearV3.SrcpProof.size_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.size_gate

/-- info: 'ZkFormal.NearV3.SrcpProof.size_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.size_prefix

/-- info: 'ZkFormal.NearV3.SrcpProof.size_traffic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.size_traffic

/-- info: 'ZkFormal.NearV3.srcp_rootFromPath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.srcp_rootFromPath

/-- info: 'ZkFormal.NearV3.srcp_verifyReceiptProof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.srcp_verifyReceiptProof

/-- info: 'ZkFormal.NearV3.SrcpProof.list_counter_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.list_counter_bound

/-- info: 'ZkFormal.NearV3.SrcpProof.list_id_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.list_id_lt

/-- info: 'ZkFormal.NearV3.SrcpProof.list_j_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.list_j_succ

/-- info: 'ZkFormal.NearV3.SrcpProof.leaf_traffic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.leaf_traffic

/-- info: 'ZkFormal.NearV3.SrcpProof.root_leaf_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.root_leaf_unit

/-- info: 'ZkFormal.NearV3.SrcpProof.next_path_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.next_path_unit

/-- info: 'ZkFormal.NearV3.SrcpProof.next_path_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.next_path_length

/-- info: 'ZkFormal.NearV3.SrcpProof.path_unit_traffic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.path_unit_traffic

/-- info: 'ZkFormal.NearV3.SrcpProof.path_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.path_run

/-- info: 'ZkFormal.NearV3.SrcpProof.path_items_traffic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.path_items_traffic

/-- info: 'ZkFormal.NearV3.SrcpProof.block_path_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.block_path_run

/-- info: 'ZkFormal.NearV3.SrcpProof.block_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.block_wf

/-- info: 'ZkFormal.NearV3.SrcpProof.block_traffic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.block_traffic

/-- info: 'ZkFormal.NearV3.SrcpProof.block_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.block_size

/-- info: 'ZkFormal.NearV3.SrcpProof.blocks_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.blocks_from

/-- info: 'ZkFormal.NearV3.SrcpProof.BlockChain.wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.BlockChain.wf

/-- info: 'ZkFormal.NearV3.SrcpProof.BlockChain.table_traffic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.BlockChain.table_traffic

/-- info: 'ZkFormal.NearV3.srcp_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.srcp_view

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.R_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.R_eq

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.rows_log_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.rows_log_bound

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.root_q_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.root_q_succ

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.mem_kinds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.mem_kinds

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.mem_recs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.mem_recs

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.leaf_registers' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.leaf_registers

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.path_registers' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.path_registers

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.path_first_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.path_first_flag

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.path_last_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.path_last_flag

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.leaf_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.leaf_shift

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.path_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.path_shift

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.firstAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.firstAt

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.lastAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.lastAt

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.kinds_adj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.kinds_adj

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.adjAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.adjAt

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.before_next' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.before_next

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.next_root_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.next_root_size

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.internal_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.internal_size

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.charge_gate' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.charge_gate

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.bool_constraints' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.bool_constraints

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.shape_constraints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.shape_constraints

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.lookup_gate_constraints' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.lookup_gate_constraints

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.digest_constraints' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.digest_constraints

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.first_constraints' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.first_constraints

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.last_constraints' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.last_constraints

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.end_constraints' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.end_constraints

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.list_carry_constraints' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.list_carry_constraints

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.register_constraints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.register_constraints

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.segment_constraints' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.segment_constraints

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.duplicate_constraint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.duplicate_constraint

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.window_constraints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.window_constraints

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.counter_constraints' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.counter_constraints

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.size_constraint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.size_constraint

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.table_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.table_local

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.row_traffic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.row_traffic

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.root_messages' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.root_messages

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.leaf_messages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.leaf_messages

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.path_byte_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.path_byte_value

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.path_digest_flag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.path_digest_flag

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.path_messages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.path_messages

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.block_messages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.block_messages

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.active_messages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.active_messages

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.size_messages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.size_messages

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.messages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.messages

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.table_traffic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.table_traffic

/-- info: 'ZkFormal.NearV3.source_ql' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.source_ql

/-- info: 'ZkFormal.NearV3.source_interval_before' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.source_interval_before

/-- info: 'ZkFormal.NearV3.source_lastQ_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.source_lastQ_le

/-- info: 'ZkFormal.NearV3.source_msgId_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.source_msgId_lt

/-- info: 'ZkFormal.NearV3.source_payload_field_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.source_payload_field_unique

/-- info: 'ZkFormal.NearV3.source_bytes_isolate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.source_bytes_isolate

/-- info: 'ZkFormal.NearV3.source_sha_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.source_sha_digest

/-- info: 'ZkFormal.NearV3.sourceEncoding_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.sourceEncoding_eq

/-- info: 'ZkFormal.NearV3.source_sha_digest_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.source_sha_digest_bytes

/-- info: 'ZkFormal.NearV3.source_predecessor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.source_predecessor

/-- info: 'ZkFormal.NearV3.source_final_payload' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.source_final_payload

/-- info: 'ZkFormal.NearV3.source_hashes_of_sha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.source_hashes_of_sha

/-- info: 'ZkFormal.NearV3.source_rootFromPath_of_sha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.source_rootFromPath_of_sha

/-- info: 'ZkFormal.NearV3.source_verifyReceiptProof_of_sha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.source_verifyReceiptProof_of_sha

/-- info: 'ZkFormal.NearV3.source_roots_eq_of_same_proof' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.source_roots_eq_of_same_proof

/-- info: 'ZkFormal.NearV3.source_roots_eq_of_lookupLast' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.source_roots_eq_of_lookupLast

/-- info: 'ZkFormal.NearV3.source_duplicate_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.source_duplicate_empty

/-- info: 'ZkFormal.NearV3.source_duplicate_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.source_duplicate_length

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.proofItems_indices' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.proofItems_indices

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.proofItems_canon' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.proofItems_canon

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.proofItems_lengths' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.proofItems_lengths

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.proofItems_steps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.proofItems_steps

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.blockOfProof_leaf_path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.blockOfProof_leaf_path

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.blocksOfProofs_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.blocksOfProofs_wf

/-- info: 'ZkFormal.NearV3.pPathItem_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.pPathItem_shape

/-- info: 'ZkFormal.NearV3.pEntry_path_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.pEntry_path_shape

/-- info: 'ZkFormal.NearV3.decodeStateWitness_path_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.decodeStateWitness_path_shape

/-- info: 'ZkFormal.NearV3.lookupLast_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.lookupLast_mem

/-- info: 'ZkFormal.NearV3.lookupLast_path_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.lookupLast_path_shape

/-- info: 'ZkFormal.NearV3.checkD0_source_paths' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.checkD0_source_paths

/-- info: 'ZkFormal.NearV3.relD0a_source_paths' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.relD0a_source_paths
