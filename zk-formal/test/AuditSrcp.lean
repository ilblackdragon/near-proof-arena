import ZkFormal.NearV3.Rcpt.Render.Srcp.Accumulator
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
