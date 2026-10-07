import ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionCompile
import ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTraffic
import ZkFormal.NearV3.Rcpt.Candidates.DedupCarry
import ZkFormal.NearV3.Rcpt.Candidates.SourceCurrentSize

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.sourceCarryBus_reserved' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.sourceCarryBus_reserved

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.left_degree' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.left_degree

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.right_degree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.right_degree

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.left_width' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.left_width

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.right_width' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.right_width

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.carry_width' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.carry_width

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.source_shape_g2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.source_shape_g2

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.left_shape_g2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.left_shape_g2

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.right_shape_g2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.right_shape_g2

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.carry_degrees_fit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.carry_degrees_fit

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.wiredReservedSize_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.wiredReservedSize_eq

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.wiredReservedSize_margin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.wiredReservedSize_margin

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.left_carry_row' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.left_carry_row

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.right_carry_row' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.right_carry_row

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.left_carry_recv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.left_carry_recv

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.right_carry_send' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.right_carry_send

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.left_carry_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.left_carry_messages

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.right_carry_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.right_carry_messages

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.carry_equal_of_balance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.carry_equal_of_balance

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.carry_cells' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.carry_cells

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.left_normal_row' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.left_normal_row

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.right_normal_row' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.right_normal_row

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.pair_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.pair_messages

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.pair_counts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.pair_counts

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.rendered_carry_equal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.rendered_carry_equal

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.carry_balance_of_equal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.carry_balance_of_equal

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.qvParserShape_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.qvParserShape_eq

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.right_of_zero_first' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.right_of_zero_first

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.left_of_not_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.left_of_not_last

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.left_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.left_last

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.base_mult_bits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.base_mult_bits

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.left_mult_bits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.left_mult_bits

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.right_mult_bits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.right_mult_bits

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.left_rows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.left_rows

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.right_rows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.right_rows

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.left_field_constraints' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.left_field_constraints

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.right_field_constraints' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.right_field_constraints

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.left_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.left_local

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.right_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable.right_local

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.relD0a_partition_padding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.relD0a_partition_padding

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.relD0a_partition_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.relD0a_partition_local
