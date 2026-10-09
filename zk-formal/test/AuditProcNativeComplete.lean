import ZkFormal.NearV3.Candidates.ProcModelStep
import ZkFormal.NearV3.Candidates.ProcModelValid
import ZkFormal.NearV3.Candidates.ProcZeroPending
import ZkFormal.NearV3.Candidates.ProcZeroTransition
import ZkFormal.NearV3.Candidates.ProcZeroTrace
import ZkFormal.NearV3.Candidates.ProcRoundOrder
import ZkFormal.NearV3.Candidates.ProcNativeComplete
/-- info: 'ZkFormal.NearV3.Candidates.ProcModelStep.process_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcModelStep.process_eq

/-- info: 'ZkFormal.NearV3.Candidates.ProcModelValid.scalar_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcModelValid.scalar_valid

/-- info: 'ZkFormal.NearV3.Candidates.ProcModelValid.process_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcModelValid.process_valid

/-- info: 'ZkFormal.NearV3.Candidates.ProcModelValid.run_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcModelValid.run_valid

/-- info: 'ZkFormal.NearV3.Candidates.ProcZeroPending.insert_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcZeroPending.insert_mem

/-- info: 'ZkFormal.NearV3.Candidates.ProcZeroPending.sort_fold_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcZeroPending.sort_fold_mem

/-- info: 'ZkFormal.NearV3.Candidates.ProcZeroPending.sort_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcZeroPending.sort_mem

/-- info: 'ZkFormal.NearV3.Candidates.ProcZeroPending.seed_le_fold' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcZeroPending.seed_le_fold

/-- info: 'ZkFormal.NearV3.Candidates.ProcZeroPending.member_le_fold' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcZeroPending.member_le_fold

/-- info: 'ZkFormal.NearV3.Candidates.ProcZeroPending.zero_filter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcZeroPending.zero_filter

/-- info: 'ZkFormal.NearV3.Candidates.ProcZeroPending.zero_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcZeroPending.zero_head

/-- info: 'ZkFormal.NearV3.Candidates.ProcZeroPending.initial' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcZeroPending.initial

/-- info: 'ZkFormal.NearV3.Candidates.ProcZeroTransition.entry_pending' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcZeroTransition.entry_pending

/-- info: 'ZkFormal.NearV3.Candidates.ProcZeroTransition.entries_pending' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcZeroTransition.entries_pending

/-- info: 'ZkFormal.NearV3.Candidates.ProcZeroTransition.next_positive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcZeroTransition.next_positive

/-- info: 'ZkFormal.NearV3.Candidates.ProcZeroTransition.filtered_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcZeroTransition.filtered_pending

/-- info: 'ZkFormal.NearV3.Candidates.ProcZeroTrace.step_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcZeroTrace.step_inv

/-- info: 'ZkFormal.NearV3.Candidates.ProcZeroTrace.process_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcZeroTrace.process_trace

/-- info: 'ZkFormal.NearV3.Candidates.ProcZeroTrace.run_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcZeroTrace.run_trace

/-- info: 'ZkFormal.NearV3.Candidates.ProcRoundOrder.trace_empty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcRoundOrder.trace_empty

/-- info: 'ZkFormal.NearV3.Candidates.ProcRoundOrder.trace_snoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcRoundOrder.trace_snoc

/-- info: 'ZkFormal.NearV3.Candidates.ProcRoundOrder.cursor_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcRoundOrder.cursor_rule

/-- info: 'ZkFormal.NearV3.Candidates.ProcRoundOrder.stamped_rules' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcRoundOrder.stamped_rules

/-- info: 'ZkFormal.NearV3.Candidates.ProcRoundOrder.run_roundOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcRoundOrder.run_roundOrder

/-- info: 'ZkFormal.NearV3.Candidates.ProcRoundOrder.runData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcRoundOrder.runData

/-- info: 'ZkFormal.NearV3.Candidates.ProcNativeComplete.single_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcNativeComplete.single_local

/-- info: 'ZkFormal.NearV3.Candidates.ProcNativeComplete.list_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcNativeComplete.list_local

