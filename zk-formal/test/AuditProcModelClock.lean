import ZkFormal.NearV3.Candidates.ProcModelEntryShape
import ZkFormal.NearV3.Candidates.ProcModelRoundShape
import ZkFormal.NearV3.Candidates.ProcModelClock
/-- info: 'ZkFormal.NearV3.Candidates.ProcModelEntryShape.stamped_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcModelEntryShape.stamped_append

/-- info: 'ZkFormal.NearV3.Candidates.ProcModelEntryShape.entry_shape' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcModelEntryShape.entry_shape

/-- info: 'ZkFormal.NearV3.Candidates.ProcModelEntryShape.entry_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcModelEntryShape.entry_inv

/-- info: 'ZkFormal.NearV3.Candidates.ProcModelEntryShape.entries_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcModelEntryShape.entries_inv

/-- info: 'ZkFormal.NearV3.Candidates.ProcModelEntryShape.entries_counts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcModelEntryShape.entries_counts

/-- info: 'ZkFormal.NearV3.Candidates.ProcModelRoundShape.step_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcModelRoundShape.step_inv

/-- info: 'ZkFormal.NearV3.Candidates.ProcModelRoundShape.process_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcModelRoundShape.process_trace

/-- info: 'ZkFormal.NearV3.Candidates.ProcModelClock.stamped_concat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcModelClock.stamped_concat

/-- info: 'ZkFormal.NearV3.Candidates.ProcModelClock.trace_flat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcModelClock.trace_flat

/-- info: 'ZkFormal.NearV3.Candidates.ProcModelClock.process_clock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcModelClock.process_clock

/-- info: 'ZkFormal.NearV3.Candidates.ProcModelClock.process_time_check' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcModelClock.process_time_check

