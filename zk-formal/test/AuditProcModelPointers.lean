import ZkFormal.NearV3.Candidates.ProcRequestPointers
import ZkFormal.NearV3.Candidates.ProcEntryPointers
import ZkFormal.NearV3.Candidates.ProcModelPointers
import ZkFormal.NearV3.Candidates.ProcConvertedPointers

/-- info: 'ZkFormal.NearV3.Candidates.ProcRequestPointers.next_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcRequestPointers.next_valid

/-- info: 'ZkFormal.NearV3.Candidates.ProcRequestPointers.initial_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcRequestPointers.initial_valid

/-- info: 'ZkFormal.NearV3.Candidates.ProcRequestPointers.event_push_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcRequestPointers.event_push_valid

/-- info: 'ZkFormal.NearV3.Candidates.ProcEntryPointers.entry_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcEntryPointers.entry_inv

/-- info: 'ZkFormal.NearV3.Candidates.ProcEntryPointers.entries_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcEntryPointers.entries_inv

/-- info: 'ZkFormal.NearV3.Candidates.ProcModelPointers.step_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcModelPointers.step_inv

/-- info: 'ZkFormal.NearV3.Candidates.ProcModelPointers.process_pointers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcModelPointers.process_pointers

/-- info: 'ZkFormal.NearV3.Candidates.ProcConvertedPointers.convRaw_small' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcConvertedPointers.convRaw_small

/-- info: 'ZkFormal.NearV3.Candidates.ProcConvertedPointers.view_small' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcConvertedPointers.view_small

/-- info: 'ZkFormal.NearV3.Candidates.ProcConvertedPointers.model_index_guards' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcConvertedPointers.model_index_guards

/-- info: 'ZkFormal.NearV3.Candidates.ProcConvertedPointers.model_index_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcConvertedPointers.model_index_checks

