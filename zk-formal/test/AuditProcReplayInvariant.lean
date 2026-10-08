import ZkFormal.NearV3.Candidates.ExceptLoop
import ZkFormal.NearV3.Candidates.ProcConverted
import ZkFormal.NearV3.Candidates.ProcReplayChain
import ZkFormal.NearV3.Candidates.ProcReplayMetadata
/-- info: 'ZkFormal.NearV3.Candidates.ExceptLoop.invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ExceptLoop.invariant

/-- info: 'ZkFormal.NearV3.Candidates.ProcConverted.step_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcConverted.step_bounded

/-- info: 'ZkFormal.NearV3.Candidates.ProcConverted.loop_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcConverted.loop_bounded

/-- info: 'ZkFormal.NearV3.Candidates.ProcConverted.run_converted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcConverted.run_converted

/-- info: 'ZkFormal.NearV3.Candidates.ProcReplayChain.inv_exists' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcReplayChain.inv_exists

/-- info: 'ZkFormal.NearV3.Candidates.ProcReplayChain.run_stamped' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcReplayChain.run_stamped

/-- info: 'ZkFormal.NearV3.Candidates.ProcReplayMetadata.empty_cursor' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcReplayMetadata.empty_cursor

/-- info: 'ZkFormal.NearV3.Candidates.ProcReplayMetadata.initial' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcReplayMetadata.initial

/-- info: 'ZkFormal.NearV3.Candidates.ProcReplayMetadata.last_cursor' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcReplayMetadata.last_cursor

/-- info: 'ZkFormal.NearV3.Candidates.ProcReplayMetadata.adjacent_snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcReplayMetadata.adjacent_snoc

/-- info: 'ZkFormal.NearV3.Candidates.ProcReplayMetadata.follows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcReplayMetadata.follows

/-- info: 'ZkFormal.NearV3.Candidates.ProcReplayMetadata.run_metadata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcReplayMetadata.run_metadata

