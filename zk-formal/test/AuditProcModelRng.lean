import ZkFormal.NearV3.Candidates.ProcModelRng
import ZkFormal.NearV3.Candidates.ProcReplayRounds
/-- info: 'ZkFormal.NearV3.Candidates.ProcModelRng.entry_rng' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcModelRng.entry_rng

/-- info: 'ZkFormal.NearV3.Candidates.ProcModelRng.entries_rng' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcModelRng.entries_rng

/-- info: 'ZkFormal.NearV3.Candidates.ProcModelRng.step_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcModelRng.step_inv

/-- info: 'ZkFormal.NearV3.Candidates.ProcModelRng.process_trace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcModelRng.process_trace

/-- info: 'ZkFormal.NearV3.Candidates.ProcReplayRounds.replay_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcReplayRounds.replay_append

/-- info: 'ZkFormal.NearV3.Candidates.ProcReplayRounds.trace_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcReplayRounds.trace_replay

/-- info: 'ZkFormal.NearV3.Candidates.ProcReplayRounds.model_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcReplayRounds.model_replay

