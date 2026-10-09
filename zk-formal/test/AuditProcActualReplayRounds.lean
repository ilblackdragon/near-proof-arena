import ZkFormal.NearV3.Candidates.ProcActualReplayRounds

/-- info: 'ZkFormal.NearV3.Candidates.ProcActualReplayRounds.replay_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcActualReplayRounds.replay_append

/-- info: 'ZkFormal.NearV3.Candidates.ProcActualReplayRounds.trace_replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcActualReplayRounds.trace_replay

/-- info: 'ZkFormal.NearV3.Candidates.ProcActualReplayRounds.model_replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcActualReplayRounds.model_replay
