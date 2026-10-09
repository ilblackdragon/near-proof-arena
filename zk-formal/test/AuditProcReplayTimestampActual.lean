import ZkFormal.NearV3.Candidates.ProcReplayTimestampActual

/-- info: 'ZkFormal.NearV3.Candidates.ProcReplayTimestampActual.round_time' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcReplayTimestampActual.round_time

/-- info: 'ZkFormal.NearV3.Candidates.ProcReplayTimestampActual.loop_time' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcReplayTimestampActual.loop_time

/-- info: 'ZkFormal.NearV3.Candidates.ProcReplayTimestampActual.replay_time' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcReplayTimestampActual.replay_time

/-- info: 'ZkFormal.NearV3.Candidates.ProcReplayTimestampActual.bucket_sum' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcReplayTimestampActual.bucket_sum

/-- info: 'ZkFormal.NearV3.Candidates.ProcReplayTimestampActual.replay_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcReplayTimestampActual.replay_bound

/-- info: 'ZkFormal.NearV3.Candidates.ProcReplayTimestampActual.prepared_replay_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcReplayTimestampActual.prepared_replay_bound
