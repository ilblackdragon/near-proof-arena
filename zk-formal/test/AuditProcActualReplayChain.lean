import ZkFormal.NearV3.Candidates.ProcActualReplayChain

/-- info: 'ZkFormal.NearV3.Candidates.ProcActualReplayChain.inv_exists' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcActualReplayChain.inv_exists

/-- info: 'ZkFormal.NearV3.Candidates.ProcActualReplayChain.run_stamped' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcActualReplayChain.run_stamped
