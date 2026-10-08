import ZkFormal.NearV3.Candidates.ProcRoundGuards
import ZkFormal.NearV3.Candidates.ProcTagTransition
import ZkFormal.NearV3.Candidates.ProcRoundSuccess

/-- info: 'ZkFormal.NearV3.Candidates.ProcRoundGuards.initial' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcRoundGuards.initial

/-- info: 'ZkFormal.NearV3.Candidates.ProcRoundGuards.head_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcRoundGuards.head_mem

/-- info: 'ZkFormal.NearV3.Candidates.ProcRoundGuards.guards' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcRoundGuards.guards

/-- info: 'ZkFormal.NearV3.Candidates.ProcTagTransition.entry_positive' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcTagTransition.entry_positive

/-- info: 'ZkFormal.NearV3.Candidates.ProcTagTransition.entry_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcTagTransition.entry_below

/-- info: 'ZkFormal.NearV3.Candidates.ProcTagTransition.filtered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcTagTransition.filtered

/-- info: 'ZkFormal.NearV3.Candidates.ProcTagTransition.entries_tags' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcTagTransition.entries_tags

/-- info: 'ZkFormal.NearV3.Candidates.ProcRoundSuccess.initial_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcRoundSuccess.initial_ready

/-- info: 'ZkFormal.NearV3.Candidates.ProcRoundSuccess.step_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcRoundSuccess.step_success

