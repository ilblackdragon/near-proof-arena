import ZkFormal.NearV3.Candidates.ProcPushPerm
import ZkFormal.NearV3.Candidates.ProcPushEntries
import ZkFormal.NearV3.Candidates.ProcPushConservation
/-- info: 'ZkFormal.NearV3.Candidates.ProcPushPerm.insert_perm' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPushPerm.insert_perm

/-- info: 'ZkFormal.NearV3.Candidates.ProcPushPerm.fold_perm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPushPerm.fold_perm

/-- info: 'ZkFormal.NearV3.Candidates.ProcPushPerm.sort_perm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPushPerm.sort_perm

/-- info: 'ZkFormal.NearV3.Candidates.ProcPushPerm.pop_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPushPerm.pop_perm

/-- info: 'ZkFormal.NearV3.Candidates.ProcPushEntries.entry_inv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPushEntries.entry_inv

/-- info: 'ZkFormal.NearV3.Candidates.ProcPushEntries.entries_pushes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPushEntries.entries_pushes

/-- info: 'ZkFormal.NearV3.Candidates.ProcPushConservation.step_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPushConservation.step_inv

/-- info: 'ZkFormal.NearV3.Candidates.ProcPushConservation.end_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPushConservation.end_zero

/-- info: 'ZkFormal.NearV3.Candidates.ProcPushConservation.process_balance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPushConservation.process_balance

/-- info: 'ZkFormal.NearV3.Candidates.ProcPushConservation.process_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPushConservation.process_perm

/-- info: 'ZkFormal.NearV3.Candidates.ProcPushConservation.process_log_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPushConservation.process_log_perm

