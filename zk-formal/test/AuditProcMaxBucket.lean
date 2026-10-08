import ZkFormal.NearV3.Candidates.ProcPendingTime
import ZkFormal.NearV3.Candidates.ProcMaxBucket
import ZkFormal.NearV3.Candidates.ProcModelTime

/-- info: 'ZkFormal.NearV3.Candidates.ProcPendingTime.append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPendingTime.append

/-- info: 'ZkFormal.NearV3.Candidates.ProcPendingTime.initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPendingTime.initial

/-- info: 'ZkFormal.NearV3.Candidates.ProcPendingTime.entry_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPendingTime.entry_inv

/-- info: 'ZkFormal.NearV3.Candidates.ProcPendingTime.entries_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPendingTime.entries_inv

/-- info: 'ZkFormal.NearV3.Candidates.ProcMaxBucket.insert_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcMaxBucket.insert_last

/-- info: 'ZkFormal.NearV3.Candidates.ProcMaxBucket.sort_id' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcMaxBucket.sort_id

/-- info: 'ZkFormal.NearV3.Candidates.ProcMaxBucket.fold_max' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcMaxBucket.fold_max

/-- info: 'ZkFormal.NearV3.Candidates.ProcMaxBucket.max_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcMaxBucket.max_mem

/-- info: 'ZkFormal.NearV3.Candidates.ProcMaxBucket.native_pop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcMaxBucket.native_pop

/-- info: 'ZkFormal.NearV3.Candidates.ProcModelTime.step_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcModelTime.step_inv

/-- info: 'ZkFormal.NearV3.Candidates.ProcModelTime.process_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcModelTime.process_time

