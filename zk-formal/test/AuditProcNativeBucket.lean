import ZkFormal.NearV3.Candidates.ProcNativeBucket
import ZkFormal.NearV3.Candidates.ProcNativePush
import ZkFormal.NearV3.Candidates.ProcNativeBucketReplay

/-- info: 'ZkFormal.NearV3.Candidates.ProcNativeBucket.reqAt_source' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcNativeBucket.reqAt_source

/-- info: 'ZkFormal.NearV3.Candidates.ProcNativeBucket.step_state' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcNativeBucket.step_state

/-- info: 'ZkFormal.NearV3.Candidates.ProcNativeBucket.runL_state' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcNativeBucket.runL_state

/-- info: 'ZkFormal.NearV3.Candidates.ProcNativeBucket.entries_bucket_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcNativeBucket.entries_bucket_state

/-- info: 'ZkFormal.NearV3.Candidates.ProcNativePush.step_pushes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcNativePush.step_pushes

/-- info: 'ZkFormal.NearV3.Candidates.ProcNativeBucketReplay.entries_pushes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcNativeBucketReplay.entries_pushes

/-- info: 'ZkFormal.NearV3.Candidates.ProcNativeBucketReplay.bucket_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcNativeBucketReplay.bucket_exact

