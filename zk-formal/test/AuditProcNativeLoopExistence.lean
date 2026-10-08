import ZkFormal.NearV3.Candidates.ProcNativeRound
import ZkFormal.NearV3.Candidates.ProcNativeRoundExistence
import ZkFormal.NearV3.Candidates.ProcNativeLoopExistence
import ZkFormal.NearV3.Candidates.ProcNativeInitial

/-- info: 'ZkFormal.NearV3.Candidates.ProcNativeRound.shuffle_pullback' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcNativeRound.shuffle_pullback

/-- info: 'ZkFormal.NearV3.Candidates.ProcNativeRound.buckets_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcNativeRound.buckets_nonempty

/-- info: 'ZkFormal.NearV3.Candidates.ProcNativeRound.step_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcNativeRound.step_refines

/-- info: 'ZkFormal.NearV3.Candidates.ProcNativeRoundExistence.of_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcNativeRoundExistence.of_native

/-- info: 'ZkFormal.NearV3.Candidates.ProcNativeRoundExistence.processLoop_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcNativeRoundExistence.processLoop_succ

/-- info: 'ZkFormal.NearV3.Candidates.ProcNativeLoopExistence.empty_forIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcNativeLoopExistence.empty_forIn

/-- info: 'ZkFormal.NearV3.Candidates.ProcNativeLoopExistence.empty_state' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcNativeLoopExistence.empty_state

/-- info: 'ZkFormal.NearV3.Candidates.ProcNativeLoopExistence.loop_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcNativeLoopExistence.loop_exists

/-- info: 'ZkFormal.NearV3.Candidates.ProcNativeInitial.conv_nonempty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcNativeInitial.conv_nonempty

/-- info: 'ZkFormal.NearV3.Candidates.ProcNativeInitial.initial_pushes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcNativeInitial.initial_pushes

/-- info: 'ZkFormal.NearV3.Candidates.ProcNativeInitial.initial_buckets' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcNativeInitial.initial_buckets

/-- info: 'ZkFormal.NearV3.Candidates.ProcNativeInitial.prepared_process_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcNativeInitial.prepared_process_exists

