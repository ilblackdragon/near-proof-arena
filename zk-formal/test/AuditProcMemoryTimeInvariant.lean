import ZkFormal.NearV3.Candidates.ProcMemoryTimeInvariant

/-- info: 'ZkFormal.NearV3.Candidates.ProcMemoryTimeInvariant.before_mono' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcMemoryTimeInvariant.before_mono

/-- info: 'ZkFormal.NearV3.Candidates.ProcMemoryTimeInvariant.append_time' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcMemoryTimeInvariant.append_time

/-- info: 'ZkFormal.NearV3.Candidates.ProcMemoryTimeInvariant.modify_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcMemoryTimeInvariant.modify_time

/-- info: 'ZkFormal.NearV3.Candidates.ProcMemoryTimeInvariant.empty_logs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcMemoryTimeInvariant.empty_logs

/-- info: 'ZkFormal.NearV3.Candidates.ProcMemoryTimeInvariant.read_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcMemoryTimeInvariant.read_step

/-- info: 'ZkFormal.NearV3.Candidates.ProcMemoryTimeInvariant.scan_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcMemoryTimeInvariant.scan_success

/-- info: 'ZkFormal.NearV3.Candidates.ProcMemoryTimeInvariant.ordered_scan' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcMemoryTimeInvariant.ordered_scan
