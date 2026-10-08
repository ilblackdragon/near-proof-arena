import ZkFormal.NearV3.Candidates.ProcEntryAdjacent
import ZkFormal.NearV3.Candidates.ProcHeader
import ZkFormal.NearV3.Candidates.ProcNonEntry

/-- info: 'ZkFormal.NearV3.Candidates.ProcEntryScalar.flag_cast' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcEntryScalar.flag_cast

/-- info: 'ZkFormal.NearV3.Candidates.ProcEntryScalar.inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcEntryScalar.inverse

/-- info: 'ZkFormal.NearV3.Candidates.ProcEntryScalar.local_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcEntryScalar.local_entry

/-- info: 'ZkFormal.NearV3.Candidates.ProcEntryScalar.replay_entry' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcEntryScalar.replay_entry

/-- info: 'ZkFormal.NearV3.Candidates.ProcEntryAdjacent.adjacent_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcEntryAdjacent.adjacent_entry

/-- info: 'ZkFormal.NearV3.Candidates.ProcEntryAdjacent.entry_constraints' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcEntryAdjacent.entry_constraints

/-- info: 'ZkFormal.NearV3.Candidates.ProcHeader.header_constraints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcHeader.header_constraints

/-- info: 'ZkFormal.NearV3.Candidates.ProcNonEntry.constraints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcNonEntry.constraints
