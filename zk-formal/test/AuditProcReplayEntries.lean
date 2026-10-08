import ZkFormal.NearV3.Candidates.ExceptRange
import ZkFormal.NearV3.Candidates.ProcReplayShape
import ZkFormal.NearV3.Candidates.ProcReplayDecisions
import ZkFormal.NearV3.Candidates.ProcReplayAllowance
import ZkFormal.NearV3.Candidates.ProcReplayEntries
/-- info: 'ZkFormal.NearV3.Candidates.ExceptRange.invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ExceptRange.invariant

/-- info: 'ZkFormal.NearV3.Candidates.ExceptRange.range_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ExceptRange.range_invariant

/-- info: 'ZkFormal.NearV3.Candidates.ProcReplayShape.indexed_push' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcReplayShape.indexed_push

/-- info: 'ZkFormal.NearV3.Candidates.ProcReplayShape.check_true' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcReplayShape.check_true

/-- info: 'ZkFormal.NearV3.Candidates.ProcReplayShape.run_shapes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcReplayShape.run_shapes

/-- info: 'ZkFormal.NearV3.Candidates.ProcReplayDecisions.rem_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcReplayDecisions.rem_lt

/-- info: 'ZkFormal.NearV3.Candidates.ProcReplayDecisions.check_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcReplayDecisions.check_lt

/-- info: 'ZkFormal.NearV3.Candidates.ProcReplayDecisions.run_decisions' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcReplayDecisions.run_decisions

/-- info: 'ZkFormal.NearV3.Candidates.ProcReplayAllowance.link_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcReplayAllowance.link_bound

/-- info: 'ZkFormal.NearV3.Candidates.ProcReplayAllowance.set_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcReplayAllowance.set_bound

/-- info: 'ZkFormal.NearV3.Candidates.ProcReplayAllowance.decrease_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcReplayAllowance.decrease_bound

/-- info: 'ZkFormal.NearV3.Candidates.ProcReplayAllowance.run_allowances' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcReplayAllowance.run_allowances

/-- info: 'ZkFormal.NearV3.Candidates.ProcReplayEntries.maxAllowance_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcReplayEntries.maxAllowance_lt

/-- info: 'ZkFormal.NearV3.Candidates.ProcReplayEntries.run_entries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcReplayEntries.run_entries

/-- info: 'ZkFormal.NearV3.Candidates.ProcReplayEntries.runData_of_roundOrder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcReplayEntries.runData_of_roundOrder

