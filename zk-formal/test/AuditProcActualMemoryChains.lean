import ZkFormal.NearV3.Candidates.ProcActualMemoryChains
import ZkFormal.NearV3.Candidates.ProcActualMemoryOpSemantics
import ZkFormal.NearV3.Candidates.ProcActualMemoryChainReads
import ZkFormal.NearV3.Candidates.ProcActualMemoryChainEntry
import ZkFormal.NearV3.Candidates.ProcActualMemoryChainReplay
import ZkFormal.NearV3.Candidates.ProcActualMemoryChainSegments
import ZkFormal.NearV3.Candidates.MemConcatLocal

/-- info: 'ZkFormal.NearV3.Candidates.ProcActualMemoryChains.append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcActualMemoryChains.append

/-- info: 'ZkFormal.NearV3.Candidates.ProcActualMemoryChains.modify' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcActualMemoryChains.modify

/-- info: 'ZkFormal.NearV3.Candidates.ProcActualMemoryChains.empty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcActualMemoryChains.empty

/-- info: 'ZkFormal.NearV3.Candidates.ProcActualMemoryOpSemantics.read' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcActualMemoryOpSemantics.read

/-- info: 'ZkFormal.NearV3.Candidates.ProcActualMemoryOpSemantics.link' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcActualMemoryOpSemantics.link

/-- info: 'ZkFormal.NearV3.Candidates.ProcActualMemoryOpSemantics.budget' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcActualMemoryOpSemantics.budget

/-- info: 'ZkFormal.NearV3.Candidates.ProcActualMemoryChainReads.step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcActualMemoryChainReads.step

/-- info: 'ZkFormal.NearV3.Candidates.ProcActualMemoryChainReads.reads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcActualMemoryChainReads.reads

/-- info: 'ZkFormal.NearV3.Candidates.ProcActualMemoryChainReads.empty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcActualMemoryChainReads.empty

/-- info: 'ZkFormal.NearV3.Candidates.ProcActualMemoryChainEntry.budget_last' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcActualMemoryChainEntry.budget_last

/-- info: 'ZkFormal.NearV3.Candidates.ProcActualMemoryChainEntry.entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcActualMemoryChainEntry.entry

/-- info: 'ZkFormal.NearV3.Candidates.ProcActualMemoryChainReplay.entries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcActualMemoryChainReplay.entries

/-- info: 'ZkFormal.NearV3.Candidates.ProcActualMemoryChainReplay.round' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcActualMemoryChainReplay.round

/-- info: 'ZkFormal.NearV3.Candidates.ProcActualMemoryChainReplay.rounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcActualMemoryChainReplay.rounds

/-- info: 'ZkFormal.NearV3.Candidates.ProcActualMemoryChainReplay.replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcActualMemoryChainReplay.replay

/-- info: 'ZkFormal.NearV3.Candidates.ProcActualMemoryChainSegments.metadata' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcActualMemoryChainSegments.metadata

/-- info: 'ZkFormal.NearV3.Candidates.ProcActualMemoryChainSegments.selected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcActualMemoryChainSegments.selected

/-- info: 'ZkFormal.NearV3.Candidates.ProcActualMemoryChainSegments.make' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcActualMemoryChainSegments.make

/-- info: 'ZkFormal.NearV3.Candidates.ProcActualMemoryChainSegments.append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcActualMemoryChainSegments.append

/-- info: 'ZkFormal.NearV3.Candidates.ProcActualMemoryChainSegments.build' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcActualMemoryChainSegments.build

/-- info: 'ZkFormal.NearV3.Candidates.ProcActualMemoryChainSegments.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcActualMemoryChainSegments.run

/-- info: 'ZkFormal.NearV3.Candidates.MemConcatLocal.fold_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.MemConcatLocal.fold_rows

/-- info: 'ZkFormal.NearV3.Candidates.MemConcatLocal.rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.MemConcatLocal.rows

/-- info: 'ZkFormal.NearV3.Candidates.MemConcatLocal.flattened_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.MemConcatLocal.flattened_rows

/-- info: 'ZkFormal.NearV3.Candidates.MemConcatLocal.flattened_trace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.MemConcatLocal.flattened_trace

/-- info: 'ZkFormal.NearV3.Candidates.MemConcatLocal.table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.MemConcatLocal.table
