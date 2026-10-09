import ZkFormal.NearV3.Render.Ups.NativeMemoryAllocation
import ZkFormal.NearV3.Candidates.NativeMemoryAllocation

/-- info: 'ZkFormal.NearV3.Render.UpsGen.nativeMemoryBase_upper_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.UpsGen.nativeMemoryBase_upper_bound
/-- info: 'ZkFormal.NearV3.Render.UpsGen.nativeInstance_newChildMemory' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.UpsGen.nativeInstance_newChildMemory
/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.newchunk_mem_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.newchunk_mem_context
/-- info: 'ZkFormal.NearV3.Candidates.NativeReceiptMemoryBytes.accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.NativeReceiptMemoryBytes.accepted
/-- info: 'ZkFormal.NearV3.Candidates.NativeMemoryAllocation.accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.NativeMemoryAllocation.accepted
