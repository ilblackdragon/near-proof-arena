import ZkFormal.NearV3.Qv.Candidates.EmptyRender
import ZkFormal.NearV3.Qv.Candidates.ShardTraffic
import ZkFormal.NearV3.Qv.Candidates.ValueBudget
open NearSpec ZkFormal.NearV3.Qv ZkFormal.NearV3.Qv.Candidates.ValueGen
#guard checkRows [] 0
#guard checkRows (emptyRows 4 0 2 (u64 300)) 4
#guard checkRows (emptyRows 4 0 2 (u64 300)) 5
#guard checkRows (bufferRows 5 0 1 []) 2
#guard checkRows (bufferRows 5 0 1 [⟨u64 9,u64 300⟩,⟨u64 2,u64 0⟩,⟨u64 9,u64 7⟩]) 7
#guard checkRows (rawRows 8 3 1 []) 0
#guard checkRows (rawRows 8 3 1 [0,255,17]) 2
#guard checkRows (emptyRows 4 0 2 (u64 300) ++ bufferRows 5 0 1 [] ++ rawRows 8 3 1 []) 5
-- Mutate the second queue index without changing its first copy.
#guard !(checkRows ((emptyRows 4 0 2 (u64 300)).modify 8 (fun r => r.set 6 45)) 4)
-- Mutate the count byte without changing the number of buffered entries.
#guard !(checkRows ((bufferRows 5 0 1 []).modify 0 (fun r => r.set 6 1)) 2)
-- A buffer may not stop before finishing its header.
#guard !(checkRows ((bufferRows 5 0 1 []).take 3) 2)

-- Repeat the acceptance/rejection fixtures over BabyBear.
#guard checkFieldRows [] 0
#guard checkFieldRows (emptyRows 4 0 2 (u64 300)) 4
#guard checkFieldRows (emptyRows 4 0 2 (u64 300)) 5
#guard checkFieldRows (bufferRows 5 0 1 []) 2
#guard checkFieldRows (bufferRows 5 0 1 [⟨u64 9,u64 300⟩,⟨u64 2,u64 0⟩,⟨u64 9,u64 7⟩]) 7
#guard checkFieldRows (rawRows 8 3 1 []) 0
#guard checkFieldRows (rawRows 8 3 1 [0,255,17]) 2
#guard checkFieldRows (emptyRows 4 0 2 (u64 300) ++ bufferRows 5 0 1 [] ++ rawRows 8 3 1 []) 5
#guard !(checkFieldRows ((emptyRows 4 0 2 (u64 300)).modify 8 (fun r => r.set 6 45)) 4)
#guard !(checkFieldRows ((bufferRows 5 0 1 []).modify 0 (fun r => r.set 6 1)) 2)
#guard !(checkFieldRows ((bufferRows 5 0 1 []).take 3) 2)

/-- info: 'ZkFormal.NearV3.Qv.Candidates.value_shape_g2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.value_shape_g2

/-- info: 'ZkFormal.NearV3.Qv.Candidates.value_table_wf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.value_table_wf

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.emptyRows_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.emptyRows_bytes

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.bufferRows_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.bufferRows_bytes

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.rawRows_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.rawRows_bytes

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.emptyTrace_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.emptyTrace_local

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.emptyGeneratedTrace_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.emptyGeneratedTrace_local

/-- info: 'ZkFormal.NearV3.Qv.Candidates.ValueGen.bufferRows_shards' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.Candidates.ValueGen.bufferRows_shards
