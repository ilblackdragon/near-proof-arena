import ZkFormal.NearV3.Qv.Buffered

open NearSpec NearSpecV3 ZkFormal.NearV3.Qv

#guard (queueEmpty none "test").isOk = true
#guard (queueEmpty (some (u64 300 ++ u64 300)) "test").isOk = true
#guard (queueEmpty (some (u64 300 ++ u64 301)) "test").isOk = false
#guard (queueEmpty (some (List.replicate 15 0)) "test").isOk = false
#guard (queueEmpty (some (List.replicate 17 0)) "test").isOk = false
#guard (bufferedShards none).toOption = some []
#guard (bufferedShards (some (bufferedBytes []))).toOption = some []
-- Reference parsing preserves repeated and unsorted shard IDs.
#guard (bufferedShards (some (bufferedBytes [(9,300,300),(2,0,0),(9,7,7)]))).toOption = some [9,2,9]
#guard (bufferedShards (some (bufferedBytes [(9,300,301)]))).isOk = false
#guard (bufferedShards (some (bufferedBytes [(9,300,300)] ++ [0]))).isOk = false
#guard (bufferedShards (some [1,0,0,0])).isOk = false

/-- info: 'ZkFormal.NearV3.Qv.queueEmpty_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.queueEmpty_iff
/-- info: 'ZkFormal.NearV3.Qv.emptyQueue_some_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.emptyQueue_some_iff
/-- info: 'ZkFormal.NearV3.Qv.emptyQueue_bytewise' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.emptyQueue_bytewise
/-- info: 'ZkFormal.NearV3.Qv.bufferEntryParser_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.bufferEntryParser_inv
/-- info: 'ZkFormal.NearV3.Qv.bufferVec_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.bufferVec_inv
/-- info: 'ZkFormal.NearV3.Qv.bufferedShards_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.bufferedShards_encode
/-- info: 'ZkFormal.NearV3.Qv.bufferedShards_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.bufferedShards_iff
