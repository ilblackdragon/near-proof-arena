import ZkFormal.NearV3.Qv.ByteBuffers
import ZkFormal.NearV3.Qv.ReadPlan

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

/-- info: 'ZkFormal.NearV3.Qv.readKey_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.readKey_iff

/-- info: 'ZkFormal.NearV3.Qv.groupReads_of_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.groupReads_of_loop

/-- info: 'ZkFormal.NearV3.Qv.applyNewChunk_queue_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.applyNewChunk_queue_reads

/-- info: 'ZkFormal.NearV3.Qv.applyMissingChunk_delayed_read' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.applyMissingChunk_delayed_read

/-- info: 'ZkFormal.NearV3.Qv.groupReads_loop_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.groupReads_loop_iff

/-- info: 'ZkFormal.NearV3.Qv.bufferedBytes_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.bufferedBytes_length

/-- info: 'ZkFormal.NearV3.Qv.bufferedValue_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.bufferedValue_length

/-- info: 'ZkFormal.NearV3.Qv.bufferedValue_count_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.bufferedValue_count_bound

/-- info: 'ZkFormal.NearV3.Qv.bufferedValue_count_u24' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.bufferedValue_count_u24

/-- info: 'ZkFormal.NearV3.Qv.schedStep_find_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.schedStep_find_other

/-- info: 'ZkFormal.NearV3.Qv.schedStep_buffered_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.schedStep_buffered_read

/-- info: 'ZkFormal.NearV3.Qv.schedStep_group_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.schedStep_group_read

/-- info: 'ZkFormal.NearV3.Qv.MainValues.pre_buffer_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.MainValues.pre_buffer_reads

/-- info: 'ZkFormal.NearV3.Qv.applyReceipt_set' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.applyReceipt_set

/-- info: 'ZkFormal.NearV3.Qv.applySystemReceipt_set' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.applySystemReceipt_set

/-- info: 'ZkFormal.NearV3.Qv.applyReceipt_find_other' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.applyReceipt_find_other

/-- info: 'ZkFormal.NearV3.Qv.applySystemReceipt_find_other' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.applySystemReceipt_find_other

/-- info: 'ZkFormal.NearV3.Qv.applyReceipts_find_other' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.applyReceipts_find_other

/-- info: 'ZkFormal.NearV3.Qv.applyReceipts_yield_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.applyReceipts_yield_read

/-- info: 'ZkFormal.NearV3.Qv.applyNewChunk_yield_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.applyNewChunk_yield_read

/-- info: 'ZkFormal.NearV3.Qv.applyNewChunk_pre_queue_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.applyNewChunk_pre_queue_reads

/-- info: 'ZkFormal.NearV3.Qv.ByteBuffer.entry_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.ByteBuffer.entry_bytes

/-- info: 'ZkFormal.NearV3.Qv.byteBuffered_accept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.byteBuffered_accept

/-- info: 'ZkFormal.NearV3.Qv.byteBuffered_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.byteBuffered_complete

/-- info: 'ZkFormal.NearV3.Qv.byteBuffered_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.byteBuffered_iff

/-- info: 'ZkFormal.NearV3.Qv.mainRequests_hold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.mainRequests_hold

/-- info: 'ZkFormal.NearV3.Qv.applyNewChunk_requests' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.applyNewChunk_requests

/-- info: 'ZkFormal.NearV3.Qv.applyMissingChunk_request' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.applyMissingChunk_request

/-- info: 'ZkFormal.NearV3.Qv.walkId_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.walkId_injective

/-- info: 'ZkFormal.NearV3.Qv.main_group_count_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.main_group_count_bound

/-- info: 'ZkFormal.NearV3.Qv.main_walkId_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Qv.main_walkId_bound
