import ZkFormal.NearV3.Assembly.QueuePhysicalBalance

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Qv Qv.Candidates Qv.Candidates.ValueGen

def queueShardBytes (tau : Nat) (shards : List Nat) : List (List Nat) :=
  shards.zipIdx.flatMap (fun (s,i) =>
    (u64 s).zipIdx.map (fun (b,j) => [tau,i,j,b.toNat]))

/-- The buffered parser preserves the native shard list order and duplicates. -/
theorem queuePayload_buffered {bytes : Bytes} {shards : List Nat}
    (hm : (ParseMode.buffered shards).Accepts (some bytes)) :
    ∃ es : List BufferEntry, shards=es.map (·.1) ∧
      queuePayload (.buffered shards) bytes=.buffer (es.map byteBufferOfEntry) := by
  obtain ⟨es,rfl,hn,hs,he,hshards⟩ := hm
  have hd := pVec_ok "shard_buffers" bufferEntryParser bufferEntryBytes es [] hn
    (fun e he rest => bufferEntryParser_encode e (hs e he) rest)
  simp only [List.append_nil] at hd
  change pVec "shard_buffers" bufferEntryParser (bufferedBytes es)=.ok (es,[]) at hd
  exact ⟨es,hshards,by simp [queuePayload,hd]⟩

theorem queueRecord_buffered_shards (p : QueueProvider) {shards : List Nat}
    (hm : p.mode=.buffered shards) (ha : p.mode.Accepts (some p.bytes)) :
    (queueRecord p).shardBytes=queueShardBytes p.tau shards ∧
      (queueRecord p).shardCount=[[p.tau,0,8,shards.length]] := by
  rw [hm] at ha
  obtain ⟨es,rfl,hpayload⟩ := queuePayload_buffered ha
  simp only [queueRecord,hm,hpayload,Record.shardBytes,Record.shardCount,List.length_map]
  constructor
  · simp [queueShardBytes,List.zipIdx_map,List.flatMap_map,List.map_map,Function.comp_def,byteBufferOfEntry]
  · trivial

theorem queueRecord_other_shards (p : QueueProvider)
    (hm : ∀ shards, p.mode≠.buffered shards) :
    (queueRecord p).shardBytes=[] ∧ (queueRecord p).shardCount=[] := by
  cases h : p.mode with
  | empty => simp [queueRecord,queuePayload,h,Record.shardBytes,Record.shardCount]
  | raw => simp [queueRecord,queuePayload,h,Record.shardBytes,Record.shardCount]
  | buffered shards => exact False.elim (hm shards h)

open CombinedWalkGen

theorem plan_shard_messages (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve) :
    (plan pre v pres resolve).flatMap Walk.shardWordMessages =
      (if v.buffered.isSome then [[0,0,8,v.shards.length]] else []) ++ queueShardBytes 0 v.shards := by
  simp [plan,mainPlan,implicitPlan,mainWalk,Walk.shardWordMessages,queueShardBytes,
    List.flatMap_map,Nat.add_comm]

end ZkFormal.NearV3.Assembly
