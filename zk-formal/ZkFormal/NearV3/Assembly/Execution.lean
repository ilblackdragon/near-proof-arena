import ZkFormal.NearV3.Assembly.Witness
import ZkFormal.NearV3.Qv.ReceiptPreserve

/-! Exact operational semantics for the reconstructed transition stores.
These are ordinary native run relations, independent of AIR acceptance.
Queue stages are kept explicit unless pre-state well-formedness is proved.
-/
namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

structure MainExecutionV3 where
  block : Blk
  previous : Blk
  bufferedShards : List Nat
  pre : PTrie
  result : MainOut

def MainExecutionV3.ctx (k : WalkD0) (m : MainExecutionV3) : ApplyCtx :=
  blockCtx k.L k.H.shardId k.slotB2.gasLimit m.block m.previous.hdr.nextGasPrice

structure MainExecutionV3.Valid (k : WalkD0) (x : ExtV3) (m : MainExecutionV3) : Prop where
  block : k.blks[k.b2i]? = some m.block
  previous : k.blks[k.b2i + 1]? = some m.previous
  buffered : ∃ v, (partialTrie (x.store 0) k.slotB2.prevStateRoot [keyBufferedIdx]).find
    keyBufferedIdx = some v ∧ NearSpecV3.bufferedShards v = .ok m.bufferedShards
  pre : m.pre = partialTrie (x.store 0) k.slotB2.prevStateRoot
    (mainKeys x.applied m.bufferedShards)
  preRoot : m.pre.hashOf = k.slotB2.prevStateRoot
  run : applyNewChunk prims (m.ctx k) m.pre x.applied = .ok m.result
  postRoot : m.result.trie.hashOf = x.post 0

theorem MainExecutionV3.Valid.queue_stages {k : WalkD0} {x : ExtV3}
    {m : MainExecutionV3} (h : m.Valid k x) :
    ∃ mid so, ∃ v : Qv.MainValues, schedStep prims (m.ctx k) m.pre = .ok (mid, so) ∧
      v.Valid ∧ v.Reads m.pre mid m.result.trie :=
  Qv.applyNewChunk_queue_reads h.run

theorem MainExecutionV3.Valid.queue_pre {k : WalkD0} {x : ExtV3}
    {m : MainExecutionV3} (h : m.Valid k x) (hw : m.pre.wf = true) :
    ∃ v : Qv.MainValues, v.Valid ∧ v.Reads m.pre m.pre m.pre :=
  Qv.applyNewChunk_pre_queue_reads hw h.run

/-- Chronological implicit transitions. Each reads its own authenticated store,
starts at the preceding computed root, and matches its extracted post-root. -/
inductive ImplicitRunV3 (k : WalkD0) (x : ExtV3) : Nat → Bytes → List Blk → Bytes → Prop
  | nil (tau : Nat) (root : Bytes) : ImplicitRunV3 k x tau root [] root
  | cons (tau : Nat) (root : Bytes) (b : Blk) (bs : List Blk) (post : PTrie) (last : Bytes)
      (run : applyMissingChunk prims
        (blockCtx k.L k.H.shardId k.slotB2.gasLimit b b.hdr.nextGasPrice)
        (partialTrie (x.store tau) root [keyDelayedIdx, keyBwState]) = .ok post)
      (postRoot : post.hashOf = x.post tau)
      (tail : ImplicitRunV3 k x (tau + 1) post.hashOf bs last) :
      ImplicitRunV3 k x tau root (b :: bs) last

end ZkFormal.NearV3.Assembly
