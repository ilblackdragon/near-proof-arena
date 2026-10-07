import ZkFormal.NearV3.Assembly.ExactReplay
import ZkFormal.NearV3.Qv.ReceiptPreserve

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

/-- Native main execution is identical after store normalization. -/
theorem applyNewChunk_normalStore (ctx : ApplyCtx) (rs : List Receipt)
    (ws : List Bytes) (root : Bytes) (keys : List (List Nat)) (hr : root.length = 32) :
    applyNewChunk prims ctx
      (partialTrie (normalStore (partialTrie ws root keys)) root keys) rs =
    applyNewChunk prims ctx (partialTrie ws root keys) rs := by
  rw [partialTrie_normalStore ws root keys hr]

/-- Native implicit execution is identical after store normalization. -/
theorem applyMissingChunk_normalStore (ctx : ApplyCtx)
    (ws : List Bytes) (root : Bytes) (hr : root.length = 32) :
    applyMissingChunk prims ctx
      (partialTrie (normalStore (partialTrie ws root [keyDelayedIdx, keyBwState])) root
        [keyDelayedIdx, keyBwState]) =
    applyMissingChunk prims ctx (partialTrie ws root [keyDelayedIdx, keyBwState]) := by
  rw [partialTrie_normalStore ws root _ hr]

/-- The separate buffered-index discovery pass is preserved from actual main success,
using the checked queue-preservation theorem to establish pre-state determinacy. -/
theorem applyNewChunk_normalStore_buffered {ctx : ApplyCtx} {rs : List Receipt}
    {ws : List Bytes} {root : Bytes} {keys : List (List Nat)} {out : MainOut}
    (hr : root.length = 32)
    (h : applyNewChunk prims ctx (partialTrie ws root keys) rs = .ok out) :
    (partialTrie (normalStore (partialTrie ws root keys)) root [keyBufferedIdx]).find
      keyBufferedIdx = (partialTrie ws root [keyBufferedIdx]).find keyBufferedIdx := by
  have hw : (partialTrie ws root keys).wf = true := (built_spec ws trieFuel root keys hr).2.1
  obtain ⟨v, _, hv⟩ := Qv.applyNewChunk_pre_queue_reads hw h
  apply partialTrie_normalStore_singleton_find ws root keys keyBufferedIdx hr
  rw [hv.2.1]
  simp

end ZkFormal.NearV3.Assembly
