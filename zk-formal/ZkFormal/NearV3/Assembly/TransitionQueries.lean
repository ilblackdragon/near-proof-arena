import ZkFormal.NearV3.Assembly.PostShadows
import ZkFormal.NearV3.Assembly.RuntimeReplay

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

/-- Reproduce both queries made by the frozen unfolded-size calculation. This
raw-store selection does not allocate AIR node or value rows. -/
def nativeQueryStore (original : List Bytes) (root : Bytes) (keys : List (List Nat))
    (post : PTrie) : List Bytes :=
  transitionQueryStore original ((NearSpecV3.occs post).map NearSpecV3.nodeEnc ++ NearSpecV3.valsOf post) root post.hashOf keys keys

theorem nativeQueryStore_pre (original : List Bytes) (root : Bytes) (keys : List (List Nat))
    (post : PTrie) (hr : root.length = 32) :
    partialTrie (nativeQueryStore original root keys post) root keys = partialTrie original root keys :=
  transitionQueryStore_pre _ _ _ _ _ _ hr

theorem nativeQueryStore_post (original : List Bytes) (root : Bytes) (keys : List (List Nat))
    (post : PTrie) (hr : root.length = 32) (hp : post.hashOf.length = 32) :
    rebuildPost (nativeQueryStore original root keys post) post keys = rebuildPost original post keys := by
  unfold rebuildPost
  simpa only [List.append_assoc,nativeQueryStore] using transitionQueryStore_post original
    ((NearSpecV3.occs post).map NearSpecV3.nodeEnc ++ NearSpecV3.valsOf post) root post.hashOf keys keys hr hp

theorem nativeQueryStore_cost (original : List Bytes) (root : Bytes) (keys : List (List Nat))
    (post : PTrie) (hr : root.length = 32) :
    storeCost (nativeQueryStore original root keys post) ≤ storeCost original :=
  transitionQueryStore_cost _ _ _ _ _ _ hr

/-- Exact full-query replay also preserves every determinate singleton query. -/
theorem replay_singleton_find {small original : List Bytes} (root : Bytes)
    (keys : List (List Nat)) (key : List Nat) (hr : root.length = 32)
    (he : partialTrie small root keys = partialTrie original root keys)
    (hk : (partialTrie original root keys).find key ≠ none) :
    (partialTrie small root [key]).find key = (partialTrie original root [key]).find key := by
  have hb := built_spec original trieFuel root keys hr
  have hs := built_spec small trieFuel root keys hr
  have hsStored : Stored (mkStore small) (partialTrie small root keys) := hs.2.2.1
  rw [he] at hsStored
  have hroot : (partialTrie original root keys).hashOf = root := hb.1
  have hkeys : ∀ k ∈ [key], (partialTrie original root keys).find k ≠ none := by
    intro k h
    have : k = key := by simpa using h
    subst k
    exact hk
  have ho := buildFor_spec (mkStore original) trieFuel (partialTrie original root keys) [key]
    hb.2.1 hb.2.2.1 hkeys
  have hn := buildFor_spec (mkStore small) trieFuel (partialTrie original root keys) [key]
    hb.2.1 hsStored hkeys
  rw [hroot] at ho hn
  exact (hn.2 key (by simp) (hb.2.2.2 key)).trans
    (ho.2 key (by simp) (hb.2.2.2 key)).symm

theorem nativeQueryStore_main {ctx : ApplyCtx} {rs : List Receipt} {original : List Bytes}
    {root : Bytes} {keys : List (List Nat)} {out : MainOut}
    (hr : root.length = 32)
    (h : applyNewChunk prims ctx (partialTrie original root keys) rs = .ok out) :
    applyNewChunk prims ctx (partialTrie (nativeQueryStore original root keys out.trie) root keys) rs = .ok out := by
  rw [nativeQueryStore_pre _ _ _ _ hr]
  exact h

theorem nativeQueryStore_buffered {ctx : ApplyCtx} {rs : List Receipt} {original : List Bytes}
    {root : Bytes} {keys : List (List Nat)} {out : MainOut}
    (hr : root.length = 32)
    (h : applyNewChunk prims ctx (partialTrie original root keys) rs = .ok out) :
    (partialTrie (nativeQueryStore original root keys out.trie) root [keyBufferedIdx]).find keyBufferedIdx =
      (partialTrie original root [keyBufferedIdx]).find keyBufferedIdx := by
  have hw : (partialTrie original root keys).wf = true := (built_spec original trieFuel root keys hr).2.1
  obtain ⟨v,_,hv⟩ := Qv.applyNewChunk_pre_queue_reads hw h
  apply replay_singleton_find root keys keyBufferedIdx hr (nativeQueryStore_pre _ _ _ _ hr)
  rw [hv.2.1]
  simp

theorem nativeQueryStore_missing {ctx : ApplyCtx} {original : List Bytes} {root : Bytes} {post : PTrie}
    (hr : root.length = 32)
    (h : applyMissingChunk prims ctx (partialTrie original root [keyDelayedIdx,keyBwState]) = .ok post) :
    applyMissingChunk prims ctx
      (partialTrie (nativeQueryStore original root [keyDelayedIdx,keyBwState] post) root
        [keyDelayedIdx,keyBwState]) = .ok post := by
  rw [nativeQueryStore_pre _ _ _ _ hr]
  exact h

theorem nativeQueryStore_unfolded (original : List Bytes) (root : Bytes) (keys : List (List Nat))
    (post : PTrie) (hr : root.length = 32) (hp : post.hashOf.length = 32) :
    let pre := partialTrie original root keys
    let selected := nativeQueryStore original root keys post
    let pre' := partialTrie selected root keys
    NearSpecV3.unfoldedBytesT pre' + NearSpecV3.diffT pre' (rebuildPost selected post keys) =
      NearSpecV3.unfoldedBytesT pre + NearSpecV3.diffT pre (rebuildPost original post keys) := by
  dsimp only
  rw [nativeQueryStore_pre _ _ _ _ hr,nativeQueryStore_post _ _ _ _ hr hp]

end ZkFormal.NearV3.Assembly
