import ZkFormal.NearV3.Assembly.ReceiptShape
import ZkFormal.NearV3.Assembly.TrieKnownWrites

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpec.TransferV1 NearSpecV3 ReexecV3D0

theorem schedStep_shape_known {ctx : ApplyCtx} {pre post : PTrie} {so : SchedOut}
    (hs : TrieShape pre) (h : schedStep prims ctx pre = .ok (post,so)) :
    TrieShape post ∧ ∀ key, pre.find key ≠ none → post.find key ≠ none := by
  obtain ⟨_,_,_,_,_,_,_,hu⟩ := schedStep_complete h
  exact ⟨shape_upsert _ _ _ _ hs (by decide) hu,
    fun _ hk => shape_upsert_known hs (by decide) hu hk⟩

/-- The scheduler's actual read certifies its write key before the upsert. -/
theorem schedStep_write_known {ctx : ApplyCtx} {pre post : PTrie} {so : SchedOut}
    (h : schedStep prims ctx pre = .ok (post,so)) :
    pre.find keyBwState ≠ none := by
  obtain ⟨prev,_,_,hr,_,_,_,_⟩ := schedStep_complete h
  rw [(Qv.readKey_iff _ _ _ _).mp hr]
  simp

/-- Full actual main execution preserves known keys despite unchecked output
memory counters. Shape is structural, not a post-state serialization bound. -/
theorem applyNewChunk_shape_known {ctx : ApplyCtx} {pre : PTrie}
    {rs : List Receipt} {out : MainOut} (hs : TrieShape pre)
    (h : applyNewChunk prims ctx pre rs = .ok out) :
    TrieShape out.trie ∧ ∀ key, pre.find key ≠ none → out.trie.find key ≠ none := by
  unfold applyNewChunk at h
  obtain ⟨_,_,h⟩ := bind_ok' h
  obtain ⟨_,_,h⟩ := bind_ok' h
  obtain ⟨⟨mid,so⟩,hsched,h⟩ := bind_ok' h
  dsimp only at h
  obtain ⟨_,_,h⟩ := bind_ok' h
  obtain ⟨_,_,h⟩ := bind_ok' h
  obtain ⟨_,_,h⟩ := bind_ok' h
  obtain ⟨⟨acc,ls⟩,ha,h⟩ := bind_ok' h
  dsimp only at h
  obtain ⟨_,_,h⟩ := bind_ok' h
  obtain ⟨_,_,h⟩ := bind_ok' h
  simp only [pure,Except.pure,Except.ok.injEq] at h
  subst out
  obtain ⟨hmid,hknown⟩ := schedStep_shape_known hs hsched
  obtain ⟨hout,hknown'⟩ := applyReceipts_shape_known _ _ _ _ _ hmid ha
  exact ⟨hout,fun key hk => hknown' key (hknown key hk)⟩

end ZkFormal.NearV3.Assembly
