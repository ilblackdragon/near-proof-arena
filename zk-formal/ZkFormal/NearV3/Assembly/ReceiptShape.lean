import ZkFormal.NearV3.Assembly.TrieShapeSet
import ZkFormal.NearV3.Qv.ReceiptPreserve

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpec.TransferV1 NearSpecV3 ReexecV3D0

theorem applyReceipt_shape_known {ctx : Ctx} {st out : Acc} {r : Receipt}
    (hs : TrieShape st.trie) (h : applyReceipt ctx st r = some out) :
    TrieShape out.trie ∧ ∀ key, st.trie.find key ≠ none → out.trie.find key ≠ none := by
  obtain ⟨bytes, hw⟩ := Qv.applyReceipt_set h
  exact ⟨shape_set _ _ bytes _ hs hw, fun _ hk => set_known hw hk⟩

theorem applySystemReceipt_shape_known {st out : Acc} {r : Receipt}
    (hs : TrieShape st.trie) (h : applySystemReceipt st r = .ok out) :
    TrieShape out.trie ∧ ∀ key, st.trie.find key ≠ none → out.trie.find key ≠ none := by
  obtain ⟨bytes, hw⟩ := Qv.applySystemReceipt_set h
  exact ⟨shape_set _ _ bytes _ hs hw, fun _ hk => set_known hw hk⟩

/-- Actual native receipt execution preserves all initially known lookups,
including repeated writes to the same receiver. No post-state wf is required. -/
theorem applyReceipts_shape_known (ctx : ApplyCtx) :
    ∀ (rs : List Receipt) (i : Nat) (st out : Acc × List Limit),
      TrieShape st.1.trie → applyReceipts ctx i st rs = .ok out →
      TrieShape out.1.trie ∧ ∀ key, st.1.trie.find key ≠ none → out.1.trie.find key ≠ none
  | [], _, st, out, hs, h => by cases h; exact ⟨hs, fun _ hk => hk⟩
  | r::rs, i, (acc,ls), out, hs, h => by
    simp only [applyReceipts] at h
    split at h
    · cases h
    · split at h
      · obtain ⟨acc',ha,h⟩ := bind_ok' h
        obtain ⟨hs',hk⟩ := applySystemReceipt_shape_known hs ha
        obtain ⟨hout,hknown⟩ := applyReceipts_shape_known ctx rs (i+1) (acc',ls) out hs' h
        exact ⟨hout,fun key hkey => hknown key (hk key hkey)⟩
      · split at h
        · split at h <;> cases h
        · rename_i acc' ha
          obtain ⟨ls',_,h⟩ := bind_ok' h
          obtain ⟨hs',hk⟩ := applyReceipt_shape_known hs ha
          obtain ⟨hout,hknown⟩ := applyReceipts_shape_known ctx rs (i+1) (acc',ls') out hs' h
          exact ⟨hout,fun key hkey => hknown key (hk key hkey)⟩

end ZkFormal.NearV3.Assembly
