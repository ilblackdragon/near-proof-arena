import ZkFormal.NearV3.Assembly.TrieKnownWrites

namespace ZkFormal.NearV3.Assembly.Tests
open NearSpec

def overflowPre : PTrie := .ext [] (.leaf [] (.val []) 0) (2^64-1)

-- The native input is valid, although its parent and child memory totals are
-- inconsistent. Existing domain rules do not impose memory consistency.
example : overflowPre.wf=true := by decide

-- A successful native write crosses u64, invalidating full wf but preserving
-- structural validity and exact key lookup.
example : (overflowPre.upsert [] [1]).map PTrie.wf=some false := by decide
example : (overflowPre.upsert [] [1]).map (fun t => t.find [])=some (some (some [1])) := by decide
example : ∃ post, runWrites overflowPre [([],[1]),([],[2])]=some post ∧
    TrieShape post ∧ post.find []≠none := by
  let post := PTrie.ext [] (newLeaf [] [2]) (2^64-1+(newLeaf [] [2]).memD)
  have hr : runWrites overflowPre [([],[1]),([],[2])]=some post := by rfl
  obtain ⟨hs,hq⟩ := runWrites_shape_known (TrieShape.of_wf overflowPre (by decide))
    (writes := [([],[1]),([],[2])]) (by simp [nibblesOk]) hr
  exact ⟨post,hr,hs,hq [] (by decide)⟩

end ZkFormal.NearV3.Assembly.Tests
