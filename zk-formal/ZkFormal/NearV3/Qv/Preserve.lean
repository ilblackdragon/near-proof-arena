import ZkFormal.NearV3.Qv.Reads
import ZkFormal.NearV3.Assembly.Scheduler
import NearSpec.TrieUpsertProofs

/-! Move buffered queue reads across the scheduler write using the proved trie
update theorem, with well-formedness explicit. Receipt-write preservation is
separate and is not assumed by this module. -/
namespace ZkFormal.NearV3.Qv
open NearSpec NearSpecV3

theorem schedStep_find_other {ctx : ApplyCtx} {pre post : PTrie} {so : SchedOut}
    (hw : pre.wf = true) (h : schedStep prims ctx pre = .ok (post,so))
    (key : List Nat) (hne : key ≠ keyBwState) :
    post.find key = pre.find key := by
  obtain ⟨_,_,_,_,_,_,_,hu⟩ := Assembly.schedStep_complete h
  exact PTrie.find_upsert_other pre keyBwState key so.state post hw
    (by decide) hne hu

theorem schedStep_buffered_read {ctx : ApplyCtx} {pre post : PTrie} {so : SchedOut}
    (hw : pre.wf = true) (h : schedStep prims ctx pre = .ok (post,so)) :
    post.find keyBufferedIdx = pre.find keyBufferedIdx :=
  schedStep_find_other hw h _ (by decide)

theorem schedStep_group_read {ctx : ApplyCtx} {pre post : PTrie} {so : SchedOut}
    (hw : pre.wf = true) (h : schedStep prims ctx pre = .ok (post,so)) (s : Nat) :
    post.find (keyGroupsData s) = pre.find (keyGroupsData s) := by
  apply schedStep_find_other hw h
  simp [keyGroupsData,keyBwState,nibbles]

/-- The buffered value and every group-read availability fact can be taken
from the pre-state, even though execution reads them after the scheduler. -/
theorem MainValues.pre_buffer_reads {ctx : ApplyCtx} {pre mid post : PTrie}
    {so : SchedOut} {v : MainValues} (hw : pre.wf = true)
    (h : schedStep prims ctx pre = .ok (mid,so)) (hv : v.Reads pre mid post) :
    pre.find keyBufferedIdx = some v.buffered ∧
      ∀ s ∈ v.shards, ∃ value, pre.find (keyGroupsData s) = some value := by
  obtain ⟨_,hb,hg,_⟩ := hv
  rw [schedStep_buffered_read hw h] at hb
  refine ⟨hb,?_⟩
  intro s hs
  obtain ⟨value,hval⟩ := hg s hs
  rw [schedStep_group_read hw h s] at hval
  exact ⟨value,hval⟩

end ZkFormal.NearV3.Qv
