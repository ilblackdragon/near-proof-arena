import ZkFormal.NearV3.Render.Ups.TreeSplitMemoryLink

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

/-- Exact native leaf split arithmetic; serialization is handled modulo u64 later. -/
theorem leafSplitRun_memory (k : List Nat) (old : Slot) (mem : Nat) (key : List Nat)
    (v : Bytes) (hw : (PTrie.leaf k old mem).wf=true) (hk : FixedSuffix key)
    (hne : k≠key) (hL : v.length<2^24) (baseI : UpsInst) :
    ∀ part∈(leafSplitRun k old mem key v).parts,∀ base Q,encodeTreePart base part=some Q →
      Q.mB=splitChildMemory (commonPrefix k key).length part →
      RV (traceInstance baseI (leafSplitRun k old mem key v) v)
        (withMemorySign (traceInstance baseI (leafSplitRun k old mem key v) v) Q)=(part.output.memD:Int) := by
  have hp := commonPrefix_right k key
  have ho := commonPrefix_left k key
  have hkey := hk.length
  unfold leafSplitRun
  dsimp only
  cases hd : k.drop (commonPrefix k key).length with
  | nil =>
    cases hd' : key.drop (commonPrefix k key).length with
    | nil => simp only [hd,List.append_nil] at ho; simp only [hd',List.append_nil] at hp; exact (hne (ho.trans hp.symm)).elim
    | cons y ys =>
      have hys : ys.length≤1 := by
        have h := congrArg List.length hd'
        simp only [List.length_drop,List.length_cons] at h; omega
      apply split_wrap_memory baseI _ key _ .LSa _ _ _ v hL
      intro part hpart base Q he hm
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hpart
      rcases hpart with rfl|rfl
      · exact treeNlf_memory _ base Q _ ys v he hys rfl (by simpa [L,splitInstance,traceInstance] using hL)
      · exact treeSpbValue_memory _ base Q k ys old mem y v rfl he hw hys rfl
          (by simpa [L,splitInstance,traceInstance] using hL)
  | cons x xs =>
    have hmoved := drop_successor_of_cons k _ x xs hd
    cases hd' : key.drop (commonPrefix k key).length with
    | nil =>
      apply split_wrap_memory baseI _ key _ .LSb _ _ _ v hL
      intro part hpart base Q he hm
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hpart
      rcases hpart with rfl|rfl
      · exact treeMvl_memory _ base Q k xs old mem he hw (by simpa [L,splitInstance,traceInstance] using hL)
      · exact treeSpbFreshSome_memory _ base Q _ (.leaf xs old (leafMem xs old.len)) v x
          (Or.inl rfl) he (by simpa [splitChildMemory,hmoved,PTrie.memD,PTrie.mem?] using hm) rfl
          (by simpa [L,splitInstance,traceInstance] using hL)
    | cons y ys =>
      have hys : ys.length≤1 := by
        have h := congrArg List.length hd'
        simp only [List.length_drop,List.length_cons] at h; omega
      apply split_wrap_memory baseI _ key _ .LSc _ _ _ v hL
      intro part hpart base Q he hm
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hpart
      rcases hpart with rfl|rfl|rfl
      · exact treeMvl_memory _ base Q k xs old mem he hw (by simpa [L,splitInstance,traceInstance] using hL)
      · exact treeNlf_memory _ base Q _ ys v he hys rfl (by simpa [L,splitInstance,traceInstance] using hL)
      · exact treeSpbFreshNone_memory _ base Q _ (.leaf xs old (leafMem xs old.len)) ys v x y
          (Or.inl rfl) he (by simpa [splitChildMemory,hmoved,PTrie.memD,PTrie.mem?] using hm) hys rfl
          (by simpa [L,splitInstance,traceInstance] using hL)
end ZkFormal.NearV3.Render.UpsGen
