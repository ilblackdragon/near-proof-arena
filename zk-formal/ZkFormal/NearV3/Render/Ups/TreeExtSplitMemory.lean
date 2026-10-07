import ZkFormal.NearV3.Render.Ups.TreeLeafSplitMemory

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

/-- Exact arithmetic for all four native extension splits, including clamped inherited memory. -/
theorem extSplitRun_memory (k : List Nat) (child : PTrie) (mem : Nat) (key : List Nat)
    (v : Bytes) (hw : (PTrie.ext k child mem).wf=true) (hk : FixedSuffix key)
    (hprefix : isPrefix k key=false) (hL : v.length<2^24) (baseI : UpsInst) :
    ∀ part∈(extSplitRun k child mem key v).parts,∀ base Q,encodeTreePart base part=some Q →
      Q.mB=splitChildMemory (commonPrefix k key).length part →
      RV (traceInstance baseI (extSplitRun k child mem key v) v)
        (withMemorySign (traceInstance baseI (extSplitRun k child mem key v) v) Q)=(part.output.memD:Int) := by
  have hp := commonPrefix_right k key
  have ho := commonPrefix_left k key
  have hkey := hk.length
  have hnon : k.drop (commonPrefix k key).length≠[] := by
    intro h
    rw [h,List.append_nil] at ho
    have hpre := (isPrefix_iff k key).mpr ⟨_,by simpa only [←ho] using hp⟩
    simp [hprefix] at hpre
  unfold extSplitRun
  dsimp only
  cases hd : k.drop (commonPrefix k key).length with
  | nil => exact (hnon hd).elim
  | cons x xs =>
    have hmoved := drop_successor_of_cons k _ x xs hd
    cases xs with
    | nil =>
      cases hd' : key.drop (commonPrefix k key).length with
      | nil =>
        simp only [List.isEmpty_cons,List.isEmpty_nil,Bool.false_eq_true,ite_false,ite_true,List.nil_append,List.cons_append]
        apply split_wrap_memory baseI _ key _ .ESl1 _ _ _ v hL
        intro part hpart base Q he hm
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hpart
        rcases hpart with rfl
        exact treeSpbChildSome_memory _ base Q k child mem x v rfl he hw rfl
          (by simpa [L,splitInstance,traceInstance] using hL)
      | cons y ys =>
        have hys : ys.length≤1 := by
          have h := congrArg List.length hd'
          simp only [List.length_drop,List.length_cons] at h; omega
        simp only [List.isEmpty_cons,List.isEmpty_nil,Bool.false_eq_true,ite_false,ite_true,List.nil_append,List.cons_append]
        apply split_wrap_memory baseI _ key _ .ESn1 _ _ _ v hL
        intro part hpart base Q he hm
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hpart
        rcases hpart with rfl|rfl
        · exact treeNlf_memory _ base Q _ ys v he hys rfl
            (by simpa [L,splitInstance,traceInstance] using hL)
        · exact treeSpbChildNone_memory _ base Q k ys child mem x y v rfl he hw hys rfl
            (by simpa [L,splitInstance,traceInstance] using hL)
    | cons z zs =>
      cases hd' : key.drop (commonPrefix k key).length with
      | nil =>
        simp only [List.isEmpty_cons,List.isEmpty_nil,Bool.false_eq_true,ite_false,ite_true,List.nil_append,List.cons_append]
        apply split_wrap_memory baseI _ key _ .ESl0 _ _ _ v hL
        intro part hpart base Q he hm
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hpart
        rcases hpart with rfl|rfl
        · exact treeMve_memory _ base Q k (z::zs) child mem he hw
            (by simpa [L,splitInstance,traceInstance] using hL)
        · exact treeSpbFreshSome_memory _ base Q _ (.ext (z::zs) child (extOwnMem (z::zs)+(mem-extOwnMem k))) v x
            (Or.inr rfl) he (by simpa [splitChildMemory,hmoved,PTrie.memD,PTrie.mem?] using hm) rfl
            (by simpa [L,splitInstance,traceInstance] using hL)
      | cons y ys =>
        have hys : ys.length≤1 := by
          have h := congrArg List.length hd'
          simp only [List.length_drop,List.length_cons] at h; omega
        simp only [List.isEmpty_cons,List.isEmpty_nil,Bool.false_eq_true,ite_false,ite_true,List.nil_append,List.cons_append]
        apply split_wrap_memory baseI _ key _ .ESn0 _ _ _ v hL
        intro part hpart base Q he hm
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hpart
        rcases hpart with rfl|rfl|rfl
        · exact treeMve_memory _ base Q k (z::zs) child mem he hw
            (by simpa [L,splitInstance,traceInstance] using hL)
        · exact treeNlf_memory _ base Q _ ys v he hys rfl
            (by simpa [L,splitInstance,traceInstance] using hL)
        · exact treeSpbFreshNone_memory _ base Q _ (.ext (z::zs) child (extOwnMem (z::zs)+(mem-extOwnMem k))) ys v x y
            (Or.inr rfl) he (by simpa [splitChildMemory,hmoved,PTrie.memD,PTrie.mem?] using hm) hys rfl
            (by simpa [L,splitInstance,traceInstance] using hL)
end ZkFormal.NearV3.Render.UpsGen
