import ZkFormal.NearV3.Render.Ups.TreeLeafSplitDispatch

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

/-- Native extension split dispatch, with inherited children or an emitted moved extension. -/
theorem extSplitRun_byteInput (k : List Nat) (child : PTrie) (mem : Nat) (key : List Nat)
    (v : Bytes) (hw : (PTrie.ext k child mem).wf=true) (hk : FixedSuffix key)
    (hprefix : isPrefix k key=false) (baseI : UpsInst) :
    ∀ part∈(extSplitRun k child mem key v).parts,∀ base Q,encodeTreePart base part=some Q →
      Nonempty (ByteInput (traceInstance baseI (extSplitRun k child mem key v) v) Q) := by
  have hp := commonPrefix_right k key
  have ho := commonPrefix_left k key
  have hl := congrArg List.length hp
  simp only [List.length_append] at hl
  have hn : (commonPrefix k key).length≤key.length := by omega
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
    have hc : (commonPrefix k key).length+1≤k.length := by
      have h := congrArg List.length hd
      simp only [List.length_drop,List.length_cons] at h
      omega
    have hx := getD_of_drop_cons k _ x xs hd
    have hm := drop_successor_of_cons k _ x xs hd
    cases xs with
    | nil =>
      cases hd' : key.drop (commonPrefix k key).length with
      | nil =>
        simp only [List.isEmpty_cons,List.isEmpty_nil,Bool.false_eq_true,ite_false,ite_true,List.nil_append,List.cons_append] 
        apply split_wrap_byteInput baseI _ key _ .ESl1 _ _ v hw hk hp (by rfl)
        have hb := splitInstance_bounds baseI (.ext k child mem) key .ESl1 _ v hw hk hn
        have hx' : (splitInstance baseI (.ext k child mem) key .ESl1 (commonPrefix k key).length v).x=x := hx
        intro part hpart base Q he
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hpart
        rcases hpart with rfl
        rw [←hx'] at he
        exact ⟨treeSpbChildValue_input _ base k child mem v _ Q he rfl hw rfl ⟨hb.1,hb.2.1⟩ hb.2.2⟩
      | cons y ys =>
        simp only [List.isEmpty_cons,List.isEmpty_nil,Bool.false_eq_true,ite_false,ite_true,List.nil_append,List.cons_append] 
        apply split_wrap_byteInput baseI _ key _ .ESn1 _ _ v hw hk hp (by rfl)
        have hb := splitInstance_bounds baseI (.ext k child mem) key .ESn1 _ v hw hk hn
        have hx' : (splitInstance baseI (.ext k child mem) key .ESn1 (commonPrefix k key).length v).x=x := hx
        have hf := (drop_successor_of_cons key _ y ys hd').symm.trans
          (splitInstance_fresh baseI (.ext k child mem) key .ESn1 _ v hk)
        have hy := splitInstance_next baseI (.ext k child mem) key .ESn1 _ v hk y ys hd'
        have hxy := commonPrefix_diverge k key hd hd'
        intro part hpart base Q he
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hpart
        rcases hpart with rfl|rfl
        · rw [hf] at he
          exact ⟨treeNlf_byteInput _ base _ v Q he hw rfl ⟨hb.1,hb.2.1⟩ hb.2.2⟩
        · rw [←hx',hy] at he
          exact ⟨treeSpbChildNone_input _ base k child _ mem _ Q he rfl hw rfl
            (by simpa only [hx',←hy] using hxy) ⟨hb.1,hb.2.1⟩ hb.2.2⟩
    | cons z zs =>
      cases hd' : key.drop (commonPrefix k key).length with
      | nil =>
        simp only [List.isEmpty_cons,List.isEmpty_nil,Bool.false_eq_true,ite_false,ite_true,List.nil_append,List.cons_append] 
        apply split_wrap_byteInput baseI _ key _ .ESl0 _ _ v hw hk hp (by rfl)
        have hb := splitInstance_bounds baseI (.ext k child mem) key .ESl0 _ v hw hk hn
        have hx' : (splitInstance baseI (.ext k child mem) key .ESl0 (commonPrefix k key).length v).x=x := hx
        intro part hpart base Q he
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hpart
        rcases hpart with rfl|rfl
        · rw [←hm] at he
          exact ⟨treeMve_byteInput _ base k child mem Q he hw hc ⟨hb.1,hb.2.1⟩ hb.2.2⟩
        · rw [←hx'] at he
          exact ⟨treeSpbFreshSome_input _ base _ _ v _ Q he (Or.inr rfl) hw rfl rfl ⟨hb.1,hb.2.1⟩ hb.2.2⟩
      | cons y ys =>
        simp only [List.isEmpty_cons,List.isEmpty_nil,Bool.false_eq_true,ite_false,ite_true,List.nil_append,List.cons_append] 
        apply split_wrap_byteInput baseI _ key _ .ESn0 _ _ v hw hk hp (by rfl)
        have hb := splitInstance_bounds baseI (.ext k child mem) key .ESn0 _ v hw hk hn
        have hx' : (splitInstance baseI (.ext k child mem) key .ESn0 (commonPrefix k key).length v).x=x := hx
        have hf := (drop_successor_of_cons key _ y ys hd').symm.trans
          (splitInstance_fresh baseI (.ext k child mem) key .ESn0 _ v hk)
        have hy := splitInstance_next baseI (.ext k child mem) key .ESn0 _ v hk y ys hd'
        have hxy := commonPrefix_diverge k key hd hd'
        intro part hpart base Q he
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hpart
        rcases hpart with rfl|rfl|rfl
        · rw [←hm] at he
          exact ⟨treeMve_byteInput _ base k child mem Q he hw hc ⟨hb.1,hb.2.1⟩ hb.2.2⟩
        · rw [hf] at he
          exact ⟨treeNlf_byteInput _ base _ v Q he hw rfl ⟨hb.1,hb.2.1⟩ hb.2.2⟩
        · rw [←hx',hy] at he
          exact ⟨treeSpbFreshNone_input _ base _ _ _ _ Q he (Or.inr rfl) hw rfl rfl
            (by simpa only [hx',←hy] using hxy) ⟨hb.1,hb.2.1⟩ hb.2.2⟩
end ZkFormal.NearV3.Render.UpsGen
