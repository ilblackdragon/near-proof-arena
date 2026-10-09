import ZkFormal.NearV3.Render.Ups.SplitInstance
import ZkFormal.NearV3.Render.Ups.TreeSplitInput

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

theorem split_wrap_byteInput (baseI : UpsInst) (source : PTrie) (key p : List Nat)
    (cs : UCase) (result : PTrie) (parts : List TreePart) (v : Bytes)
    (hw : source.wf=true) (hk : FixedSuffix key) (hp : key=p++key.drop p.length)
    (hr : isNode result=true)
    (hi : ∀ part∈parts,∀ base Q,encodeTreePart base part=some Q →
      Nonempty (ByteInput (splitInstance baseI source key cs p.length v) Q)) :
    ∀ part∈(wrapRun source p (terminalRun source key cs p.length result parts)).parts,
      ∀ base Q,encodeTreePart base part=some Q →
      Nonempty (ByteInput (traceInstance baseI
        (wrapRun source p (terminalRun source key cs p.length result parts)) v) Q) := by
  have hl := congrArg List.length hp
  simp only [List.length_append] at hl
  have hle : p.length≤key.length := by omega
  have ht : key.take p.length=p := by conv => lhs; rw [hp]; simp
  have hb := splitInstance_bounds baseI source key cs p.length v hw hk hle
  rw [traceInstance_wrapRun]
  apply wrapRun_byteInput _ source p _ hw hr ⟨hb.1,hb.2.1⟩ hb.2.2
  · exact ht.symm.trans (splitInstance_prefix baseI source key cs p.length v hk)
  · intro hn
    exact hk.wrap hle (List.length_pos_iff.mpr hn)
  · exact hi

/-- Actual leaf split dispatch, including arbitrary unmatched source suffixes. -/
theorem leafSplitRun_byteInput (k : List Nat) (old : Slot) (mem : Nat) (key : List Nat)
    (v : Bytes) (hw : (PTrie.leaf k old mem).wf=true) (hk : FixedSuffix key)
    (hne : k≠key) (baseI : UpsInst) :
    ∀ part∈(leafSplitRun k old mem key v).parts,∀ base Q,encodeTreePart base part=some Q →
      Nonempty (ByteInput (traceInstance baseI (leafSplitRun k old mem key v) v) Q) := by
  have hp := commonPrefix_right k key
  have ho := commonPrefix_left k key
  have hl := congrArg List.length hp
  simp only [List.length_append] at hl
  have hn : (commonPrefix k key).length≤key.length := by omega
  unfold leafSplitRun
  dsimp only
  cases hd : k.drop (commonPrefix k key).length with
  | nil =>
    cases hd' : key.drop (commonPrefix k key).length with
    | nil => simp only [hd,List.append_nil] at ho; simp only [hd',List.append_nil] at hp; exact (hne (ho.trans hp.symm)).elim
    | cons y ys =>
      apply split_wrap_byteInput baseI _ key _ .LSa _ _ v hw hk hp (by rfl)
      have hb := splitInstance_bounds baseI (.leaf k old mem) key .LSa _ v hw hk hn
      have hf := (drop_successor_of_cons key _ y ys hd').symm.trans
        (splitInstance_fresh baseI (.leaf k old mem) key .LSa _ v hk)
      have hy := splitInstance_next baseI (.leaf k old mem) key .LSa _ v hk y ys hd'
      intro part hpart base Q he
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hpart
      rcases hpart with rfl|rfl
      · rw [hf] at he
        exact ⟨treeNlf_byteInput _ base _ v Q he hw rfl ⟨hb.1,hb.2.1⟩ hb.2.2⟩
      · rw [hy] at he
        exact ⟨treeSpbValue_input _ base k old mem _ _ Q he rfl hw rfl ⟨hb.1,hb.2.1⟩ hb.2.2⟩
  | cons x xs =>
    have hc : (commonPrefix k key).length+1≤k.length := by
      have h := congrArg List.length hd
      simp only [List.length_drop,List.length_cons] at h
      omega
    have hx := getD_of_drop_cons k _ x xs hd
    have hm := drop_successor_of_cons k _ x xs hd
    cases hd' : key.drop (commonPrefix k key).length with
    | nil =>
      apply split_wrap_byteInput baseI _ key _ .LSb _ _ v hw hk hp (by rfl)
      have hb := splitInstance_bounds baseI (.leaf k old mem) key .LSb _ v hw hk hn
      have hx' : (splitInstance baseI (.leaf k old mem) key .LSb (commonPrefix k key).length v).x=x := hx
      intro part hpart base Q he
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hpart
      rcases hpart with rfl|rfl
      · rw [←hm] at he
        exact ⟨treeMvl_byteInput _ base k old mem Q he hw hc ⟨hb.1,hb.2.1⟩ hb.2.2⟩
      · rw [←hx'] at he
        exact ⟨treeSpbFreshSome_input _ base _ _ v _ Q he (Or.inl rfl) hw rfl rfl ⟨hb.1,hb.2.1⟩ hb.2.2⟩
    | cons y ys =>
      apply split_wrap_byteInput baseI _ key _ .LSc _ _ v hw hk hp (by rfl)
      have hb := splitInstance_bounds baseI (.leaf k old mem) key .LSc _ v hw hk hn
      have hx' : (splitInstance baseI (.leaf k old mem) key .LSc (commonPrefix k key).length v).x=x := hx
      have hf := (drop_successor_of_cons key _ y ys hd').symm.trans
        (splitInstance_fresh baseI (.leaf k old mem) key .LSc _ v hk)
      have hy := splitInstance_next baseI (.leaf k old mem) key .LSc _ v hk y ys hd'
      have hxy := commonPrefix_diverge k key hd hd'
      intro part hpart base Q he
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hpart
      rcases hpart with rfl|rfl|rfl
      · rw [←hm] at he
        exact ⟨treeMvl_byteInput _ base k old mem Q he hw hc ⟨hb.1,hb.2.1⟩ hb.2.2⟩
      · rw [hf] at he
        exact ⟨treeNlf_byteInput _ base _ v Q he hw rfl ⟨hb.1,hb.2.1⟩ hb.2.2⟩
      · rw [←hx',hy] at he
        exact ⟨treeSpbFreshNone_input _ base _ _ _ _ Q he (Or.inl rfl) hw rfl rfl
          (by simpa only [hx',←hy] using hxy) ⟨hb.1,hb.2.1⟩ hb.2.2⟩
end ZkFormal.NearV3.Render.UpsGen
