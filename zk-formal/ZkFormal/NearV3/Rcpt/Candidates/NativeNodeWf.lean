import ZkFormal.NearV3.Rcpt.Candidates.NodePairedWf

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

theorem native_viewSlot_wf (vid : Nat) (s : Slot) (h : slotOk s=true)
    (hlen : ∀b,s=.val b → b.length<16777216) : (viewSlot vid s).wf := by
  cases s with
  | ref n hh =>
    simp only [slotOk,Bool.and_eq_true,beq_iff_eq] at h
    simpa [viewSlot,NSlot3.wf] using h.2
  | val b =>
    have hb := hlen b rfl
    change (u32Bytes b.length).length=4 ∧ _ ∧ _ ∧ _ ∧
      (u32Bytes b.length).getD 3 0=0 ∧ _
    refine ⟨u32Bytes_length _,?_,?_,?_,u32Bytes_top_zero hb,?_⟩
    · simp [viewSlot]
    · simp [viewSlot]
    · intro _;rfl
    · intro _;exact u32Bytes_value (by omega)

theorem native_viewKid_wf (nid : Nat) (t : PTrie) (h : t.wf=true) : (viewKid nid t).wf := by
  have hh := hashOf_len_of_wf t h
  unfold viewKid
  split <;> simp [NKid.wf,hh]

theorem native_viewKids_wf : ∀(nid : Nat)(cs : Kids)(n : Nat),Kids.wf cs n=true →
    (viewKids nid cs).length=n ∧ ∀c∈viewKids nid cs,c.wf
  | _,.nil,n,h => by simp [Kids.wf] at h;subst n;simp [viewKids]
  | nid,.none cs,n,h => by
    simp only [Kids.wf,Bool.and_eq_true,bne_iff_ne,ne_eq] at h
    have ht := native_viewKids_wf nid cs (n-1) h.2
    constructor
    · simp only [viewKids,List.length_cons,ht.1];omega
    · intro c hc
      simp only [viewKids,List.mem_cons] at hc
      rcases hc with rfl|hc
      · trivial
      · exact ht.2 c hc
  | nid,.some c cs,n,h => by
    simp only [Kids.wf,Bool.and_eq_true,bne_iff_ne,ne_eq] at h
    have ht := native_viewKids_wf (nid+tsize c) cs (n-1) h.2
    constructor
    · simp only [viewKids,List.length_cons,ht.1];omega
    · intro k hk
      simp only [viewKids,List.mem_cons] at hk
      rcases hk with rfl|hk
      · exact native_viewKid_wf nid c h.1.2
      · exact ht.2 k hk

theorem native_viewNode_wf (nid vid : Nat) (t : PTrie) (hw : t.wf=true)
    (hn : isNode t=true) (hv : ∀b∈valsOf t,b.length<16777216) : (viewNode nid vid t).wf := by
  cases t with
  | hash h => simp [isNode] at hn
  | leaf k s m =>
    simp only [PTrie.wf,Bool.and_eq_true] at hw
    refine ⟨?_,native_viewSlot_wf vid s hw.1.1.2 ?_,by simp [viewNode]⟩
    · simpa [nibblesOk,List.all_eq_true] using hw.1.1.1
    · intro b hb;subst s;exact hv b (by simp [valsOf_leaf,slotVal])
  | ext k c m =>
    simp only [PTrie.wf,Bool.and_eq_true] at hw
    refine ⟨?_,?_,native_viewKid_wf (nid+1) c hw.1.1.2,by simp [viewNode]⟩
    · simpa [nibblesOk,List.all_eq_true] using hw.1.1.1
    · unfold viewKid;split <;> simp
  | branch v cs m =>
    simp only [PTrie.wf,Bool.and_eq_true] at hw
    have hc := native_viewKids_wf (nid+1) cs 16 hw.1.2
    refine ⟨hc.1,?_,hc.2,by simp [viewNode]⟩
    intro s hs
    cases vv : v with
    | none => simp [viewNode,vv] at hs
    | some value =>
      have he : viewSlot vid value=s := by simpa [viewNode,vv] using hs
      rw [←he]
      apply native_viewSlot_wf vid value
      · simpa [vv] using hw.1.1
      · intro b hb;subst value
        exact hv b (by simp [valsOf_branch,vv,optSlotVal,slotVal])

/-- The unchanged native unfolded-byte cap supplies the slot-width premise for
all occurrence views, including shared subtrees unfolded more than once. -/
theorem native_forest_node_wf (ts : List PTrie) (hw : ∀t∈ts,t.wf=true)
    (hb : Assembly.preBytes ts≤2000000) (nid vid : Nat) (o : PTrie)
    (ho : o∈ts.flatMap occs) : (viewNode nid vid o).wf := by
  obtain ⟨t,ht,ho⟩ := List.mem_flatMap.mp ho
  have hn := occs_isNode t o ho
  have howf := occs_wf t (hw t ht) o ho
  apply native_viewNode_wf nid vid o howf hn
  intro b hval
  obtain ⟨c,hc,hbval⟩ := List.mem_flatMap.mp hval
  have hroot := ownVals_sub (occs_trans t o ho c hc) hbval
  have hforest : b∈Assembly.forestBytes ts := List.mem_flatMap.mpr ⟨t,ht,hroot⟩
  have hsum := Link3.le_sum_mem (List.mem_map.mpr ⟨b,hforest,rfl⟩ :
    b.length∈(Assembly.forestBytes ts).map List.length)
  have hp := forest_occurrence_bytes ts hw
  simp only [Assembly.forestStoreViews,seedValues_bytes_length] at hp
  omega

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
