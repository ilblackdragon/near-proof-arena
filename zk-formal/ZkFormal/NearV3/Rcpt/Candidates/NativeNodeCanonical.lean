import ZkFormal.NearV3.Rcpt.Candidates.NativeForestIndices

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near ZkFormal.Algebra Render.UpsGen

theorem native_bytes_small (b : Bytes) : ∀x∈b.map UInt8.toNat,x<P := by
  intro x hx
  obtain ⟨a,_,rfl⟩:=List.mem_map.mp hx
  have h:=a.toNat_lt
  change a.toNat<2013265921
  omega

theorem native_slot_canonical (vid : Nat) (s : Slot) (hi : vid<P)
    (hl : ∀b,s=.val b → b.length<P) : ∀x∈(viewSlot vid s).raw,x<P := by
  cases s with
  | ref n h =>
    intro x hx
    simp only [viewSlot,NSlot3.raw,List.mem_append] at hx
    rcases hx with hx|hx
    · exact native_bytes_small _ x hx
    · exact native_bytes_small _ x hx
  | val b =>
    intro x hx
    simp only [viewSlot,NSlot3.raw,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with ((hx|(rfl|rfl))|hx)|hx
    · exact native_bytes_small _ x hx
    · exact hi
    · exact hl b rfl
    · exact native_bytes_small _ x hx
    · exact native_bytes_small _ x hx

theorem native_kid_canonical (nid : Nat) (t : PTrie)
    (hi : nid+tsize t≤P) (hl : (nodeEnc t).length<P) :
    ∀x∈(viewKid nid t).raw,x<P := by
  unfold viewKid
  split
  · rename_i hn
    have ht:=target_bound t nid hn
    intro x hx
    simp only [NKid.raw,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with ((rfl|rfl|rfl)|hx)|hx
    · omega
    · exact hl
    · omega
    · exact native_bytes_small _ x hx
    · exact native_bytes_small _ x hx
  · exact native_bytes_small _

theorem native_kids_canonical : ∀(cs : Kids)(nid : Nat),nid+ksize cs≤P →
    (∀t∈kOccs cs,(nodeEnc t).length<P) →
    ∀c∈viewKids nid cs,∀x∈c.raw,x<P
  | .nil,_,_,_,_,hc => by simp [viewKids] at hc
  | .none cs,n,hi,hl,c,hc => by
    simp only [viewKids,List.mem_cons] at hc
    rcases hc with rfl|hc
    · simp [NKid.raw]
    · exact native_kids_canonical cs n hi hl c hc
  | .some t cs,n,hi,hl,c,hc => by
    simp only [viewKids,List.mem_cons] at hc
    have hsz : ksize (.some t cs)=tsize t+ksize cs := by simp [ksize,tsize,kOccs]
    rcases hc with rfl|hc
    · by_cases hn : isNode t=true
      · apply native_kid_canonical n t (by omega)
        exact hl t (by simp only [kOccs,List.mem_append]; exact Or.inl (by cases t <;> simp_all [occs,isNode]))
      · simpa [viewKid,hn,NKid.raw] using native_bytes_small t.hashOf
    · exact native_kids_canonical cs (n+tsize t) (by omega)
        (fun t ht => hl t (by simp [kOccs,ht])) c hc

theorem native_node_canonical (nid vid : Nat) (t : PTrie)
    (hw : t.wf=true) (hi : nid+tsize t≤P) (hv : vid<P)
    (hl : ∀o∈occs t,(nodeEnc o).length<P)
    (hb : ∀b∈valsOf t,b.length<P) : ∀x∈(viewNode nid vid t).raw,x<P := by
  cases t with
  | hash hh => simpa [viewNode,NodeV3.raw] using native_bytes_small (u64 0)
  | leaf k sl m =>
    have hk : ∀x∈k,x<16 := by
      simp only [PTrie.wf,Bool.and_eq_true] at hw
      simpa [nibblesOk,List.all_eq_true] using hw.1.1.1
    have hs:=native_slot_canonical vid sl hv (by
      intro b h;subst sl;exact hb b (by simp [valsOf_leaf,slotVal]))
    intro x hx
    simp only [viewNode,NodeV3.raw,List.mem_append] at hx
    rcases hx with (hx|hx)|hx
    · have:=hk x hx;change x<2013265921;omega
    · exact hs x hx
    · exact native_bytes_small _ x hx
  | ext k c m =>
    have hk : ∀x∈k,x<16 := by
      simp only [PTrie.wf,Bool.and_eq_true] at hw
      simpa [nibblesOk,List.all_eq_true] using hw.1.1.1
    have hs : ∀x∈(viewKid (nid+1) c).raw,x<P := by
      by_cases hn : isNode c=true
      · apply native_kid_canonical (nid+1) c
        · simpa [tsize,occs,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hi
        · exact hl c (by cases c <;> simp_all [occs,isNode])
      · simpa [viewKid,hn,NKid.raw] using native_bytes_small c.hashOf
    intro x hx
    simp only [viewNode,NodeV3.raw,List.mem_append] at hx
    rcases hx with (hx|hx)|hx
    · have:=hk x hx;change x<2013265921;omega
    · exact hs x hx
    · exact native_bytes_small _ x hx
  | branch sv cs m =>
    have hc:=native_kids_canonical cs (nid+1) (by
      simpa [tsize,ksize,occs,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hi)
      (fun t ht => hl t (by simp [occs,ht]))
    intro x hx
    simp only [viewNode,NodeV3.raw,List.mem_append] at hx
    rcases hx with (hx|hx)|hx
    · cases sv with
      | none => simp at hx
      | some sl =>
        exact native_slot_canonical vid sl hv (by
          intro b h;subst sl;exact hb b (by simp [valsOf_branch,optSlotVal,slotVal])) x hx
    · obtain ⟨c,hc',hx⟩:=List.mem_flatMap.mp hx
      exact hc c hc' x hx
    · exact native_bytes_small _ x hx

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
