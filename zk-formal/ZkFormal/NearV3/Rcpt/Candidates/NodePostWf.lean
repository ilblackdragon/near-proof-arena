import ZkFormal.NearV3.Rcpt.Candidates.NodePostFacts

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near

private theorem kid_getD (u : Inputs) (cs : List NKid) (j : Nat) :
    (cs.map (kid u)).getD j .none=kid u (cs.getD j .none) := by
  induction cs generalizing j with
  | nil => simp [kid]
  | cons c cs ih => cases j with
    | zero => rfl
    | succ j => exact ih j

private theorem kid_original (u : Inputs) (k : NKid) {c l r : Nat} {pre po : List Nat}
    (h : kid u k=.node c l r pre po) : ∃old,k=.node c l r pre old := by
  cases k <;> simp_all [kid]

theorem node_kidCid (u : Inputs) (v : NodeV3) (ids : List Nat) (h : v.kidCidOk ids) :
    (node u v).kidCidOk ids := by
  cases v with
  | leaf k s m => trivial
  | ext k c m =>
    intro cid l r pre po he
    obtain ⟨old,ho⟩ := kid_original u c he
    exact h cid l r pre old ho
  | branch v cs m =>
    intro j c l r pre po he
    rw [kid_getD] at he
    obtain ⟨old,ho⟩ := kid_original u (cs.getD j .none) he
    have hh := h j c l r pre old ho
    simpa only [←List.map_take,List.filter_map,List.length_map,Function.comp_def,
      kid_present,Option.isSome_map] using hh

theorem records_wf (u : Inputs) (ss : List NodeS3) (h : NodeWf3 ss) : NodeWf3 (records u ss) := by
  unfold records
  constructor
  · intro s hs
    obtain ⟨s,hmem,rfl⟩ := List.mem_map.mp hs
    exact node_wf u s.v (h.wf s hmem)
  · intro s hs
    obtain ⟨s,hmem,rfl⟩ := List.mem_map.mp hs
    exact h.depth s hmem
  · intro n hn
    have hn' : n<ss.length := by simpa [records] using hn
    change ((ss.map (record u))[n]).resOk n
    rw [List.getElem_map]
    exact (record_res u n ss[n]).mpr (h.res n hn')
  · intro n hn
    have hn' : n<ss.length := by simpa [records] using hn
    change ((ss.map (record u))[n]).uses.length=(edgesOf3 n ((ss.map (record u))[n])).length
    rw [List.getElem_map,record_edges]
    exact h.uses n hn'
  · intro s hs
    obtain ⟨s,hmem,rfl⟩ := List.mem_map.mp hs
    exact h.small s hmem
  · intro s hs
    obtain ⟨s,hmem,rfl⟩ := List.mem_map.mp hs
    exact node_canon u s.v (h.canon s hmem)
  · simpa [records] using h.count
  · simpa [records,record,List.map_map,Function.comp_def,node_pre] using h.rows
  · intro s hs
    obtain ⟨s,hmem,rfl⟩ := List.mem_map.mp hs
    simpa [record,node_pre] using h.upbLen s hmem
  · intro s hs
    obtain ⟨s,hmem,rfl⟩ := List.mem_map.mp hs
    exact h.upbSmall s hmem
  · intro s hs
    obtain ⟨s,hmem,rfl⟩ := List.mem_map.mp hs
    exact node_kidCid u s.v s.ucid (h.kidCid s hmem)

/-- Final digest updates impose no new byte-length correspondence premise. -/
theorem records_pre_lengths (u : Inputs) (ss : List NodeS3) :
    (records u ss).map (fun s => (s.v.ser false).length)=
      ss.map (fun s => (s.v.ser false).length) := by
  simp [records,record,List.map_map,Function.comp_def,node_pre]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
