import ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near

theorem slot_canon (u : Inputs) (s : NSlot3) (h : ∀x∈s.raw,x<Algebra.P) :
    ∀x∈(slot u s).raw,x<Algebra.P := by
  cases s with
  | ref l hh => exact h
  | val l i n pre po w =>
    cases hv : u.value i with
    | none => simpa [slot,hv] using h
    | some b =>
      intro x hx
      simp only [slot,hv,NSlot3.raw,List.mem_append] at hx
      rcases hx with ((hx|hx)|hx)|hx
      · exact h x (by simp only [NSlot3.raw,List.mem_append]; grind)
      · exact h x (by simp only [NSlot3.raw,List.mem_append]; grind)
      · exact h x (by simp only [NSlot3.raw,List.mem_append]; grind)
      · have hb := digest_byte b x hx
        have hp : 256<Algebra.P := by decide
        omega

theorem kid_canon (u : Inputs) (k : NKid) (h : ∀x∈k.raw,x<Algebra.P) :
    ∀x∈(kid u k).raw,x<Algebra.P := by
  cases k with
  | none => exact h
  | hash hh => exact h
  | node c l r pre po =>
    intro x hx
    simp only [kid,NKid.raw,List.mem_append] at hx
    rcases hx with (hx|hx)|hx
    · exact h x (by simp only [NKid.raw,List.mem_append]; grind)
    · exact h x (by simp only [NKid.raw,List.mem_append]; grind)
    · have hb := digest_byte (u.child c) x hx
      have hp : 256<Algebra.P := by decide
      omega

theorem node_canon (u : Inputs) (v : NodeV3) (h : ∀x∈v.raw,x<Algebra.P) :
    ∀x∈(node u v).raw,x<Algebra.P := by
  cases v with
  | leaf k s m =>
    intro x hx
    simp only [node,NodeV3.raw,List.mem_append] at hx
    rcases hx with (hx|hx)|hx
    · exact h x (by simp [NodeV3.raw,hx])
    · exact slot_canon u s (fun y hy => h y (by simp [NodeV3.raw,hy])) x hx
    · exact h x (by simp [NodeV3.raw,hx])
  | ext k c m =>
    intro x hx
    simp only [node,NodeV3.raw,List.mem_append] at hx
    rcases hx with (hx|hx)|hx
    · exact h x (by simp [NodeV3.raw,hx])
    · exact kid_canon u c (fun y hy => h y (by simp [NodeV3.raw,hy])) x hx
    · exact h x (by simp [NodeV3.raw,hx])
  | branch v cs m =>
    intro x hx
    simp only [node,NodeV3.raw,List.mem_append] at hx
    rcases hx with (hx|hx)|hx
    · cases v with
      | none => simp at hx
      | some s => exact slot_canon u s (fun y hy => h y (by simp [NodeV3.raw,hy])) x hx
    · obtain ⟨c,hc,hx⟩ := List.mem_flatMap.mp hx
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      exact kid_canon u c' (fun y hy => h y (by
        simp only [NodeV3.raw,List.mem_append]
        exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨c',hc',hy⟩)))) x hx
    · exact h x (by simp [NodeV3.raw,hx])

theorem record_res (u : Inputs) (n : Nat) (s : NodeS3) :
    (record u s).resOk n ↔ s.resOk n := by
  cases hv : s.v with
  | leaf k v m => simp [record,node,NodeS3.resOk,hv]
  | branch v cs m => simp [record,node,NodeS3.resOk,hv]
  | ext k c m => cases k <;> cases c <;> simp [record,node,kid,NodeS3.resOk,hv]

theorem record_edges (u : Inputs) (n : Nat) (s : NodeS3) :
    edgesOf3 n (record u s)=edgesOf3 n s := by
  cases hv : s.v with
  | leaf k v m =>
    cases v with
    | ref l hh => simp [record,node,slot,edgesOf3,hv]
    | val l i len pre po w =>
      cases hu : u.value i <;> simp [record,node,slot,edgesOf3,hv,hu]
  | ext k c m => cases c <;> cases hk : k.getLast? <;> simp [record,node,kid,edgesOf3,hv,hk]
  | branch v cs m =>
    have hc : ((cs.map (kid u)).zip (List.range (cs.map (kid u)).length)).filterMap
        (fun | (.node _ _ cr _ _,j) => some [n,0,j,cr,0,EK_DOWN] | _ => none)=
      (cs.zip (List.range cs.length)).filterMap
        (fun | (.node _ _ cr _ _,j) => some [n,0,j,cr,0,EK_DOWN] | _ => none) := by
      simp only [List.length_map,List.zip_map_left,List.filterMap_map]
      congr 1
      funext p
      rcases p with ⟨c,j⟩
      cases c <;> rfl
    cases v with
    | none => simp [record,node,edgesOf3,hv]; grind
    | some v =>
      cases v with
      | ref l hh => simp [record,node,slot,edgesOf3,hv]; grind
      | val l i len pre po w =>
        cases hu : u.value i <;> simp [record,node,slot,edgesOf3,hv,hu] <;> grind

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
