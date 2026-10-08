import ZkFormal.NearV3.Candidates.PostNodeLocal

namespace ZkFormal.NearV3.Candidates.PostNodeBytes
open ZkFormal.Near Rcpt.Candidates.NodePostUpdate

theorem slot_bytes (u : Inputs) (s : NSlot3) (h : ∀x∈s.bytes true,x<256) :
    ∀x∈(slot u s).bytes true,x<256 := by
  cases s with
  | ref l hh => exact h
  | val l i n pre po w =>
    cases hv : u.value i with
    | none => simpa [slot,hv] using h
    | some b =>
      intro x hx
      simp only [slot,hv,NSlot3.bytes,ite_true,List.mem_append] at hx
      rcases hx with hx|hx
      · exact h x (by simp [NSlot3.bytes,hx])
      · exact digest_byte b x hx

theorem kid_bytes (u : Inputs) (k : NKid) (h : ∀x∈k.bytes true,x<256) :
    ∀x∈(kid u k).bytes true,x<256 := by
  cases k with
  | none => exact h
  | hash hh => exact h
  | node c l r pre po => exact digest_byte (u.child c)

theorem kids_bytes (u : Inputs) (cs : List NKid)
    (h : ∀x∈cs.flatMap (NKid.bytes true),x<256) :
    ∀x∈(cs.map (kid u)).flatMap (NKid.bytes true),x<256 := by
  intro x hx
  obtain ⟨c,hc,hx⟩:=List.mem_flatMap.mp hx
  obtain ⟨d,hd,he⟩:=List.mem_map.mp hc
  subst c
  exact kid_bytes u d (fun y hy=>h y (List.mem_flatMap.mpr ⟨d,hd,hy⟩)) x hx

/-- Digest replacement preserves byte validity, not merely field canonicality. -/
theorem node_bytes (u : Inputs) (v : NodeV3) (h : ∀x∈v.ser true,x<256) :
    ∀x∈(node u v).ser true,x<256 := by
  cases v with
  | leaf k s m =>
    intro x hx
    simp only [node,NodeV3.ser,List.mem_append] at hx
    rcases hx with (((hx|hx)|hx)|hx)|hx
    · exact h x (by simp only [NodeV3.ser,List.mem_append]; grind)
    · exact h x (by simp only [NodeV3.ser,List.mem_append]; grind)
    · exact h x (by simp only [NodeV3.ser,List.mem_append]; grind)
    · exact slot_bytes u s (fun y hy=>h y (by simp [NodeV3.ser,hy])) x hx
    · exact h x (by simp only [NodeV3.ser,List.mem_append]; grind)
  | ext k c m =>
    intro x hx
    simp only [node,NodeV3.ser,List.mem_append] at hx
    rcases hx with (((hx|hx)|hx)|hx)|hx
    · exact h x (by simp only [NodeV3.ser,List.mem_append]; grind)
    · exact h x (by simp only [NodeV3.ser,List.mem_append]; grind)
    · exact h x (by simp only [NodeV3.ser,List.mem_append]; grind)
    · exact kid_bytes u c (fun y hy=>h y (by simp [NodeV3.ser,hy])) x hx
    · exact h x (by simp only [NodeV3.ser,List.mem_append]; grind)
  | branch v cs m =>
    have hk:=kids_bytes u cs (fun y hy=>h y (by simp [NodeV3.ser,hy]))
    cases v with
    | none =>
      intro x hx
      simp only [node,NodeV3.ser,Option.map_none,bitmap,List.mem_append] at hx
      rcases hx with ((hx|hx)|hx)|hx
      · exact h x (by simp only [NodeV3.ser,List.mem_append]; grind)
      · exact h x (by simp only [NodeV3.ser,List.mem_append]; grind)
      · exact hk x hx
      · exact h x (by simp only [NodeV3.ser,List.mem_append]; grind)
    | some s =>
      intro x hx
      simp only [node,NodeV3.ser,Option.map_some,bitmap,List.mem_append] at hx
      rcases hx with (((hx|hx)|hx)|hx)|hx
      · exact h x (by simp only [NodeV3.ser,List.mem_append]; grind)
      · exact slot_bytes u s (fun y hy=>h y (by simp [NodeV3.ser,hy])) x hx
      · exact h x (by simp only [NodeV3.ser,List.mem_append]; grind)
      · exact hk x hx
      · exact h x (by simp only [NodeV3.ser,List.mem_append]; grind)

end ZkFormal.NearV3.Candidates.PostNodeBytes
