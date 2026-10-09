import ZkFormal.NearV3.Qv.Extract.ByteLink

namespace ZkFormal.NearV3.Qv.Extract

/-- Every other stream which emits a position also emits position zero for
that ID. Unique demanded positions therefore give a nonempty selected stream
exclusive ownership of its ID. This is a multiset argument, not a set balance. -/
theorem stream_other_id_ne {α ι π : Type} [DecidableEq ι] [OfNat π 0]
    (key : α → ι × π) (id : ι) (selected others demand : List α)
    (hbalance : (selected++others).Perm demand)
    (hunique : (demand.map key).Nodup)
    (hstart : ∃ x∈selected, key x=(id,0))
    (hclosed : ∀ x∈others, ∃ y∈others, key y=((key x).1,0)) :
    ∀ x∈others, (key x).1≠id := by
  have hn := (hbalance.map key).symm.nodup hunique
  rw [List.map_append,List.nodup_append] at hn
  obtain ⟨z,hz,hzk⟩ := hstart
  have hzmem : (id,0)∈selected.map key := List.mem_map.mpr ⟨z,hz,hzk⟩
  intro x hx he
  obtain ⟨y,hy,hyk⟩ := hclosed x hx
  rw [he] at hyk
  have hymem : (id,0)∈others.map key := List.mem_map.mpr ⟨y,hy,hyk⟩
  exact hn.2.2 _ hzmem _ hymem rfl

/-- Exact global balance isolates the complete demanded stream for an ID;
a matching prefix alone cannot satisfy this theorem's hypotheses. -/
theorem stream_isolate {α ι π : Type} [DecidableEq ι] [OfNat π 0]
    (key : α → ι × π) (id : ι) (selected others demand : List α)
    (hbalance : (selected++others).Perm demand)
    (hunique : (demand.map key).Nodup)
    (hstart : ∃ x∈selected, key x=(id,0))
    (hselected : ∀ x∈selected, (key x).1=id)
    (hclosed : ∀ x∈others, ∃ y∈others, key y=((key x).1,0)) :
    selected.Perm (demand.filter (fun x => decide ((key x).1=id))) := by
  have hothers := stream_other_id_ne key id selected others demand hbalance hunique hstart hclosed
  have hfilter := hbalance.filter (fun x => decide ((key x).1=id))
  have hs : selected.filter (fun x => decide ((key x).1=id))=selected := by
    apply List.filter_eq_self.mpr
    intro x hx
    simp [hselected x hx]
  have ho : others.filter (fun x => decide ((key x).1=id))=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    simp [hothers x hx]
  simpa only [List.filter_append,hs,ho,List.append_nil] using hfilter

end ZkFormal.NearV3.Qv.Extract
