import ZkFormal.NearV3.Render.Ups.TerminalDescent

namespace ZkFormal.NearV3.Render.UpsGen

private theorem filter_drop_length_le {α : Type} (p : α→Bool) : ∀ (xs : List α) (k : Nat),
    ((xs.drop k).filter p).length≤(xs.filter p).length
  | [], k => by simp
  | x::xs, 0 => by simp
  | x::xs, k+1 => by
    have ih := filter_drop_length_le p xs k
    cases h : p x <;> simp [h] at ih ⊢ <;> omega

/-- A selected element's index in the reversed filtered list is the number of
selected elements at and above it, minus one. -/
theorem reverse_filter_position {α β : Type} (p : α→Bool) (f : α→β) (d : β) :
    ∀ (xs : List α) (k : Nat) (x : α), xs[k]?=some x → p x=true →
      (((xs.filter p).reverse).map f).getD (((xs.drop k).filter p).length-1) d=f x
  | [], _, _, h, _ => by simp at h
  | x::xs, 0, y, h, hy => by
    simp at h; subst y
    simp [hy,List.getD_eq_getElem?_getD,List.getElem?_append]
  | x::xs, k+1, y, h, hy => by
    have ih := reverse_filter_position p f d xs k y h hy
    have hb := filter_drop_length_le p xs k
    have hn : 0<(xs.filter p).length := by
      have hm : y∈xs.filter p := List.mem_filter.mpr ⟨List.mem_of_getElem? h,hy⟩
      exact List.length_pos_iff.mpr (by intro he; simp [he] at hm)
    have hi : ((xs.drop k).filter p).length-1<(xs.filter p).length := by omega
    cases hx : p x
    · simpa [hx] using ih
    · simpa [hx,List.getD_eq_getElem?_getD,List.getElem?_append,hi] using ih
end ZkFormal.NearV3.Render.UpsGen
