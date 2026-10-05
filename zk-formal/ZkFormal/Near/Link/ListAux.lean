import ZkFormal.Near.Link.Bus

/-!
# ZkFormal.Near.Link.ListAux — list lemmas used by the linking proofs
-/

namespace ZkFormal.Near

namespace Link

theorem nodup_map_of_inj_on {α β : Type} {f : α → β} {l : List α}
    (hf : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) (h : l.Nodup) : (l.map f).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  rw [List.nodup_iff_pairwise_ne] at h
  exact h.imp_of_mem (fun ha hb hne he => hne (hf _ ha _ hb he))

theorem nodup_of_map {α β : Type} {f : α → β} {l : List α} (h : (l.map f).Nodup) : l.Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at h
  rw [List.nodup_iff_pairwise_ne]
  exact h.imp (fun {a b} hne (he : a = b) => hne (he ▸ rfl))

theorem mem_zip_range {α : Type} {l : List α} {a : α} {n : Nat} :
    (a, n) ∈ l.zip (List.range l.length) ↔ ∃ h : n < l.length, l[n] = a := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, he⟩
    simp only [List.length_zip, List.length_range, Nat.min_self] at hi
    rw [List.getElem_zip] at he
    simp only [Prod.mk.injEq, List.getElem_range] at he
    obtain ⟨h1, rfl⟩ := he
    exact ⟨hi, h1⟩
  · rintro ⟨h, rfl⟩
    refine ⟨n, by simp [h], ?_⟩
    rw [List.getElem_zip]; simp

theorem map_snd_zip_range {α : Type} (l : List α) :
    (l.zip (List.range l.length)).map Prod.snd = List.range l.length :=
  List.map_snd_zip (by simp)

theorem filterMap_ite {α β : Type} (p : α → Bool) (g : α → β) (l : List α) :
    l.filterMap (fun x => if p x then some (g x) else none) = (l.filter p).map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filterMap_cons, List.filter_cons]
    cases p a <;> simp [ih]

theorem length_le_sum {α : Type} (f : α → Nat) : ∀ (l : List α), (∀ x ∈ l, 1 ≤ f x) →
    l.length ≤ (l.map f).sum
  | [], _ => by simp
  | a :: l, h => by
    have := length_le_sum f l (fun x hx => h x (by simp [hx]))
    have := h a (by simp)
    simp; omega

theorem le_sum_of_mem {α : Type} (f : α → Nat) : ∀ {l : List α} {a : α}, a ∈ l → f a ≤ (l.map f).sum
  | b :: l, a, h => by
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · have := le_sum_of_mem f h; simp; omega

/-- Nodup of the second components of a filtered `zip … range`. -/
theorem nodup_filter_zip_range {α : Type} (p : α × Nat → Bool) (l : List α) :
    (((l.zip (List.range l.length)).filter p).map Prod.snd).Nodup := by
  apply List.Nodup.sublist (List.Sublist.map _ List.filter_sublist)
  rw [map_snd_zip_range]; exact List.nodup_range

end Link

end ZkFormal.Near
