import ZkFormal.NearV3.Assembly.QueueCounterClass

namespace ZkFormal.NearV3.Assembly

/-- Stable grouping by a complete, duplicate-free provider-key list preserves
 every use, including repeated identical uses. -/
theorem provider_partition {α β γ : Type} [DecidableEq α] [DecidableEq β]
    (xs : List α) (ps : List γ) (key : α → β) (pk : γ → β)
    (hn : (ps.map pk).Nodup) (hc : ∀ x ∈ xs, key x ∈ ps.map pk) :
    xs.Perm (ps.flatMap (fun p => xs.filter (fun x => key x == pk p))) := by
  apply List.perm_iff_count.mpr
  intro a
  have hcount : ∀ qs : List γ,
      List.count a (qs.flatMap (fun p => xs.filter (fun x => key x == pk p))) =
      (qs.countP (fun p => key a == pk p))*List.count a xs := by
    intro qs
    induction qs with
    | nil => simp
    | cons p qs ih =>
      simp only [List.flatMap_cons,List.count_append,List.countP_cons]
      by_cases he : key a=pk p
      · rw [List.count_filter (by simpa using he),ih]
        simp [he,Nat.add_mul,Nat.add_comm]
      · have hz : List.count a (xs.filter (fun x => key x == pk p))=0 := by
          apply List.count_eq_zero_of_not_mem
          simp [he]
        simp [hz,ih,he]
  rw [hcount]
  by_cases ha : a ∈ xs
  · have hp : ps.countP (fun p => key a == pk p)=1 := by
      have h := hn.count_of_mem (hc a ha)
      simp only [List.count,List.countP_map,Function.comp_def] at h
      have he : ps.countP (fun p => key a == pk p)=ps.countP (fun p => pk p == key a) := by
        apply List.countP_congr
        intro p hp
        simp only [beq_iff_eq]
        exact eq_comm
      exact he.trans h
    rw [hp,Nat.one_mul]
  · rw [List.count_eq_zero_of_not_mem ha,Nat.mul_zero]

theorem nodup_key_eq {α β : Type} (xs : List α) (key : α → β)
    (hn : (xs.map key).Nodup) {a b : α} (ha : a ∈ xs) (hb : b ∈ xs)
    (he : key a=key b) : a=b := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.map_cons,List.nodup_cons] at hn
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · rfl
      · exact False.elim (hn.1 (List.mem_map.mpr ⟨b,hb,he.symm⟩))
    · rcases hb with rfl | hb
      · exact False.elim (hn.1 (List.mem_map.mpr ⟨a,ha,he⟩))
      · exact ih hn.2 ha hb

end ZkFormal.NearV3.Assembly
