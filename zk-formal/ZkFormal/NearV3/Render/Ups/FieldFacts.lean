import ZkFormal.NearV3.Render.Ups.FieldInput

/-! Structural facts about the serializer's field cursor. -/
namespace ZkFormal.NearV3.Render.UpsGen

@[simp] theorem fieldsLen_nil : fieldsLen [] = 0 := rfl
@[simp] theorem fieldsLen_cons (s l : Nat) (sh : List (Nat × Nat)) :
    fieldsLen ((s,l) :: sh) = l + fieldsLen sh := rfl

/-- A live byte belongs to a nonempty field and has an in-range field index. -/
theorem fieldAt_bounds (sh : List (Nat × Nat)) (p : Nat) (hp : p < fieldsLen sh) :
    (fieldAt sh p).2.1 < (fieldAt sh p).2.2.1 ∧
      ((fieldAt sh p).1, (fieldAt sh p).2.2.1) ∈ sh := by
  induction sh generalizing p with
  | nil => simp at hp
  | cons f sh ih =>
    obtain ⟨s,l⟩ := f
    simp only [fieldsLen_cons] at hp
    by_cases h : p < l
    · simp [fieldAt, h]
    · have hi := ih (p - l) (by omega)
      simp only [fieldAt, h, ite_false]
      exact ⟨hi.1, List.mem_cons_of_mem _ hi.2⟩

/-- Within one field, the next byte preserves its state, length and window index. -/
theorem fieldAt_next_inside (sh : List (Nat × Nat)) (p : Nat)
    (hp : (fieldAt sh p).2.1 + 1 < (fieldAt sh p).2.2.1) :
    fieldAt sh (p + 1) = ((fieldAt sh p).1, (fieldAt sh p).2.1 + 1,
      (fieldAt sh p).2.2.1, (fieldAt sh p).2.2.2) := by
  induction sh generalizing p with
  | nil => simp [fieldAt] at hp
  | cons f sh ih =>
    obtain ⟨s,l⟩ := f
    by_cases h : p < l
    · simp only [fieldAt, h, ite_true] at hp ⊢
      rw [if_pos hp]
    · have h' : ¬ p + 1 < l := by omega
      simp only [fieldAt, h, h', ite_false] at hp ⊢
      rw [show p + 1 - l = (p - l) + 1 by omega, ih (p - l) hp]

/-- Positive fields begin at index zero. -/
theorem fieldAt_zero (sh : List (Nat × Nat)) (s l : Nat) (hl : 0 < l) :
    fieldAt ((s,l) :: sh) 0 = (s,0,l,0) := by simp [fieldAt, hl]

/-- At an internal field boundary, the next cursor has index zero.  Zero-length fields
are skipped, so this fact does not need a positivity hypothesis on the shape. -/
theorem fieldAt_next_boundary (sh : List (Nat × Nat)) (p : Nat)
    (hp : p + 1 < fieldsLen sh)
    (he : (fieldAt sh p).2.1 + 1 = (fieldAt sh p).2.2.1) :
    (fieldAt sh (p + 1)).2.1 = 0 := by
  have hz : ∀ sh : List (Nat × Nat), (fieldAt sh 0).2.1 = 0 := by
    intro sh
    induction sh with
    | nil => rfl
    | cons f sh ih =>
      obtain ⟨s,l⟩ := f
      by_cases h : 0 < l
      · simp [fieldAt, h]
      · simp [fieldAt, h, ih]
  induction sh generalizing p with
  | nil => simp at hp
  | cons f sh ih =>
    obtain ⟨s,l⟩ := f
    by_cases h : p < l
    · simp only [fieldAt, h, ite_true] at he
      simp only [fieldAt, he, Nat.lt_irrefl, ite_false, Nat.sub_self]
      exact hz sh
    · have h' : ¬ p + 1 < l := by omega
      simp only [fieldsLen_cons] at hp
      simp only [fieldAt, h, ite_false] at he
      simp only [fieldAt, h', ite_false]
      rw [show p + 1 - l = (p - l) + 1 by omega]
      exact ih (p - l) (by omega) he

/-- Appending fields does not change the cursor before the prefix ends. -/
theorem fieldAt_append_before (pre post : List (Nat × Nat)) (p : Nat)
    (hp : p < fieldsLen pre) : fieldAt (pre ++ post) p = fieldAt pre p := by
  induction pre generalizing p with
  | nil => simp at hp
  | cons f pre ih =>
    obtain ⟨s,l⟩ := f
    simp only [fieldsLen_cons] at hp
    by_cases h : p < l
    · simp [fieldAt,h]
    · simp only [List.cons_append,fieldAt,h,ite_false]
      rw [ih (p-l) (by omega)]

/-- Beyond the serialization the cursor has sentinel state 9 and counts all windows. -/
theorem fieldAt_past (sh : List (Nat × Nat)) (p : Nat) (hp : fieldsLen sh ≤ p) :
    fieldAt sh p = (9,0,0,nWin sh) := by
  induction sh generalizing p with
  | nil => rfl
  | cons f sh ih =>
    obtain ⟨s,l⟩ := f
    simp only [fieldsLen_cons] at hp
    have hn : ¬ p < l := by omega
    simp only [fieldAt,hn,ite_false]
    rw [ih (p-l) (by omega)]
    by_cases hs : s = 7 <;> simp [nWin,hs]

/-- Passing a serialized prefix subtracts its byte length and counts its child windows. -/
theorem fieldAt_append_after (pre post : List (Nat × Nat)) (p : Nat)
    (hp : fieldsLen pre ≤ p) :
    fieldAt (pre ++ post) p =
      ((fieldAt post (p - fieldsLen pre)).1,
       (fieldAt post (p - fieldsLen pre)).2.1,
       (fieldAt post (p - fieldsLen pre)).2.2.1,
       (fieldAt post (p - fieldsLen pre)).2.2.2 + nWin pre) := by
  induction pre generalizing p with
  | nil => simp [fieldAt,fieldsLen,nWin]
  | cons f pre ih =>
    obtain ⟨s,l⟩ := f
    simp only [fieldsLen_cons] at hp
    have hn : ¬ p < l := by omega
    simp only [List.cons_append,fieldAt,hn,ite_false]
    rw [ih (p - l) (by omega)]
    have he : p - l - fieldsLen pre = p - (l + fieldsLen pre) := by omega
    rw [he]
    simp only [fieldsLen_cons]
    by_cases hs : s = 7 <;> simp [nWin,hs,Nat.add_assoc]

/-- Every canonical node field has a valid state and positive length. -/
theorem nodeFields_mem {ty hk children s l : Nat}
    (h : (s,l) ∈ nodeFields ty hk children) : s < 9 ∧ 0 < l := by
  simp only [nodeFields, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_replicate] at h
  rcases h with ((((h | h) | h) | h) | h) | h
  · cases h; omega
  · split at h
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with (h | h) | h
      · cases h; omega
      · cases h; omega
      · split at h
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          cases h; constructor <;> omega
        · cases h
    · cases h
  · split at h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h <;> cases h <;> omega
    · cases h
  · split at h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      cases h; omega
    · cases h
  · rcases h with ⟨_, h⟩; cases h; omega
  · cases h; omega

/-- Length of each scalar field; child windows all have the fixed digest width. -/
theorem nodeFields_length {ty hk children s l : Nat}
    (h : (s,l) ∈ nodeFields ty hk children) :
    (s = 0 → l = 1) ∧ (s = 1 → l = 4) ∧ (s = 2 → l = 1) ∧
    (s = 3 → l + 1 = hk) ∧ (s = 4 → l = 4) ∧ (s = 5 → l = 32) ∧
    (s = 6 → l = 2) ∧ (s = 7 → l = 32) ∧ (s = 8 → l = 8) := by
  simp only [nodeFields, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_replicate] at h
  rcases h with ((((h | h) | h) | h) | h) | h
  · cases h; omega
  · split at h
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with (h | h) | h
      · cases h; omega
      · cases h; omega
      · split at h
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          cases h; omega
        · cases h
    · cases h
  · split at h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h <;> cases h <;> omega
    · cases h
  · split at h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      cases h; omega
    · cases h
  · rcases h with ⟨_, h⟩; cases h; omega
  · cases h; omega

/-- Canonical serialization gives a live cursor one of the nine field states. -/
theorem FieldsOk.state {Q : UpsPartI} (ok : FieldsOk Q) {p : Nat} (hp : p < Q.q.length) :
    (fieldAt Q.shape p).1 < 9 := by
  have hm := (fieldAt_bounds Q.shape p (by rw [← ok.bytes]; exact hp)).2
  have hn : ((fieldAt Q.shape p).1, (fieldAt Q.shape p).2.2.1) ∈
      nodeFields Q.ty Q.qhk (nWin Q.shape) := by rw [← ok.shape]; exact hm
  exact (nodeFields_mem hn).1

/-- The first byte of a canonical node is its one-byte tag. -/
theorem FieldsOk.first {Q : UpsPartI} (ok : FieldsOk Q) :
    fieldAt Q.shape 0 = (0,0,1,0) := by
  rw [ok.shape]
  simp [nodeFields, fieldAt]

end ZkFormal.NearV3.Render.UpsGen
