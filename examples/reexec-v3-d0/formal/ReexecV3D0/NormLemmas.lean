import ReexecV3D0.TrieQ

/-!
# Normal-form lemmas: sorting, deduplication, and the value store
-/

namespace ReexecV3D0

open NearSpec NearSpecV3

theorem insertBy_perm {α : Type} (le : α → α → Bool) (x : α) :
    ∀ l : List α, (insertBy le x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertBy
    split
    · exact List.Perm.refl _
    · exact ((insertBy_perm le x ys).cons y).trans (List.Perm.swap x y ys)

theorem isort_perm {α : Type} (le : α → α → Bool) : ∀ l : List α, (isort le l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertBy_perm le x _).trans ((isort_perm le xs).cons x)

theorem mem_isort {α : Type} {le : α → α → Bool} {l : List α} {x : α} :
    x ∈ isort le l ↔ x ∈ l := (isort_perm le l).mem_iff

theorem dedupLastBy_sublist {α : Type} (k : α → Bytes) : ∀ l : List α, (dedupLastBy k l).Sublist l
  | [] => List.Sublist.slnil
  | e :: es => by
    unfold dedupLastBy
    split
    · exact (dedupLastBy_sublist k es).cons e
    · exact (dedupLastBy_sublist k es).cons₂ e

theorem mem_dedupLastBy {α : Type} (k : α → Bytes) : ∀ (l : List α) (x : α),
    x ∈ dedupLastBy k l → x ∈ l := fun l x h => (dedupLastBy_sublist k l).subset h

theorem mem_dedupLastBy_id : ∀ (l : List Bytes) (x : Bytes), x ∈ l → x ∈ dedupLastBy id l
  | [], x, h => by simp at h
  | e :: es, x, h => by
    unfold dedupLastBy
    simp only [List.mem_cons] at h
    split
    · rename_i hany
      rcases h with rfl | h
      · simp only [id, List.any_eq_true, beq_iff_eq] at hany
        obtain ⟨y, hy, rfl⟩ := hany
        exact mem_dedupLastBy_id es y hy
      · exact mem_dedupLastBy_id es x h
    · rcases h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_dedupLastBy_id es x h)

theorem storeGet_mkStore (l : List Bytes) (x : Bytes) :
    storeGet (mkStore l) x = l.find? (fun v => sha256 v == x) := by
  unfold storeGet mkStore
  rw [List.find?_map]
  have : ((fun p : Bytes × Bytes => p.1 == x) ∘ fun v => (sha256 v, v)) = (fun v => sha256 v == x) := rfl
  rw [this]
  cases l.find? (fun v => sha256 v == x) <;> rfl

theorem storeGet_some_hash {l : List Bytes} {x v : Bytes} (h : storeGet (mkStore l) x = some v) :
    sha256 v = x ∧ v ∈ l := by
  rw [storeGet_mkStore] at h
  have h1 := List.find?_some h
  have h2 := List.mem_of_find?_eq_some h
  simp only [beq_iff_eq] at h1
  exact ⟨h1, h2⟩

/-- The normal-form store agrees with the original one at every looked-up hash. -/
theorem storeGet_normVals (vals q : List Bytes) :
    ∀ x ∈ q, storeGet (mkStore (normVals vals q)) x = storeGet (mkStore vals) x := by
  intro x hx
  -- every normal-form value is the stored value for its own hash
  have hP : ∀ w ∈ normVals vals q, storeGet (mkStore vals) (sha256 w) = some w := by
    intro w hw
    unfold normVals at hw
    rw [mem_isort] at hw
    have := mem_dedupLastBy id _ w hw
    rw [List.mem_filterMap] at this
    obtain ⟨y, -, hy⟩ := this
    have := (storeGet_some_hash hy).1
    rw [this]; exact hy
  rw [storeGet_mkStore (normVals vals q)]
  cases hg : storeGet (mkStore vals) x with
  | none =>
    rw [List.find?_eq_none]
    intro w hw hwx
    have := hP w hw
    simp only [beq_iff_eq] at hwx
    rw [hwx, hg] at this; cases this
  | some v =>
    have hv : v ∈ normVals vals q := by
      unfold normVals
      rw [mem_isort]
      apply mem_dedupLastBy_id
      exact List.mem_filterMap.mpr ⟨x, hx, hg⟩
    have hvx := (storeGet_some_hash hg).1
    cases hf : (normVals vals q).find? (fun v => sha256 v == x) with
    | none =>
      rw [List.find?_eq_none] at hf
      have := hf v hv
      simp [hvx] at this
    | some w =>
      have h1 := List.find?_some hf
      have h2 := List.mem_of_find?_eq_some hf
      simp only [beq_iff_eq] at h1
      have := hP w h2
      rw [h1, hg] at this
      rw [this]

theorem partialTrie_normVals (vals q : List Bytes) (R : Bytes) (K : List (List Nat))
    (hq : ∀ x ∈ qFor (mkStore vals) trieFuel R K, x ∈ q) :
    partialTrie (normVals vals q) R K = partialTrie vals R K := by
  unfold partialTrie
  exact buildFor_agree _ _ trieFuel R K (fun x hx => storeGet_normVals vals q x (hq x hx))

/-! ## Receipt-proof entries -/

theorem dedupLastBy_pairwise {α : Type} (k : α → Bytes) :
    ∀ l : List α, (dedupLastBy k l).Pairwise (fun a b => k a ≠ k b)
  | [] => List.Pairwise.nil
  | e :: es => by
    unfold dedupLastBy
    split
    · exact dedupLastBy_pairwise k es
    · rename_i hany
      refine List.Pairwise.cons (fun b hb => ?_) (dedupLastBy_pairwise k es)
      intro heq
      apply hany
      rw [List.any_eq_true]
      exact ⟨b, mem_dedupLastBy k es b hb, by rw [heq]; exact beq_self_eq_true _⟩

theorem dedupLastBy_of_pairwise {α : Type} (k : α → Bytes) :
    ∀ l : List α, l.Pairwise (fun a b => k a ≠ k b) → dedupLastBy k l = l
  | [] => fun _ => rfl
  | e :: es => fun h => by
    unfold dedupLastBy
    rw [List.pairwise_cons] at h
    have hno : es.any (fun x => k x == k e) = false := by
      rw [Bool.eq_false_iff]
      intro ha
      rw [List.any_eq_true] at ha
      obtain ⟨x, hx, hxe⟩ := ha
      exact h.1 x hx (by simp at hxe; exact hxe.symm)
    rw [hno]
    simp only [Bool.false_eq_true, ite_false]
    rw [dedupLastBy_of_pairwise k es h.2]

theorem lookupLast_eq_find {k : Bytes} :
    ∀ l : List ProofEntry, l.Pairwise (fun a b => a.key ≠ b.key) →
      lookupLast k l = l.find? (fun e => e.key == k)
  | [] => fun _ => rfl
  | e :: es => fun h => by
    rw [List.pairwise_cons] at h
    simp only [lookupLast, List.find?_cons]
    rw [lookupLast_eq_find es h.2]
    by_cases hek : (e.key == k) = true
    · simp only [hek]
      have : es.find? (fun e => e.key == k) = none := by
        rw [List.find?_eq_none]
        intro x hx hxk
        simp only [beq_iff_eq] at hek hxk
        exact h.1 x hx (by rw [hek, hxk])
      rw [this]; simp
    · simp only [Bool.not_eq_true] at hek
      simp only [hek]
      cases es.find? (fun e => e.key == k) <;> rfl

theorem find?_perm_unique {α : Type} (p : α → Bool) {l l' : List α} (hp : l.Perm l') :
    l.Pairwise (fun a b => ¬ (p a = true ∧ p b = true)) → l.find? p = l'.find? p := by
  induction hp with
  | nil => intro; rfl
  | cons x _ ih =>
    intro h
    rw [List.pairwise_cons] at h
    simp only [List.find?_cons]
    rw [ih h.2]
  | swap x y l =>
    intro h
    simp only [List.pairwise_cons, List.mem_cons] at h
    simp only [List.find?_cons]
    cases hx : p x <;> cases hy : p y <;> simp
    exact absurd ⟨hy, hx⟩ (h.1 x (Or.inl rfl))
  | trans h1 _ ih1 ih2 =>
    intro h
    rw [ih1 h, ih2 (h1.pairwise h (fun hh => fun hb => hh ⟨hb.2, hb.1⟩))]

theorem normEntries_pairwise (es : List ProofEntry) :
    (normEntries es).Pairwise (fun a b => a.key ≠ b.key) :=
  (isort_perm _ _).symm.pairwise (dedupLastBy_pairwise _ es) (fun h => fun h' => h h'.symm)

theorem lookupLast_dedup {k : Bytes} :
    ∀ es : List ProofEntry, lookupLast k (dedupLastBy (·.key) es) = lookupLast k es
  | [] => rfl
  | e :: es => by
    unfold dedupLastBy
    split
    · rename_i hany
      rw [lookupLast_dedup es]
      simp only [lookupLast]
      cases hl : lookupLast k es with
      | some x => rfl
      | none =>
        -- some later entry has e's key; if that key is k, lookupLast k es would be some
        by_cases hek : (e.key == k) = true
        · exfalso
          rw [List.any_eq_true] at hany
          obtain ⟨x, hx, hxe⟩ := hany
          simp only [beq_iff_eq] at hek hxe
          have : lookupLast k es ≠ none := by
            clear hl
            induction es with
            | nil => cases hx
            | cons y ys ihy =>
              simp only [lookupLast]
              cases hy : lookupLast k ys with
              | some z => simp
              | none =>
                rcases List.mem_cons.mp hx with rfl | hx'
                · simp [hxe, hek]
                · exact absurd hy (ihy hx')
          exact this hl
        · simp only [Bool.not_eq_true] at hek; simp [hek]
    · simp only [lookupLast]
      rw [lookupLast_dedup es]

theorem lookupLast_normEntries (k : Bytes) (es : List ProofEntry) :
    lookupLast k (normEntries es) = lookupLast k es := by
  rw [lookupLast_eq_find _ (normEntries_pairwise es), ← lookupLast_dedup es,
    lookupLast_eq_find _ (dedupLastBy_pairwise _ es)]
  unfold normEntries
  apply find?_perm_unique _ (isort_perm _ _)
  exact (isort_perm _ _).symm.pairwise (dedupLastBy_pairwise _ es)
    (fun h => fun h' => h h'.symm) |>.imp (fun hne hb => by
      simp only [beq_iff_eq] at hb; exact hne (by rw [hb.1, hb.2]))

theorem dedup_has_key : ∀ (es : List ProofEntry) (x : ProofEntry), x ∈ es →
    ∃ y ∈ dedupLastBy (·.key) es, y.key = x.key
  | [], x, hx => by cases hx
  | z :: zs, x, hx => by
    unfold dedupLastBy
    rcases List.mem_cons.mp hx with rfl | hx'
    · split
      · rename_i hany
        rw [List.any_eq_true] at hany
        obtain ⟨w, hw, hwe⟩ := hany
        simp only [beq_iff_eq] at hwe
        obtain ⟨y, hy, hye⟩ := dedup_has_key zs w hw
        exact ⟨y, hy, by rw [hye, hwe]⟩
      · exact ⟨x, List.mem_cons_self, rfl⟩
    · obtain ⟨y, hy, hye⟩ := dedup_has_key zs x hx'
      split
      · exact ⟨y, hy, hye⟩
      · exact ⟨y, List.mem_cons_of_mem _ hy, hye⟩

theorem distinctKeys_eq (es : List ProofEntry) :
    distinctKeys es = (dedupLastBy (·.key) es).map (·.key) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [distinctKeys, dedupLastBy]
    rw [ih]
    have hc : ((dedupLastBy (·.key) es).map (·.key)).contains e.key = es.any (fun x => x.key == e.key) := by
      rw [Bool.eq_iff_iff, List.contains_iff_mem, List.mem_map, List.any_eq_true]
      constructor
      · rintro ⟨x, hx, hxk⟩; exact ⟨x, mem_dedupLastBy _ es x hx, by simp [hxk]⟩
      · rintro ⟨x, hx, hxe⟩
        simp only [beq_iff_eq] at hxe
        have := dedup_has_key es x hx
        obtain ⟨y, hy, hye⟩ := this
        exact ⟨y, hy, by rw [hye, hxe]⟩
    rw [hc]
    split <;> rfl

theorem distinctKeys_normEntries_length (es : List ProofEntry) :
    (distinctKeys (normEntries es)).length = (distinctKeys es).length := by
  rw [distinctKeys_eq, distinctKeys_eq, List.length_map, List.length_map,
    dedupLastBy_of_pairwise _ _ (normEntries_pairwise es)]
  exact (isort_perm _ _).length_eq

end ReexecV3D0
