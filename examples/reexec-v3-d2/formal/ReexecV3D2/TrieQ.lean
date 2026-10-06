import ReexecV3D2.NormLemmas

/-!
# The recorded-storage tree `HStore`, and `revealAll` depends on the store only at the
hashes it looks up (`qAll`)
-/

namespace ReexecV3D2

open NearSpec NearSpecV3 NearSpecV3.D2

/-! ## `cmpBytes` and `HStore` lookups -/

theorem cmpBytes_cases : ∀ a b : Bytes, cmpBytes a b = 0 ∨ cmpBytes a b = 1 ∨ cmpBytes a b = 2
  | [], [] => by simp [cmpBytes]
  | [], _ :: _ => by simp [cmpBytes]
  | _ :: _, [] => by simp [cmpBytes]
  | x :: xs, y :: ys => by
    simp only [cmpBytes]
    split
    · simp
    · split
      · simp
      · exact cmpBytes_cases xs ys

theorem cmpBytes_eq_one : ∀ a b : Bytes, cmpBytes a b = 1 ↔ a = b
  | [], [] => by simp [cmpBytes]
  | [], _ :: _ => by simp [cmpBytes]
  | _ :: _, [] => by simp [cmpBytes]
  | x :: xs, y :: ys => by
    simp only [cmpBytes]
    by_cases h1 : x.toNat < y.toNat
    · simp only [h1, ite_true]
      constructor
      · intro h; cases h
      · intro h; cases h; omega
    · by_cases h2 : y.toNat < x.toNat
      · simp only [h1, h2, ite_true, ite_false]
        constructor
        · intro h; cases h
        · intro h; cases h; omega
      · have hxy : x = y := UInt8.toNat_inj.mp (by omega)
        subst hxy
        simp only [h1, h2, ite_false, List.cons.injEq, true_and]
        exact cmpBytes_eq_one xs ys

theorem cmp_ne_one {a b : Bytes} (h : a ≠ b) : cmpBytes a b = 0 ∨ cmpBytes a b = 2 := by
  rcases cmpBytes_cases a b with h0 | h1 | h2
  · exact Or.inl h0
  · exact absurd ((cmpBytes_eq_one a b).mp h1) h
  · exact Or.inr h2

theorem get?_insert (k v k' : Bytes) :
    ∀ s : HStore, (s.insert k v).get? k' = if k' = k then some v else s.get? k'
  | .tip => by
    simp only [HStore.insert, HStore.get?]
    by_cases hk : k' = k
    · subst hk; rw [(cmpBytes_eq_one k' k').mpr rfl]; simp
    · rcases cmp_ne_one hk with h | h <;> simp [h, hk, HStore.get?]
  | .node k0 v0 l r => by
    simp only [HStore.insert]
    rcases cmpBytes_cases k k0 with hc | hc | hc
    · simp only [hc, HStore.get?]
      rcases cmpBytes_cases k' k0 with hd | hd | hd
      · simp only [hd]; exact get?_insert k v k' l
      · have := (cmpBytes_eq_one _ _).mp hd; subst this
        have hk : ¬ k' = k := fun e => by subst e; rw [(cmpBytes_eq_one _ _).mpr rfl] at hc; cases hc
        simp [hd, hk]
      · simp only [hd]
        by_cases hk : k' = k
        · subst hk; rw [hc] at hd; cases hd
        · simp [hk]
    · have := (cmpBytes_eq_one _ _).mp hc; subst this
      simp only [hc]
      rcases cmpBytes_cases k' k with hd | hd | hd
      · have hk : ¬ k' = k := fun e => by subst e; rw [(cmpBytes_eq_one _ _).mpr rfl] at hd; cases hd
        simp [HStore.get?, hd, hk]
      · have := (cmpBytes_eq_one _ _).mp hd; subst this; simp [HStore.get?, hd]
      · have hk : ¬ k' = k := fun e => by subst e; rw [(cmpBytes_eq_one _ _).mpr rfl] at hd; cases hd
        simp [HStore.get?, hd, hk]
    · simp only [hc, HStore.get?]
      rcases cmpBytes_cases k' k0 with hd | hd | hd
      · simp only [hd]
        by_cases hk : k' = k
        · subst hk; rw [hc] at hd; cases hd
        · simp [hk]
      · have := (cmpBytes_eq_one _ _).mp hd; subst this
        have hk : ¬ k' = k := fun e => by subst e; rw [(cmpBytes_eq_one _ _).mpr rfl] at hc; cases hc
        simp [hd, hk]
      · simp only [hd]; exact get?_insert k v k' r

theorem hGet_foldl (h : Bytes) : ∀ (L : List Bytes) (s : HStore),
    (L.foldl (fun m v => m.insert (sha256 v) v) s).get? h =
      (L.reverse.find? (fun v => sha256 v == h)).or (s.get? h)
  | [], s => by simp
  | x :: xs, s => by
    simp only [List.foldl_cons, List.reverse_cons]
    rw [hGet_foldl h xs, get?_insert, List.find?_append]
    by_cases hx : h = sha256 x
    · subst hx
      simp only [ite_true, List.find?_cons, beq_self_eq_true, List.find?_nil]
      cases xs.reverse.find? (fun v => sha256 v == sha256 x) <;> rfl
    · have : (sha256 x == h) = false := by simp; exact fun e => hx e.symm
      simp only [hx, ite_false, List.find?_cons, this, List.find?_nil]
      cases xs.reverse.find? (fun v => sha256 v == h) <;> simp

theorem hGet_mkHStore (L : List Bytes) (h : Bytes) :
    hGet (mkHStore L) h = L.reverse.find? (fun v => sha256 v == h) := by
  unfold hGet mkHStore
  rw [hGet_foldl]
  simp [HStore.get?]

theorem hGet_some {L : List Bytes} {h w : Bytes} (e : hGet (mkHStore L) h = some w) :
    sha256 w = h ∧ w ∈ L := by
  rw [hGet_mkHStore] at e
  have h1 := List.find?_some e
  have h2 := List.mem_of_find?_eq_some e
  simp only [beq_iff_eq] at h1
  exact ⟨h1, List.mem_reverse.mp h2⟩

/-- The normal-form store answers like the original one at every looked-up hash. -/
theorem hGet_normValsH (vals q : List Bytes) :
    ∀ x ∈ q, hGet (mkHStore (normValsH vals q)) x = hGet (mkHStore vals) x := by
  intro x hx
  have hP : ∀ w ∈ normValsH vals q, hGet (mkHStore vals) (sha256 w) = some w := by
    intro w hw
    unfold normValsH at hw
    rw [mem_isort] at hw
    have := mem_dedupLastBy id _ w hw
    rw [List.mem_filterMap] at this
    obtain ⟨y, -, hy⟩ := this
    have := (hGet_some hy).1
    rw [this]; exact hy
  rw [hGet_mkHStore (normValsH vals q)]
  cases hg : hGet (mkHStore vals) x with
  | none =>
    rw [List.find?_eq_none]
    intro w hw hwx
    have := hP w (List.mem_reverse.mp hw)
    simp only [beq_iff_eq] at hwx
    rw [hwx, hg] at this; cases this
  | some v =>
    have hv : v ∈ normValsH vals q := by
      unfold normValsH
      rw [mem_isort]
      apply mem_dedupLastBy_id
      exact List.mem_filterMap.mpr ⟨x, hx, hg⟩
    have hvx := (hGet_some hg).1
    cases hf : (normValsH vals q).reverse.find? (fun v => sha256 v == x) with
    | none =>
      rw [List.find?_eq_none] at hf
      have := hf v (List.mem_reverse.mpr hv)
      simp [hvx] at this
    | some w =>
      have h1 := List.find?_some hf
      have h2 := List.mem_of_find?_eq_some hf
      simp only [beq_iff_eq] at h1
      have := hP w (List.mem_reverse.mp h2)
      rw [h1, hg] at this
      rw [this]

theorem mem_normValsH {vals q : List Bytes} {x : Bytes} (hx : x ∈ normValsH vals q) : x ∈ vals := by
  unfold normValsH at hx
  rw [mem_isort] at hx
  have := mem_dedupLastBy id _ x hx
  rw [List.mem_filterMap] at this
  obtain ⟨y, -, hy⟩ := this
  exact (hGet_some hy).2

theorem normValsH_nodup (vals q : List Bytes) : (normValsH vals q).Nodup := by
  unfold normValsH
  exact (isort_perm _ _).symm.nodup (by
    have := dedupLastBy_pairwise id (q.filterMap (hGet (mkHStore vals)))
    exact this.imp (fun h => h))

/-- Re-normalising with a sub-list of the looked-up hashes. -/
theorem normValsH_idem (vals : List Bytes) (q q' : List Bytes) (hq' : ∀ x ∈ q', x ∈ q) :
    normValsH (normValsH vals q) q' = normValsH vals q' := by
  have := filterMap_congr_mem _ _ q' (fun x hx => hGet_normValsH vals q x (hq' x hx))
  unfold normValsH at this ⊢
  rw [this]

/-! ## `revealAll` agreement -/

theorem hSlot_agree {s s' : HStore} {len : Nat} {vh : Bytes} (h : hGet s' vh = hGet s vh) :
    hSlot s' len vh = hSlot s len vh := by
  unfold hSlot; rw [h]

theorem revealKids_agree {f g : Bytes → PTrie} {qf : Bytes → List Bytes} {P : Bytes → Prop}
    (hfg : ∀ ch, (∀ x ∈ qf ch, P x) → f ch = g ch) :
    ∀ (hs : List (Option Bytes)), (∀ x ∈ qKidsAll qf hs, P x) → revealKids f hs = revealKids g hs
  | [], _ => rfl
  | none :: more, hq => by
    simp only [revealKids]
    rw [revealKids_agree hfg more (by simpa [qKidsAll] using hq)]
  | some ch :: more, hq => by
    simp only [revealKids]
    simp only [qKidsAll, List.mem_append] at hq
    rw [hfg ch (fun x hx => hq x (Or.inl hx)), revealKids_agree hfg more (fun x hx => hq x (Or.inr hx))]

/-- **Agreement.** If two stores agree on every hash `revealAll` looks up, the revealed
tries are equal. -/
theorem revealAll_agree (s s' : HStore) :
    ∀ fuel h, (∀ x ∈ qAll s fuel h, hGet s' x = hGet s x) → revealAll s' fuel h = revealAll s fuel h := by
  intro fuel
  induction fuel with
  | zero => intro h _; rfl
  | succ fuel ih =>
    intro h hq
    unfold revealAll
    unfold qAll at hq
    simp only [List.mem_cons] at hq
    rw [hq h (Or.inl rfl)]
    have hq' := fun x hx => hq x (Or.inr hx)
    clear hq
    cases hg : hGet s h with
    | none => rfl
    | some node =>
      simp only [hg] at hq'
      dsimp only at hq' ⊢
      split
      · rfl
      · rename_i hlen
        simp only [hlen, ite_false] at hq'
        split
        · rename_i rest hb
          simp only [hb] at hq'
          split
          · rename_i k hk2
            simp only [hk2] at hq'
            split
            · rfl
            · rename_i hl
              simp only [hl, Bool.false_eq_true, ite_false, List.mem_singleton] at hq'
              rw [hSlot_agree (hq' _ rfl)]
          · rfl
        · rename_i rest hb
          simp only [hb] at hq'
          split
          · rename_i k hk2
            simp only [hk2] at hq'
            split
            · rfl
            · rename_i hl
              simp only [hl, Bool.false_eq_true, ite_false] at hq'
              rw [ih _ hq']
          · rfl
        · rename_i rest hb
          simp only [hb] at hq'
          split
          · rfl
          · rename_i hl
            simp only [hl, Bool.false_eq_true, ite_false] at hq'
            rw [revealKids_agree (P := fun x => hGet s' x = hGet s x) (fun ch hc => ih ch hc) _ hq']
        · rename_i rest hb
          simp only [hb] at hq'
          split
          · rfl
          · rename_i hl
            simp only [hl, ite_false] at hq'
            split
            · rfl
            · rename_i hl2
              simp only [hl2, Bool.false_eq_true, ite_false, List.mem_cons] at hq'
              rw [hSlot_agree (hq' _ (Or.inl rfl)),
                revealKids_agree (P := fun x => hGet s' x = hGet s x) (fun ch hc => ih ch hc) _
                  (fun x hx => hq' x (Or.inr hx))]
        · rfl

theorem qKidsAll_agree {f g : Bytes → List Bytes} {P : Bytes → Prop}
    (hfg : ∀ ch, (∀ x ∈ f ch, P x) → g ch = f ch) :
    ∀ (hs : List (Option Bytes)), (∀ x ∈ qKidsAll f hs, P x) → qKidsAll g hs = qKidsAll f hs
  | [], _ => rfl
  | none :: more, hq => by
    simp only [qKidsAll]
    exact qKidsAll_agree hfg more (by simpa [qKidsAll] using hq)
  | some ch :: more, hq => by
    simp only [qKidsAll, List.mem_append] at hq ⊢
    rw [hfg ch (fun x hx => hq x (Or.inl hx)), qKidsAll_agree hfg more (fun x hx => hq x (Or.inr hx))]

/-- `qAll` itself only depends on the store at the hashes it looks up. -/
theorem qAll_agree (s s' : HStore) :
    ∀ fuel h, (∀ x ∈ qAll s fuel h, hGet s' x = hGet s x) → qAll s' fuel h = qAll s fuel h := by
  intro fuel
  induction fuel with
  | zero => intro h _; rfl
  | succ fuel ih =>
    intro h hq
    unfold qAll at hq ⊢
    simp only [List.mem_cons] at hq
    rw [hq h (Or.inl rfl)]
    have hq' := fun x hx => hq x (Or.inr hx)
    clear hq
    congr 1
    cases hg : hGet s h with
    | none => rfl
    | some node =>
      simp only [hg] at hq' ⊢
      split
      · rfl
      · rename_i hlen
        simp only [hlen, ite_false] at hq'
        split
        · rfl
        · rename_i rest hb
          simp only [hb] at hq'
          split
          · rename_i k hk2
            simp only [hk2] at hq'
            split
            · rfl
            · rename_i hl
              simp only [hl, Bool.false_eq_true, ite_false] at hq'
              exact ih _ hq'
          · rfl
        · rename_i rest hb
          simp only [hb] at hq'
          split
          · rfl
          · rename_i hl
            simp only [hl, Bool.false_eq_true, ite_false] at hq'
            exact qKidsAll_agree (P := fun x => hGet s' x = hGet s x) (fun ch hc => ih ch hc) _ hq'
        · rename_i rest hb
          simp only [hb] at hq'
          split
          · rfl
          · rename_i hl
            simp only [hl, ite_false] at hq'
            split
            · rfl
            · rename_i hl2
              simp only [hl2, Bool.false_eq_true, ite_false, List.mem_cons] at hq'
              rw [qKidsAll_agree (P := fun x => hGet s' x = hGet s x) (fun ch hc => ih ch hc) _
                (fun x hx => hq' x (Or.inr hx))]
        · rfl

theorem revealAll_normValsH (vals q : List Bytes) (R : Bytes)
    (hq : ∀ x ∈ qAll (mkHStore vals) revealFuel R, x ∈ q) :
    revealAll (mkHStore (normValsH vals q)) revealFuel R = revealAll (mkHStore vals) revealFuel R :=
  revealAll_agree _ _ revealFuel R (fun x hx => hGet_normValsH vals q x (hq x hx))

theorem qAll_normValsH (vals q : List Bytes) (R : Bytes)
    (hq : ∀ x ∈ qAll (mkHStore vals) revealFuel R, x ∈ q) :
    qAll (mkHStore (normValsH vals q)) revealFuel R = qAll (mkHStore vals) revealFuel R :=
  qAll_agree _ _ revealFuel R (fun x hx => hGet_normValsH vals q x (hq x hx))

end ReexecV3D2
