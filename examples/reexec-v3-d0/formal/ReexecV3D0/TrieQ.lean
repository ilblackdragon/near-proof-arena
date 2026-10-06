import ReexecV3D0.NormDefs

/-!
# `buildFor` depends on the store only at the hashes it looks up (`qFor`)
-/

namespace ReexecV3D0

open NearSpec NearSpecV3

theorem mkSlot_agree {s s' : Store} {len : Nat} {vh : Bytes} {want : Bool}
    (h : want = true → storeGet s' vh = storeGet s vh) :
    mkSlot s' len vh want = mkSlot s len vh want := by
  unfold mkSlot
  cases want
  · rfl
  · simp only [ite_true]; rw [h rfl]


theorem buildKidsWith_agree {f g : Bytes → List (List Nat) → PTrie}
    {qf : Bytes → List (List Nat) → List Bytes} {P : Bytes → Prop}
    (hfg : ∀ ch ks, (∀ x ∈ qf ch ks, P x) → f ch ks = g ch ks) :
    ∀ (i : Nat) (hs : List (Option Bytes)) (keys : List (List Nat)),
    (∀ x ∈ qKids qf i hs keys, P x) → buildKidsWith f i hs keys = buildKidsWith g i hs keys := by
  intro i hs
  induction hs generalizing i with
  | nil => intro keys _; rfl
  | cons o more ih =>
    intro keys hq
    cases o with
    | none =>
      simp only [buildKidsWith]
      rw [ih (i + 1) keys (by simpa [qKids] using hq)]
    | some ch =>
      simp only [buildKidsWith]
      simp only [qKids, List.mem_append] at hq
      rw [hfg ch _ (fun x hx => hq x (Or.inl hx)), ih (i + 1) keys (fun x hx => hq x (Or.inr hx))]

theorem branchWith_agree {f g : Bytes → List (List Nat) → PTrie}
    {qf : Bytes → List (List Nat) → List Bytes} {P : Bytes → Prop}
    (hfg : ∀ ch ks, (∀ x ∈ qf ch ks, P x) → f ch ks = g ch ks)
    (h : Bytes) (v : Option Slot) (rest : Bytes) (keys : List (List Nat)) (mem : Nat)
    (hq : ∀ x ∈ qBranch qf rest keys, P x) :
    branchWith f h v rest keys mem = branchWith g h v rest keys mem := by
  unfold branchWith
  unfold qBranch at hq
  dsimp only at hq ⊢
  split
  · rfl
  · rename_i hne
    simp only [hne] at hq
    rw [buildKidsWith_agree hfg 0 _ keys hq]

/-- **Agreement.** If two stores agree on every hash `buildFor` looks up, the partial
tries are equal. -/
theorem buildFor_agree (s s' : Store) :
    ∀ fuel h keys, (∀ x ∈ qFor s fuel h keys, storeGet s' x = storeGet s x) →
      buildFor s' fuel h keys = buildFor s fuel h keys := by
  intro fuel
  induction fuel with
  | zero => intro h keys _; rfl
  | succ fuel ih =>
    intro h keys hq
    unfold buildFor
    unfold qFor at hq
    by_cases hk : keys.isEmpty = true
    · simp only [hk, ite_true]
    · simp only [hk, Bool.false_eq_true, ite_false, List.mem_cons] at hq ⊢
      rw [hq h (Or.inl rfl)]
      have hq' := fun x hx => hq x (Or.inr hx)
      clear hq
      cases hg : storeGet s h with
      | none => rfl
      | some node =>
        simp only [hg] at hq'
        dsimp only at hq' ⊢
        split
        · rfl
        · rename_i hlen
          simp only [hlen, ite_false] at hq'
          split
          · -- leaf
            rename_i rest hb
            simp only [hb] at hq'
            split
            · rename_i k hk2
              simp only [hk2] at hq'
              split
              · rfl
              · rename_i hl
                simp only [hl, Bool.false_eq_true, ite_false] at hq'
                rw [mkSlot_agree (fun hw => by
                  apply hq'; simp [hw])]
            · rfl
          · -- extension
            rename_i rest hb
            simp only [hb] at hq'
            split
            · rename_i k hk2
              simp only [hk2] at hq'
              split
              · rfl
              · rename_i hl
                simp only [hl, Bool.false_eq_true, ite_false] at hq'
                rw [ih _ _ hq']
            · rfl
          · -- branch
            rename_i rest hb
            simp only [hb] at hq'
            exact branchWith_agree (P := fun x => storeGet s' x = storeGet s x)
              (fun ch ks hc => ih ch ks hc) h none rest keys _ hq'
          · -- branch with value
            rename_i rest hb
            simp only [hb] at hq'
            split
            · rfl
            · rename_i hl
              simp only [hl, ite_false, List.mem_append] at hq'
              rw [mkSlot_agree (fun hw => by apply hq'; left; simp only [hw, ite_true, List.mem_singleton])]
              exact branchWith_agree (P := fun x => storeGet s' x = storeGet s x)
                (fun ch ks hc => ih ch ks hc) h _ (rest.drop 36) keys _ (fun x hx => hq' x (Or.inr hx))
          · rfl

end ReexecV3D0
