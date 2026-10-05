import ZkFormal.Near.Extract.RcptCharClass

/-!
# ZkFormal.Near.Extract.RcptStrings — account-id grammar (pure part)

`char_spec`: the character classes of `RcptCharClass` are those of
`AccountId`; `charsOk_of`: no leading, trailing or doubled separator gives
`AccountId.charsOk`.
-/

namespace ZkFormal.Near.RcptProof

open NearSpec

instance (hi lo : Nat) : Decidable (ClassOK hi lo) := by unfold ClassOK; infer_instance

theorem char_spec : ∀ hi, hi < 8 → ∀ lo, lo < 16 → ClassOK hi lo →
    (AccountId.isAlnum (UInt8.ofNat (16 * hi + lo)) || AccountId.isSep (UInt8.ofNat (16 * hi + lo))) = true ∧
    (AccountId.isSep (UInt8.ofNat (16 * hi + lo)) = decide (hi = 2 ∨ hi = 5)) ∧
    (AccountId.isAlnum (UInt8.ofNat (16 * hi + lo)) = true → AccountId.isSep (UInt8.ofNat (16 * hi + lo)) = false) ∧
    (AccountId.isHex (UInt8.ofNat (16 * hi + lo)) = decide (hi = 3 ∨ (hi = 6 ∧ lo ≤ 6))) ∧
    16 * hi + lo < 128 := by
  decide

theorem charsOk_of : ∀ (l : List UInt8) (b : Bool),
    (∀ c ∈ l, (AccountId.isAlnum c || AccountId.isSep c) = true) →
    (∀ c ∈ l, AccountId.isAlnum c = true → AccountId.isSep c = false) →
    (∀ i (h : i + 1 < l.length), ¬ (AccountId.isSep l[i] = true ∧ AccountId.isSep l[i + 1] = true)) →
    (b = true → ∀ (h : 0 < l.length), AccountId.isSep l[0] = false) →
    (∀ (h : 0 < l.length), AccountId.isSep l[l.length - 1] = false) →
    (l = [] → b = false) →
    AccountId.charsOk b l = true := by
  intro l
  induction l with
  | nil => intro b _ _ _ _ _ hb; simp [AccountId.charsOk, hb rfl]
  | cons c cs ih =>
    intro b hcl hdis hcons hfirst hlast _
    simp only [AccountId.charsOk]
    have hc := hcl c (by simp)
    by_cases ha : AccountId.isAlnum c = true
    · rw [if_pos ha]
      refine ih false (fun d hd => hcl d (by simp [hd])) (fun d hd => hdis d (by simp [hd]))
        (fun i h => hcons (i + 1) (by simp; omega)) (fun h => by simp at h) (fun h => ?_) (fun _ => rfl)
      have := hlast (by simp)
      have e : (c :: cs)[(c :: cs).length - 1]'(by simp) = cs[cs.length - 1] := by
        rw [List.getElem_cons]; simp only [List.length_cons, Nat.add_sub_cancel]
        rw [dif_neg (by omega)]
      rwa [e] at this
    · rw [if_neg ha]
      have hs : AccountId.isSep c = true := by simpa [ha] using hc
      rw [if_pos hs]
      have hb : b = false := by
        cases b
        · rfl
        · have := hfirst rfl (by simp); simp [hs] at this
      subst hb
      simp only [Bool.not_false, Bool.true_and]
      have hne : cs ≠ [] := by
        intro he; subst he
        have := hlast (by simp); simp [hs] at this
      refine ih true (fun d hd => hcl d (by simp [hd])) (fun d hd => hdis d (by simp [hd]))
        (fun i h => hcons (i + 1) (by simp; omega)) (fun _ h => ?_) (fun h => ?_) (fun he => absurd he hne)
      · have := hcons 0 (by simp; omega)
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at this
        cases h' : AccountId.isSep cs[0] <;> simp_all
      · have := hlast (by simp)
        have e : (c :: cs)[(c :: cs).length - 1]'(by simp) = cs[cs.length - 1] := by
          rw [List.getElem_cons]; simp only [List.length_cons, Nat.add_sub_cancel]
          rw [dif_neg (by omega)]
        rwa [e] at this

end ZkFormal.Near.RcptProof
