import StateM5a.Walk

/-!
# StateM5a.SerInj — the node serialization is injective (`NodeSerInj`, proved)

`Walk.NodeSerInj` says: two well-formed revealed nodes with equal serializations
(`RawTrieNodeWithSize`, `Walk.ser`), the first one a row's node (`Shallow`: children are hash
stubs, the value slot a `ValueRef`), are related by `refinedBy`.  Proved here from the spec's
encoder alone:

* the tag byte separates leaf (`0`), branch without / with value (`1` / `2`), extension (`3`);
* `u16` / `u32` / `u64` are injective below `2^16` / `2^32` / `2^64` (`leN_inj`), the bounds
  `PTrie.wf` carries (the bitmap bound from `Kids.wf cs 16`, `kidsBitmap_lt`);
* `hexPrefix k b` is injective on nibble lists (`hexPrefix_inj`: the parity bit of the first
  byte, then `packNibbles` on an even-length list, `packNibbles_inj`);
* every child hash is 32 bytes (`hashOf_length`: `sha256_length` or `wf` of a stub), so the
  bitmap and the children block split slot by slot (`kids_inj`);
* a `ValueRef` determines a slot up to `SlotRefines` (`slot_of_valueRef`).

So `refinedBy_of_hash` needs only `Sha256CR` (`refinedBy_of_hash'`).
-/

namespace StateM5a.SerInj

open NearSpec NearSpecV3.D2 StateM5a.Walk

/-! ## Fixed-width integers -/

theorem leN_len : ∀ (w x : Nat), (leN w x).length = w
  | 0, _ => rfl
  | w + 1, x => by simp [leN, leN_len w]

theorem ofNat_toNat (a : Nat) : (UInt8.ofNat a).toNat = a % 256 := by simp

theorem leN_inj : ∀ (w a b : Nat), leN w a = leN w b → a < 256 ^ w → b < 256 ^ w → a = b
  | 0, a, b, _, ha, hb => by simp at ha hb; omega
  | w + 1, a, b, h, ha, hb => by
    simp only [leN, List.cons.injEq] at h
    have h0 := congrArg UInt8.toNat h.1
    rw [ofNat_toNat, ofNat_toNat] at h0
    rw [Nat.pow_succ] at ha hb
    have := leN_inj w (a / 256) (b / 256) h.2 (by omega) (by omega)
    omega

/-! ## Hash lengths -/

theorem hashOf_length (t : PTrie) (hw : t.wf = true) : t.hashOf.length = 32 := by
  cases t with
  | hash h => simpa [PTrie.wf, PTrie.hashOf] using hw
  | leaf => simp [PTrie.hashOf, ArenaCore.sha256_length]
  | ext => simp [PTrie.hashOf, ArenaCore.sha256_length]
  | branch v cs m => cases v <;> simp [PTrie.hashOf, ArenaCore.sha256_length]

theorem valueRef_length (s : Slot) (hs : slotOk s = true) : s.valueRef.length = 36 := by
  cases s with
  | val v => simp [Slot.valueRef, u32, leN_len, ArenaCore.sha256_length]
  | ref len h =>
    simp only [slotOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hs
    simp [Slot.valueRef, u32, leN_len, hs.2]

/-- A row's `ValueRef` slot and any well-formed slot with the same `valueRef` bytes. -/
theorem slot_of_valueRef (len : Nat) (h : Bytes) (s₂ : Slot) (h₁ : slotOk (.ref len h) = true)
    (h₂ : slotOk s₂ = true) (he : (Slot.ref len h).valueRef = s₂.valueRef) :
    SlotRefines (.ref len h) s₂ := by
  simp only [slotOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h₁
  cases s₂ with
  | val v =>
    simp only [slotOk, decide_eq_true_eq] at h₂
    simp only [Slot.valueRef] at he
    obtain ⟨hl, hh⟩ := List.append_inj he (by simp [u32, leN_len])
    have := leN_inj 4 len v.length hl (by omega) (by omega)
    subst this; subst hh
    exact Or.inr ⟨v, rfl, rfl⟩
  | ref len₂ h₂' =>
    simp only [slotOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h₂
    simp only [Slot.valueRef] at he
    obtain ⟨hl, hh⟩ := List.append_inj he (by simp [u32, leN_len])
    have := leN_inj 4 len len₂ hl (by omega) (by omega)
    subst this; subst hh
    exact Or.inl rfl

/-! ## `hexPrefix` -/

theorem packNibbles_inj : ∀ (k₁ k₂ : List Nat), (∀ x ∈ k₁, x < 16) → (∀ x ∈ k₂, x < 16) →
    k₁.length % 2 = 0 → k₂.length % 2 = 0 → packNibbles k₁ = packNibbles k₂ → k₁ = k₂
  | [], [], _, _, _, _, _ => rfl
  | [], [_], _, _, _, h, _ => by simp at h
  | [], _ :: _ :: _, _, _, _, _, h => by simp [packNibbles] at h
  | [_], _, _, _, h, _, _ => by simp at h
  | _ :: _ :: _, [], _, _, _, _, h => by simp [packNibbles] at h
  | _ :: _ :: _, [_], _, _, _, h, _ => by simp at h
  | a :: b :: r₁, c :: d :: r₂, n₁, n₂, l₁, l₂, h => by
    simp only [packNibbles, List.cons.injEq] at h
    have h0 := congrArg UInt8.toNat h.1
    rw [ofNat_toNat, ofNat_toNat] at h0
    have ha := n₁ a (by simp); have hb := n₁ b (by simp)
    have hc := n₂ c (by simp); have hd := n₂ d (by simp)
    have hac : a = c := by omega
    have hbd : b = d := by omega
    subst hac; subst hbd
    have := packNibbles_inj r₁ r₂ (fun x hx => n₁ x (by simp [hx])) (fun x hx => n₂ x (by simp [hx]))
      (by simp at l₁; omega) (by simp at l₂; omega) h.2
    rw [this]

theorem hexPrefix_cases (k : List Nat) (b : Bool) :
    (∃ n rest, k = n :: rest ∧ k.length % 2 = 1 ∧
      hexPrefix k b = UInt8.ofNat (16 + n + (if b then 32 else 0)) :: packNibbles rest) ∨
    (k.length % 2 = 0 ∧ hexPrefix k b = UInt8.ofNat (if b then 32 else 0) :: packNibbles k) := by
  cases k with
  | nil => right; simp [hexPrefix]
  | cons n rest =>
    rcases Nat.mod_two_eq_zero_or_one (n :: rest).length with h | h
    · right
      refine ⟨h, ?_⟩
      unfold hexPrefix
      simp only [h]
    · left
      refine ⟨n, rest, rfl, h, ?_⟩
      unfold hexPrefix
      simp only [h]

/-- `hexPrefix` with a fixed leaf flag is injective on nibble lists. -/
theorem hexPrefix_inj (k₁ k₂ : List Nat) (b : Bool) (n₁ : ∀ x ∈ k₁, x < 16) (n₂ : ∀ x ∈ k₂, x < 16)
    (h : hexPrefix k₁ b = hexPrefix k₂ b) : k₁ = k₂ := by
  have hb : (if b then 32 else 0) < 33 := by split <;> omega
  rcases hexPrefix_cases k₁ b with ⟨a, r₁, rfl, l₁, e₁⟩ | ⟨l₁, e₁⟩ <;>
    rcases hexPrefix_cases k₂ b with ⟨c, r₂, rfl, l₂, e₂⟩ | ⟨l₂, e₂⟩ <;>
    rw [e₁, e₂, List.cons.injEq] at h <;> have h0 := congrArg UInt8.toNat h.1 <;>
    simp only [ofNat_toNat] at h0
  · have ha := n₁ a (by simp); have hc := n₂ c (by simp)
    have hac : a = c := by omega
    subst hac
    rw [packNibbles_inj r₁ r₂ (fun x hx => n₁ x (by simp [hx])) (fun x hx => n₂ x (by simp [hx]))
      (by simp at l₁; omega) (by simp at l₂; omega) h.2]
  · have ha := n₁ a (by simp); omega
  · have hc := n₂ c (by simp); omega
  · exact packNibbles_inj k₁ k₂ n₁ n₂ l₁ l₂ h.2

/-! ## Children: bitmap and hash block -/

theorem kidsBitmap_shift : ∀ (cs : Kids) (i : Nat), kidsBitmap cs i = 2 ^ i * kidsBitmap cs 0
  | .nil, i => by simp [kidsBitmap]
  | .none r, i => by
    simp only [kidsBitmap]
    rw [kidsBitmap_shift r (i + 1), kidsBitmap_shift r 1, Nat.pow_succ, Nat.pow_one, Nat.mul_assoc]
  | .some _ r, i => by
    simp only [kidsBitmap]
    rw [kidsBitmap_shift r (i + 1), kidsBitmap_shift r 1, Nat.pow_succ, Nat.pow_one, Nat.pow_zero,
      Nat.mul_add, Nat.mul_one, Nat.mul_assoc]

theorem kidsBitmap_lt : ∀ (cs : Kids) (n : Nat), Kids.wf cs n = true → kidsBitmap cs 0 < 2 ^ n
  | .nil, n, h => by
    simp only [Kids.wf, beq_iff_eq] at h; subst h; simp [kidsBitmap]
  | .none r, n, h => by
    simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    have := kidsBitmap_lt r (n - 1) h.2
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [kidsBitmap]; rw [kidsBitmap_shift r 1, Nat.pow_succ]
    simp only [Nat.add_sub_cancel] at this
    omega
  | .some _ r, n, h => by
    simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    have := kidsBitmap_lt r (n - 1) h.2
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [kidsBitmap]; rw [kidsBitmap_shift r 1, Nat.pow_succ]
    simp only [Nat.add_sub_cancel] at this
    omega

/-- Equal bitmaps and equal children blocks (followed by anything): the row's stub children
refine the other node's children slot by slot, and the tails agree. -/
theorem kids_inj : ∀ (cs₁ cs₂ : Kids) (n : Nat) (X₁ X₂ : Bytes),
    Kids.wf cs₁ n = true → Kids.wf cs₂ n = true →
    (∀ j c, Kids.at cs₁ j = some c → ∃ h, c = .hash h) →
    kidsBitmap cs₁ 0 = kidsBitmap cs₂ 0 →
    Kids.hashes cs₁ ++ X₁ = Kids.hashes cs₂ ++ X₂ →
    Kids.refinedBy cs₁ cs₂ ∧ X₁ = X₂
  | .nil, .nil, _, X₁, X₂, _, _, _, _, he => by simpa [Kids.refinedBy, Kids.hashes] using he
  | .nil, .none _, n, _, _, w₁, w₂, _, _, _ => by
    simp only [Kids.wf, beq_iff_eq, Bool.and_eq_true, bne_iff_ne, ne_eq] at w₁ w₂; omega
  | .nil, .some _ _, n, _, _, w₁, w₂, _, _, _ => by
    simp only [Kids.wf, beq_iff_eq, Bool.and_eq_true, bne_iff_ne, ne_eq] at w₁ w₂; omega
  | .none _, .nil, n, _, _, w₁, w₂, _, _, _ => by
    simp only [Kids.wf, beq_iff_eq, Bool.and_eq_true, bne_iff_ne, ne_eq] at w₁ w₂; omega
  | .some _ _, .nil, n, _, _, w₁, w₂, _, _, _ => by
    simp only [Kids.wf, beq_iff_eq, Bool.and_eq_true, bne_iff_ne, ne_eq] at w₁ w₂; omega
  | .none r₁, .some _ r₂, _, _, _, _, _, _, hb, _ => by
    simp only [kidsBitmap] at hb
    rw [kidsBitmap_shift r₁ 1, kidsBitmap_shift r₂ 1] at hb; simp at hb; omega
  | .some _ r₁, .none r₂, _, _, _, _, _, _, hb, _ => by
    simp only [kidsBitmap] at hb
    rw [kidsBitmap_shift r₁ 1, kidsBitmap_shift r₂ 1] at hb; simp at hb; omega
  | .none r₁, .none r₂, n, X₁, X₂, w₁, w₂, hs, hb, he => by
    simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne, ne_eq] at w₁ w₂
    simp only [kidsBitmap] at hb
    rw [kidsBitmap_shift r₁ 1, kidsBitmap_shift r₂ 1] at hb
    simp only [Kids.hashes] at he
    have := kids_inj r₁ r₂ (n - 1) X₁ X₂ w₁.2 w₂.2 (fun j c h => hs (j + 1) c h) (by omega) he
    simpa [Kids.refinedBy] using this
  | .some c₁ r₁, .some c₂ r₂, n, X₁, X₂, w₁, w₂, hs, hb, he => by
    simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne, ne_eq] at w₁ w₂
    simp only [kidsBitmap] at hb
    rw [kidsBitmap_shift r₁ 1, kidsBitmap_shift r₂ 1] at hb
    simp only [Kids.hashes, List.append_assoc] at he
    obtain ⟨hh, ht⟩ := List.append_inj he
      (by rw [hashOf_length c₁ w₁.1.2, hashOf_length c₂ w₂.1.2])
    have := kids_inj r₁ r₂ (n - 1) X₁ X₂ w₁.2 w₂.2 (fun j c h => hs (j + 1) c h) (by omega) ht
    obtain ⟨h, rfl⟩ := hs 0 c₁ rfl
    simp only [PTrie.hashOf] at hh
    exact ⟨⟨hh, this.1⟩, this.2⟩

/-! ## `NodeSerInj` -/

theorem nibblesOk_iff (k : List Nat) : nibblesOk k = true ↔ ∀ x ∈ k, x < 16 := by
  simp [nibblesOk]

/-- **The node serialization is injective** (on well-formed nodes, the first a row's node). -/
theorem nodeSerInj : NodeSerInj := by
  intro n₁ n₂ hw₁ hw₂ hn₁ hn₂ hs he
  cases n₁ with
  | hash h => exact absurd rfl (hn₁ h)
  | leaf k s m =>
    obtain ⟨len, hh, rfl⟩ := hs
    cases n₂ with
    | hash h => exact absurd rfl (hn₂ h)
    | ext => simp [ser] at he
    | branch v => cases v <;> simp [ser] at he
    | leaf k₂ s₂ m₂ =>
      simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq, nibblesOk_iff] at hw₁ hw₂
      simp only [ser] at he
      obtain ⟨he, hm⟩ := List.append_inj' he (by simp [u64, leN_len])
      obtain ⟨he, hv⟩ := List.append_inj' he
        (by rw [valueRef_length _ hw₁.1.1.2, valueRef_length _ hw₂.1.1.2])
      obtain ⟨-, hp⟩ := List.append_inj he (by simp [u32, leN_len])
      simp only [PTrie.refinedBy]
      refine ⟨hexPrefix_inj k k₂ true hw₁.1.1.1 hw₂.1.1.1 hp,
        leN_inj 8 m m₂ hm (by simp only [Nat.reducePow]; omega) (by simp only [Nat.reducePow]; omega),
        slot_of_valueRef len hh s₂ hw₁.1.1.2 hw₂.1.1.2 hv⟩
  | ext k c m =>
    obtain ⟨h, rfl⟩ := hs
    cases n₂ with
    | hash h => exact absurd rfl (hn₂ h)
    | leaf => simp [ser] at he
    | branch v => cases v <;> simp [ser] at he
    | ext k₂ c₂ m₂ =>
      simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq, nibblesOk_iff] at hw₁ hw₂
      simp only [ser] at he
      obtain ⟨he, hm⟩ := List.append_inj' he (by simp [u64, leN_len])
      obtain ⟨he, hc⟩ := List.append_inj' he
        (by rw [hashOf_length _ hw₂.1.1.2]; simpa [PTrie.hashOf] using hw₁.1.1.2)
      obtain ⟨-, hp⟩ := List.append_inj he (by simp [u32, leN_len])
      simp only [PTrie.refinedBy]
      refine ⟨hexPrefix_inj k k₂ false hw₁.1.1.1 hw₂.1.1.1 hp,
        leN_inj 8 m m₂ hm (by simp only [Nat.reducePow]; omega) (by simp only [Nat.reducePow]; omega),
        by simpa [PTrie.hashOf] using hc⟩
  | branch v cs m =>
    obtain ⟨hsv, hsk⟩ := hs
    cases n₂ with
    | hash h => exact absurd rfl (hn₂ h)
    | leaf => cases v <;> simp [ser] at he
    | ext => cases v <;> simp [ser] at he
    | branch v₂ cs₂ m₂ =>
      cases v with
      | none =>
        cases v₂ with
        | some => simp [ser] at he
        | none =>
          simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq] at hw₁ hw₂
          simp only [ser] at he
          obtain ⟨he, hm⟩ := List.append_inj' he (by simp [u64, leN_len])
          obtain ⟨hb, hk⟩ := List.append_inj he (by simp [u16, leN_len])
          simp only [List.singleton_append, List.cons.injEq, true_and] at hb
          have hbm := leN_inj 2 _ _ hb (kidsBitmap_lt cs 16 hw₁.1.2) (kidsBitmap_lt cs₂ 16 hw₂.1.2)
          have := kids_inj cs cs₂ 16 [] [] hw₁.1.2 hw₂.1.2 hsk hbm (by simpa using hk)
          simp only [PTrie.refinedBy]
          exact ⟨leN_inj 8 m m₂ hm (by simp only [Nat.reducePow]; omega)
            (by simp only [Nat.reducePow]; omega), trivial, this.1⟩
      | some s =>
        cases v₂ with
        | none => simp [ser] at he
        | some s₂ =>
          obtain ⟨len, hh, rfl⟩ := hsv _ rfl
          simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq] at hw₁ hw₂
          simp only [ser] at he
          obtain ⟨he, hm⟩ := List.append_inj' he (by simp [u64, leN_len])
          obtain ⟨he, hk⟩ := List.append_inj he
            (by simp only [List.length_append, u16, leN_len,
                  valueRef_length _ hw₁.1.1, valueRef_length _ hw₂.1.1])
          obtain ⟨hv, hb⟩ := List.append_inj' he (by simp [u16, leN_len])
          simp only [List.singleton_append, List.cons.injEq, true_and] at hv
          have hbm := leN_inj 2 _ _ hb (kidsBitmap_lt cs 16 hw₁.1.2) (kidsBitmap_lt cs₂ 16 hw₂.1.2)
          have := kids_inj cs cs₂ 16 [] [] hw₁.1.2 hw₂.1.2 hsk hbm (by simpa using hk)
          simp only [PTrie.refinedBy]
          exact ⟨leN_inj 8 m m₂ hm (by simp only [Nat.reducePow]; omega)
            (by simp only [Nat.reducePow]; omega),
            slot_of_valueRef len hh s₂ hw₁.1.1 hw₂.1.1 hv, this.1⟩

/-- `refinedBy_of_hash` with `NodeSerInj` discharged: only `Sha256CR` remains. -/
theorem refinedBy_of_hash' (hCR : Sha256CR) {n₁ n₂ : PTrie}
    (hw₁ : n₁.wf = true) (hw₂ : n₂.wf = true) (h₁ : ∀ h, n₁ ≠ .hash h) (h₂ : ∀ h, n₂ ≠ .hash h)
    (hs : Shallow n₁) (hh : n₁.hashOf = n₂.hashOf) : n₁.refinedBy n₂ :=
  refinedBy_of_hash hCR nodeSerInj hw₁ hw₂ h₁ h₂ hs hh

end StateM5a.SerInj
