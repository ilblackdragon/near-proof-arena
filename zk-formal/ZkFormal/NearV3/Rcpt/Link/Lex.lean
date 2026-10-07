import ZkFormal.NearV3.Rcpt.Extract.RcptView

/-!
# ZkFormal.NearV3.Rcpt.Link.Lex — byte-wise comparison against padded boundaries

The routing rows of `rcptV3` compare the receiver `v` position by position with a boundary
padded by the end marker `0` (account-id bytes are `≥ 1`), and the receiver itself is
padded by `0` at position `|v|`.  While the prefixes are equal:
* `lo_i ≤ v_i` at every position `i ≤ |v|` gives `lexLe lo v` (`lex_lo`);
* `v_i ≤ hi_i`, strictly at `i = |v|`, gives `¬ lexLe hi v` (`lex_hi`).
-/

namespace ZkFormal.NearV3

open ZkFormal.Near

theorem toBytes_cons (a : Nat) (l : List Nat) : toBytes (a :: l) = UInt8.ofNat a :: toBytes l := rfl

theorem u8_lt {a b : Nat} (ha : a < 256) (hb : b < 256) : (UInt8.ofNat a < UInt8.ofNat b) ↔ a < b := by
  rw [UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat', UInt8.toNat_ofNat', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem u8_eq {a b : Nat} (ha : a < 256) (hb : b < 256) : (UInt8.ofNat a == UInt8.ofNat b) = decide (a = b) := by
  have : UInt8.ofNat a = UInt8.ofNat b ↔ a = b := by
    constructor
    · intro h; have := congrArg UInt8.toNat h
      rwa [UInt8.toNat_ofNat', UInt8.toNat_ofNat', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
    · intro h; rw [h]
  by_cases h : a = b <;> simp [h, this]

/-- **`lo ≤ v`** from the position-wise checks while equal. -/
theorem lex_lo : ∀ (lo v : List Nat), (∀ y ∈ lo, 0 < y ∧ y < 256) → (∀ y ∈ v, 0 < y ∧ y < 256) →
    (∀ i, i ≤ v.length → (∀ k, k < i → padB v k = padB lo k) → padB lo i ≤ padB v i) →
    NearSpecV3.lexLe (toBytes lo) (toBytes v) = true
  | [], _, _, _, _ => by simp [toBytes, NearSpecV3.lexLe]
  | a :: lo, [], hlo, _, h => by
    have := h 0 (by simp) (fun k hk => by omega)
    have ha := hlo a (by simp)
    simp [padB] at this; omega
  | a :: lo, x :: v, hlo, hv, h => by
    have ha := hlo a (by simp); have hx := hv x (by simp)
    have h0 := h 0 (by simp) (fun k hk => by omega)
    simp only [padB, List.getD_cons_zero] at h0
    simp only [toBytes_cons, NearSpecV3.lexLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
      u8_lt ha.2 hx.2, u8_eq hx.2 ha.2]
    by_cases hlt : a < x
    · exact Or.inl hlt
    · have e : x = a := by omega
      subst e
      refine Or.inr ⟨by simp, lex_lo lo v (fun y hy => hlo y (by simp [hy])) (fun y hy => hv y (by simp [hy]))
        (fun i hi hk => ?_)⟩
      have := h (i + 1) (by simp; omega) (fun k hk' => by
        cases k with
        | zero => rfl
        | succ k => simpa [padB] using hk k (by omega))
      simpa [padB] using this

/-- **`v < hi`** (i.e. `¬ hi ≤ v`) from the position-wise checks while equal, strict at the end. -/
theorem lex_hi : ∀ (hi v : List Nat), (∀ y ∈ hi, 0 < y ∧ y < 256) → (∀ y ∈ v, 0 < y ∧ y < 256) →
    (∀ i, i ≤ v.length → (∀ k, k < i → padB v k = padB hi k) →
      padB v i ≤ padB hi i ∧ (i = v.length → padB v i < padB hi i)) →
    NearSpecV3.lexLe (toBytes hi) (toBytes v) = false
  | [], v, _, hv, h => by
    exfalso
    have h0 := h 0 (by omega) (fun k hk => by omega)
    cases v with
    | nil => have := h0.2 rfl; simp [padB] at this
    | cons x v => have := h0.1; have hx := hv x (by simp); simp [padB] at this; omega
  | a :: hi, [], _, _, _ => by simp [toBytes, NearSpecV3.lexLe]
  | a :: hi, x :: v, hhi, hv, h => by
    have ha := hhi a (by simp); have hx := hv x (by simp)
    have h0 := (h 0 (by simp) (fun k hk => by omega)).1
    simp only [padB, List.getD_cons_zero] at h0
    simp only [toBytes_cons, NearSpecV3.lexLe, Bool.or_eq_false_iff, decide_eq_false_iff_not,
      Bool.and_eq_false_imp, u8_lt ha.2 hx.2, u8_eq ha.2 hx.2, decide_eq_true_eq]
    refine ⟨by omega, fun e => ?_⟩
    subst e
    exact lex_hi hi v (fun y hy => hhi y (by simp [hy])) (fun y hy => hv y (by simp [hy])) (fun i hi' hk => by
      have := h (i + 1) (by simp; omega) (fun k hk' => by
        cases k with
        | zero => rfl
        | succ k => simpa [padB] using hk k (by omega))
      simp only [padB, List.getD_cons_succ, List.length_cons] at this ⊢
      exact ⟨this.1, fun e => this.2 (by omega)⟩)

end ZkFormal.NearV3
