import ZkFormal.Near.Link.Streams

/-!
# ZkFormal.Near.Link.RcptFacts — per-receipt facts from `RcptV.Wf`

Lengths, canonical values and length bounds of the receipt-side messages.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false

namespace Link

theorem valid_length {s : Bytes} (h : AccountId.valid s = true) : 2 ≤ s.length ∧ s.length ≤ 64 := by
  simp only [AccountId.valid, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2⟩

theorem toBytes_length (l : List Nat) : (toBytes l).length = l.length := List.length_map _

/-- Account-id lengths of a receipt. -/
theorem idLens {x : RcptV} {r a b c : Nat} (w : x.Wf r a b c) :
    x.p.length ≤ 64 ∧ x.v.length ≤ 64 ∧ x.s.length ≤ 64 := by
  obtain ⟨h1, h2, h3, -⟩ := w.ids
  have := valid_length h1; have := valid_length h2; have := valid_length h3
  simp only [toBytes_length] at *
  omega

/-- The `RcptWf` per-receipt facts, with the running token amounts. -/
theorem rcptWf_at {pub : List Fp} {rs : RcptVs} (h : RcptWf pub rs) :
    ∃ toks : List Nat, toks.length = rs.length + 1 ∧ toks.head? = some 0 ∧
      (∀ r (hr : r < rs.length), rs[r].Wf r (leN' (pubBytes pub PV_BGP 16)) (toks.getD r 0)
        (toks.getD (r + 1) 0)) ∧
      ((∀ i, i < 16 → pubNat pub (PV_TOK + i) < 256) →
        toks.getD rs.length 0 = leN' (pubBytes pub PV_TOK 16)) := h.toks

/-- Values of the receipt-side messages: raw or bytes. -/
def RawOrByte (x : RcptV) (l : List Nat) : Prop := ∀ y ∈ l, y ∈ x.raw ∨ y < 256

theorem rawOrByte_append {x : RcptV} {l₁ l₂ : List Nat} (h₁ : RawOrByte x l₁) (h₂ : RawOrByte x l₂) :
    RawOrByte x (l₁ ++ l₂) := by
  intro y hy; rcases List.mem_append.mp hy with h | h
  · exact h₁ y h
  · exact h₂ y h

theorem rawOrByte_const {x : RcptV} {l : List Nat} (h : ∀ y ∈ l, y < 256) : RawOrByte x l :=
  fun y hy => .inr (h y hy)

theorem rawOrByte_raw {x : RcptV} {l : List Nat} (h : ∀ y ∈ l, y ∈ x.raw) : RawOrByte x l :=
  fun y hy => .inl (h y hy)

theorem rawOrByte_borsh {x : RcptV} {l : List Nat} (hl : l.length ≤ 64) (h : ∀ y ∈ l, y ∈ x.raw) :
    RawOrByte x (RcptV.borshN l) := by
  refine rawOrByte_append (rawOrByte_const ?_) (rawOrByte_raw h)
  intro y hy; rcases mem_u32r hy with rfl | rfl <;> omega

section
variable {x : RcptV} {r a b c : Nat} (w : x.Wf r a b c)
include w

macro "rob" : tactic => `(tactic| (
  repeat' apply rawOrByte_append
  all_goals first
    | (apply rawOrByte_raw; intro y hy; simp [RcptV.raw, hy]; done)
    | (apply rawOrByte_raw; intro y hy; simp at hy; subst hy; simp [RcptV.raw]; done)
    | (apply rawOrByte_const; decide)
    | (apply rawOrByte_const; intro y hy; rcases mem_u32r hy with rfl | rfl <;> omega)
    | (apply rawOrByte_const; intro y hy; simp at hy; omega)))

theorem enc_vals : RawOrByte x x.enc := by
  obtain ⟨hp, hv, hs⟩ := idLens w
  unfold RcptV.enc; rob

theorem encRefund_vals : RawOrByte x x.encRefund := by
  obtain ⟨hp, hv, hs⟩ := idLens w
  unfold RcptV.encRefund; rob

theorem peo_vals : RawOrByte x x.peo := by
  obtain ⟨hp, hv, hs⟩ := idLens w
  unfold RcptV.peo
  cases x.hr <;> simp only [Bool.false_eq_true, if_false, if_true, List.append_nil] <;> rob

omit w in
theorem leaf_vals : RawOrByte x x.leaf := by
  unfold RcptV.leaf; rob

omit w in
theorem ridMsg_vals {pub : List Fp} (hpub : ∀ j, pubNat pub j < 256) : RawOrByte x (ridMsg pub x) := by
  intro y hy
  simp only [ridMsg, List.mem_append] at hy
  rcases hy with (hy | hy) | hy
  · left; simp [RcptV.raw, hy]
  · right; simp only [pubBytes, List.mem_map] at hy; obtain ⟨j, -, rfl⟩ := hy; exact hpub _
  · right; rw [List.mem_replicate] at hy; omega

theorem enc_length : x.enc.length ≤ 400 := by
  obtain ⟨hp, hv, hs⟩ := idLens w
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := w.lens
  simp [RcptV.enc, RcptV.borshN, u32r, tailN, h1, h2, h4, h5]; omega

theorem encRefund_length : x.encRefund.length ≤ 400 := by
  obtain ⟨hp, hv, hs⟩ := idLens w
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := w.lens
  simp [RcptV.encRefund, RcptV.borshN, u32r, tailN, systemN, h2, h11, h12]; omega

theorem peo_length : x.peo.length ≤ 400 := by
  obtain ⟨hp, hv, hs⟩ := idLens w
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := w.lens
  simp [RcptV.peo, RcptV.borshN, u32r, G_LEn, h10, h12]; split <;> (try simp) <;> omega

theorem leaf_length : x.leaf.length = 68 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := w.lens
  simp [RcptV.leaf, h1, h13]

theorem ridMsg_length (pub : List Fp) : (ridMsg pub x).length = 48 := by
  obtain ⟨h1, -⟩ := w.lens
  simp [ridMsg, h1, pubBytes_length]

end

end Link

end ZkFormal.Near
