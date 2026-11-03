import NearSpecV3.D2.State

/-!
# StateM5a.Order — `KCMP` proves the spec's key order

A `KCMP` pair `(ka, kb)` is a run of rows `j = 0..p`: for `j < p` both keys have the same nibble
`x` (two `NIB` lookups with one column), and at `p` either key `a` has ended (`KLEN(ka, p)`) while
`b` has a nibble, or `a`'s nibble is smaller (`xb − xa − 1` is a 4-bit value).  That is `NibLt` on
the keys' nibble strings, and `nibLt_bytesLt` turns it into the spec's `bytesLt` on the raw keys —
the order `sortKV` (hence `Ovl.finalize`'s `applyChanges`) applies the committed changes in.  So
consecutive working-set leaves hold strictly increasing keys: the leaves are distinct and the FINAL
walks (leaf order) apply the changes in the spec's order.
-/

namespace StateM5a.Order

open NearSpec NearSpecV3.D2

/-- The relation a `KCMP` run establishes between two nibble strings. -/
def NibLt (a b : List Nat) : Prop :=
  ∃ p, a.take p = b.take p ∧
    ((p = a.length ∧ p < b.length) ∨ ∃ x y, a[p]? = some x ∧ b[p]? = some y ∧ x < y)

theorem nibbles_length (A : Bytes) : (nibbles A).length = 2 * A.length := by
  induction A with
  | nil => rfl
  | cons x xs ih => simp only [nibbles, List.length_cons, ih]; omega

theorem byte_eq_of_nibbles {x y : UInt8} (h1 : x.toNat / 16 = y.toNat / 16)
    (h2 : x.toNat % 16 = y.toNat % 16) : x.toNat = y.toNat := by omega

theorem nibLt_bytesLt : ∀ (A B : Bytes), NibLt (nibbles A) (nibbles B) → bytesLt A B = true
  | [], [], ⟨p, _, h⟩ => by
    rcases h with ⟨_, hp⟩ | ⟨_, _, hx, _, _⟩
    · simp [nibbles] at hp
    · simp [nibbles] at hx
  | [], _ :: _, _ => rfl
  | _ :: _, [], ⟨p, _, h⟩ => by
    rcases h with ⟨_, hp⟩ | ⟨_, _, _, hy, _⟩
    · simp [nibbles] at hp
    · simp [nibbles] at hy
  | x :: xs, y :: ys, ⟨p, ht, h⟩ => by
    simp only [bytesLt]
    match p with
    | 0 =>
      rcases h with ⟨hp, _⟩ | ⟨a, b, ha, hb, hab⟩
      · simp [nibbles] at hp
      · simp only [nibbles, List.getElem?_cons_zero, Option.some.injEq] at ha hb
        subst ha; subst hb
        have : x.toNat < y.toNat := by omega
        simp [this]
    | 1 =>
      simp only [nibbles, List.take_succ_cons, List.take_zero, List.cons.injEq, and_true] at ht
      rcases h with ⟨hp, _⟩ | ⟨a, b, ha, hb, hab⟩
      · simp [nibbles] at hp
      · simp only [nibbles, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at ha hb
        subst ha; subst hb
        have : x.toNat < y.toNat := by omega
        simp [this]
    | q + 2 =>
      simp only [nibbles, List.take_succ_cons, List.cons.injEq] at ht
      obtain ⟨h1, h2, h3⟩ := ht
      have hxy := byte_eq_of_nibbles h1 h2
      have hn1 : ¬ x.toNat < y.toNat := by omega
      have hn2 : ¬ y.toNat < x.toNat := by omega
      simp only [hn1, hn2, if_false]
      apply nibLt_bytesLt xs ys
      refine ⟨q, h3, ?_⟩
      rcases h with ⟨hp, hq⟩ | ⟨a, b, ha, hb, hab⟩
      · left
        simp only [nibbles, List.length_cons] at hp hq
        exact ⟨by omega, by omega⟩
      · right
        simp only [nibbles, List.getElem?_cons_succ] at ha hb
        exact ⟨a, b, ha, hb, hab⟩

end StateM5a.Order
