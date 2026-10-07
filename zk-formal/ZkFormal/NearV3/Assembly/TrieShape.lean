import NearSpec.TrieUpsertProofs

namespace ZkFormal.NearV3.Assembly
open NearSpec

/- Lookup preservation only needs valid stored nibble paths and recursively
 valid revealed children. It does not depend on memory bounds, slot byte bounds,
 hash widths, or even the child-list arity. -/
mutual
def TrieShape : PTrie → Prop
  | .hash _ => True
  | .leaf k _ _ => nibblesOk k=true
  | .ext k c _ => nibblesOk k=true ∧ TrieShape c
  | .branch _ cs _ => KidsShape cs
def KidsShape : Kids → Prop
  | .nil => True
  | .none cs => KidsShape cs
  | .some c cs => TrieShape c ∧ KidsShape cs
end

mutual
theorem TrieShape.of_wf : ∀ t : PTrie, t.wf=true → TrieShape t
  | .hash _,_ => trivial
  | .leaf _ _ _,h => wf_leaf h
  | .ext k c m,h => ⟨(wf_ext h).1,TrieShape.of_wf c (wf_ext h).2⟩
  | .branch _ cs _,h => KidsShape.of_wf cs 16 (wf_branch h)
theorem KidsShape.of_wf : ∀ cs : Kids, ∀ n, cs.wf n=true → KidsShape cs
  | .nil,_,_ => trivial
  | .none cs,n,h => KidsShape.of_wf cs (n-1) (wf_kids_none h)
  | .some c cs,n,h => ⟨TrieShape.of_wf c (wf_kids_some h).1,KidsShape.of_wf cs (n-1) (wf_kids_some h).2⟩
end

/- Adapted from frozen NearSpec/TrieUpsertProofs.lean find_upsert_other:
 source SHA256 eae1d423a69555fb819815b74510de1b5402bf39e0fc15f37cf8a9c5129442c4.
 Only the wf premise/projections and recursive theorem names change. The native
 upsert/find functions and split helper proofs are reused unchanged. -/
mutual
/-- After `upsert k v`, every other key looks up exactly as before. -/
theorem shape_find_upsert_other : ∀ (t : PTrie) (key key' : List Nat) (v : Bytes) (t' : PTrie),
    TrieShape t → nibblesOk key = true → key' ≠ key → t.upsert key v = some t' →
    t'.find key' = t.find key'
  | .hash _, _, _, _, _, _, _, _, h => by simp [PTrie.upsert] at h
  | .leaf k s m, key, key', v, t', hw, hk, hne, h => by
    simp only [PTrie.upsert] at h
    by_cases e : k = key
    · simp only [e, ↓reduceIte, Option.some.injEq] at h; subst h e
      rw [find_newLeaf, find_leaf]
      simp [Ne.symm hne]
    · simp only [e, ↓reduceIte, Option.some.injEq] at h; subst h
      exact find_splitLeaf_other s v m hw hk e hne
  | .ext k c m, key, key', v, t', hw, hk, hne, h => by
    simp only [PTrie.upsert] at h
    by_cases hp : isPrefix k key = true
    · simp only [hp, ↓reduceIte] at h
      cases hm : c.mem? <;> cases hu : c.upsert (key.drop k.length) v <;> simp [hm, hu] at h
      subst h
      rw [find_ext, find_ext]
      by_cases hp' : isPrefix k key' = true
      · simp only [hp', ↓reduceIte]
        obtain ⟨a, rfl⟩ := (isPrefix_iff _ _).1 hp
        obtain ⟨b, rfl⟩ := (isPrefix_iff _ _).1 hp'
        rw [drop_append_length] at hu ⊢
        have hab : b ≠ a := fun e => hne (by rw [e])
        exact shape_find_upsert_other c a b v _ hw.2
          (nibblesOk_append.1 hk).2 hab hu
      · simp [hp']
    · have hp' : isPrefix k key = false := by simpa using hp
      simp only [hp', Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h; subst h
      exact find_splitExt_other c m v hw.1 hk hp' hne
  | .branch bv cs m, [], key', v, t', _, _, hne, h => by
    simp only [PTrie.upsert, Option.some.injEq] at h; subst h
    cases key' with
    | nil => exact absurd rfl hne
    | cons n' rest' => simp [find_branch_cons]
  | .branch bv cs m, n :: rest, key', v, t', hw, hk, hne, h => by
    simp only [PTrie.upsert] at h
    cases hu : Kids.upsert cs n rest v with
    | none => simp [hu] at h
    | some r =>
      simp only [hu, Option.map_some, Option.some.injEq] at h; subst h
      cases key' with
      | nil => simp [find_branch_nil]
      | cons n' rest' =>
        rw [find_branch_cons, find_branch_cons]
        exact shape_kids_find_upsert_other cs 16 n rest n' rest' v r.1 r.2.1 r.2.2 hw
          (nibblesOk_cons.1 hk).2 hne hu

theorem shape_kids_find_upsert_other : ∀ (cs : Kids) (cnt n : Nat) (key : List Nat) (n' : Nat)
    (key' : List Nat) (v : Bytes) (cs' : Kids) (a b : Nat),
    KidsShape cs → nibblesOk key = true → (n' :: key') ≠ (n :: key) →
    Kids.upsert cs n key v = some (cs', a, b) → Kids.find cs' n' key' = Kids.find cs n' key'
  | .nil, _, _, _, _, _, _, _, _, _, _, _, _, h => by simp [Kids.upsert] at h
  | .none r, _, 0, key, n', key', v, cs', a, b, _, _, hne, h => by
    simp only [Kids.upsert, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, -⟩ := h
    cases n' with
    | zero =>
      simp only [Kids.find, find_newLeaf]
      have : key ≠ key' := fun e => hne (by rw [e])
      simp [this]
    | succ j => simp [Kids.find]
  | .some c r, cnt, 0, key, n', key', v, cs', a, b, hw, hk, hne, h => by
    simp only [Kids.upsert] at h
    cases hm : c.mem? <;> cases hu : c.upsert key v <;> simp [hm, hu] at h
    obtain ⟨rfl, -, -⟩ := h
    cases n' with
    | zero =>
      simp only [Kids.find]
      have : key' ≠ key := fun e => hne (by rw [e])
      exact shape_find_upsert_other c key key' v _ hw.1 hk this hu
    | succ j => simp [Kids.find]
  | .none r, cnt, i + 1, key, n', key', v, cs', a, b, hw, hk, hne, h => by
    simp only [Kids.upsert] at h
    cases hu : Kids.upsert r i key v with
    | none => simp [hu] at h
    | some x =>
      simp only [hu, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      cases n' with
      | zero => simp [Kids.find]
      | succ j =>
        simp only [Kids.find]
        have : (j :: key') ≠ (i :: key) := fun e => hne (by simp at e; simp [e])
        exact shape_kids_find_upsert_other r (cnt - 1) i key j key' v x.1 x.2.1 x.2.2 hw
          hk this hu
  | .some c r, cnt, i + 1, key, n', key', v, cs', a, b, hw, hk, hne, h => by
    simp only [Kids.upsert] at h
    cases hu : Kids.upsert r i key v with
    | none => simp [hu] at h
    | some x =>
      simp only [hu, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      cases n' with
      | zero => simp [Kids.find]
      | succ j =>
        simp only [Kids.find]
        have : (j :: key') ≠ (i :: key) := fun e => hne (by simp at e; simp [e])
        exact shape_kids_find_upsert_other r (cnt - 1) i key j key' v x.1 x.2.1 x.2.2
          hw.2 hk this hu
end

end ZkFormal.NearV3.Assembly
