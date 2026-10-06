import NearSpec.TrieUpsertProofs

/-!
# ZkFormal.NearV3.Spec.TrieOps — `TrieOpsStmt`: reads and writes on distinct keys

D0's main transition upserts `0x0f` (nibbles `[0, 15]`) *before* the receipts'
account writes and reads `[10]` *after* them (V3-D0-DESIGN §3.2.7), while the
AIR applies all writes to one pre/post node set.  This file proves the `PTrie`
facts that make the order irrelevant:

* `find_set_self`, `find_set_ne` — `set` is a map update on revealed keys;
* `find_upsert_ne` — NearSpec's `PTrie.find_upsert_other`, restated;
* `set_mem` — `set` keeps every stored `memory_usage` (in particular the root's);
* **`set_upsert_comm`** — for distinct keys, a same-length `set` commutes with
  `upsert` *exactly* (the two orders produce the same `PTrie`, so the same
  root hash): `t.set k₁ v₁ = some t₁ → t.upsert k₂ v₂ = some t₂ →
  ∃ t₁₂, t₁.upsert k₂ v₂ = some t₁₂ ∧ t₂.set k₁ v₁ = some t₁₂`.
  Same length matters: when `upsert` splits the leaf of `k₁`, the moved leaf's
  `memory_usage` is computed from the value length at that moment.
-/

namespace ZkFormal.NearV3

open NearSpec

/-! ## `set` as a map update -/

theorem set_mem : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (t' : PTrie),
    t.set key v = some t' → t'.mem? = t.mem?
  | .hash _, _, _, _, h => by simp [PTrie.set] at h
  | .leaf k s m, key, v, t', h => by
    simp only [PTrie.set] at h
    split at h
    · cases hs : s.get <;> simp [hs] at h; subst h; rfl
    · simp at h
  | .ext k c m, key, v, t', h => by
    simp only [PTrie.set] at h
    split at h
    · cases hs : c.set (key.drop k.length) v <;> simp [hs] at h; subst h; rfl
    · simp at h
  | .branch bv cs m, [], v, t', h => by
    simp only [PTrie.set] at h
    split at h <;> simp at h; subst h; rfl
  | .branch bv cs m, n :: rest, v, t', h => by
    simp only [PTrie.set] at h
    cases hs : Kids.set cs n rest v <;> simp [hs] at h; subst h; rfl

theorem set_memD {t : PTrie} {key : List Nat} {v : Bytes} {t' : PTrie}
    (h : t.set key v = some t') : t'.memD = t.memD := by
  simp [PTrie.memD, set_mem t key v t' h]

mutual
theorem PTrie.find_set_self : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (t' : PTrie),
    t.set key v = some t' → t'.find key = some (some v)
  | .hash _, _, _, _, h => by simp [PTrie.set] at h
  | .leaf k s m, key, v, t', h => by
    simp only [PTrie.set] at h
    split at h
    · rename_i e
      have e' : k = key := by simpa using e
      subst e'
      cases hs : s.get <;> simp [hs] at h; subst h; simp [PTrie.find, Slot.get]
    · simp at h
  | .ext k c m, key, v, t', h => by
    simp only [PTrie.set] at h
    split at h
    · rename_i hp
      cases hs : c.set (key.drop k.length) v <;> simp [hs] at h; subst h
      simp [PTrie.find, hp, PTrie.find_set_self c _ v _ hs]
    · simp at h
  | .branch bv cs m, [], v, t', h => by
    simp only [PTrie.set] at h
    split at h <;> simp at h; subst h; simp [PTrie.find, Slot.get]
  | .branch bv cs m, n :: rest, v, t', h => by
    simp only [PTrie.set] at h
    cases hs : Kids.set cs n rest v <;> simp [hs] at h; subst h
    simp only [PTrie.find]; exact Kids.find_set_self cs n rest v _ hs
theorem Kids.find_set_self : ∀ (cs : Kids) (n : Nat) (key : List Nat) (v : Bytes) (cs' : Kids),
    Kids.set cs n key v = some cs' → Kids.find cs' n key = some (some v)
  | .nil, _, _, _, _, h => by simp [Kids.set] at h
  | .none _, 0, _, _, _, h => by simp [Kids.set] at h
  | .some c r, 0, key, v, cs', h => by
    simp only [Kids.set] at h
    cases hs : c.set key v <;> simp [hs] at h; subst h
    simp only [Kids.find]; exact PTrie.find_set_self c key v _ hs
  | .none r, i + 1, key, v, cs', h => by
    simp only [Kids.set] at h
    cases hs : Kids.set r i key v <;> simp [hs] at h; subst h
    simp only [Kids.find]; exact Kids.find_set_self r i key v _ hs
  | .some c r, i + 1, key, v, cs', h => by
    simp only [Kids.set] at h
    cases hs : Kids.set r i key v <;> simp [hs] at h; subst h
    simp only [Kids.find]; exact Kids.find_set_self r i key v _ hs
end

mutual
/-- **`find_set_ne`**: a `set` does not change the lookup of any other key. -/
theorem PTrie.find_set_ne : ∀ (t : PTrie) (key key' : List Nat) (v : Bytes) (t' : PTrie),
    t.set key v = some t' → key' ≠ key → t'.find key' = t.find key'
  | .hash _, _, _, _, _, h, _ => by simp [PTrie.set] at h
  | .leaf k s m, key, key', v, t', h, hne => by
    simp only [PTrie.set] at h
    split at h
    · rename_i e
      have e' : k = key := by simpa using e
      subst e'
      cases hs : s.get <;> simp [hs] at h; subst h
      simp [PTrie.find, Ne.symm hne]
    · simp at h
  | .ext k c m, key, key', v, t', h, hne => by
    simp only [PTrie.set] at h
    split at h
    · rename_i hp
      cases hs : c.set (key.drop k.length) v <;> simp [hs] at h; subst h
      simp only [PTrie.find]
      by_cases hp' : isPrefix k key' = true
      · simp only [hp', ↓reduceIte]
        obtain ⟨a, rfl⟩ := (isPrefix_iff _ _).1 hp
        obtain ⟨b, rfl⟩ := (isPrefix_iff _ _).1 hp'
        rw [drop_append_length] at hs ⊢
        exact PTrie.find_set_ne c a b v _ hs (fun e => hne (by rw [e]))
      · simp [hp']
    · simp at h
  | .branch bv cs m, [], key', v, t', h, hne => by
    simp only [PTrie.set] at h
    split at h <;> simp at h; subst h
    cases key' with
    | nil => exact absurd rfl hne
    | cons n' r' => simp [PTrie.find]
  | .branch bv cs m, n :: rest, key', v, t', h, hne => by
    simp only [PTrie.set] at h
    cases hs : Kids.set cs n rest v <;> simp [hs] at h; subst h
    cases key' with
    | nil => simp [PTrie.find]
    | cons n' r' => simp only [PTrie.find]; exact Kids.find_set_ne cs n rest n' r' v _ hs hne
theorem Kids.find_set_ne : ∀ (cs : Kids) (n : Nat) (key : List Nat) (n' : Nat) (key' : List Nat)
    (v : Bytes) (cs' : Kids), Kids.set cs n key v = some cs' → (n' :: key') ≠ (n :: key) →
    Kids.find cs' n' key' = Kids.find cs n' key'
  | .nil, _, _, _, _, _, _, h, _ => by simp [Kids.set] at h
  | .none _, 0, _, _, _, _, _, h, _ => by simp [Kids.set] at h
  | .some c r, 0, key, n', key', v, cs', h, hne => by
    simp only [Kids.set] at h
    cases hs : c.set key v <;> simp [hs] at h; subst h
    cases n' with
    | zero => simp only [Kids.find]; exact PTrie.find_set_ne c key key' v _ hs (fun e => hne (by rw [e]))
    | succ j => simp [Kids.find]
  | .none r, i + 1, key, n', key', v, cs', h, hne => by
    simp only [Kids.set] at h
    cases hs : Kids.set r i key v <;> simp [hs] at h; subst h
    cases n' with
    | zero => simp [Kids.find]
    | succ j =>
      simp only [Kids.find]
      exact Kids.find_set_ne r i key j key' v _ hs (fun e => hne (by simp at e; simp [e]))
  | .some c r, i + 1, key, n', key', v, cs', h, hne => by
    simp only [Kids.set] at h
    cases hs : Kids.set r i key v <;> simp [hs] at h; subst h
    cases n' with
    | zero => simp [Kids.find]
    | succ j =>
      simp only [Kids.find]
      exact Kids.find_set_ne r i key j key' v _ hs (fun e => hne (by simp at e; simp [e]))
end

/-- **`find_upsert_ne`** (NearSpec's `PTrie.find_upsert_other`). -/
theorem find_upsert_ne {t t' : PTrie} {key key' : List Nat} {v : Bytes} (hw : t.wf = true)
    (hk : nibblesOk key = true) (hne : key' ≠ key) (h : t.upsert key v = some t') :
    t'.find key' = t.find key' :=
  PTrie.find_upsert_other t key key' v t' hw hk hne h

/-! ## `set` through the split building blocks -/

theorem kidsFrom_congr : ∀ (n i : Nat) (f g : Nat → Option PTrie),
    (∀ x, i ≤ x → f x = g x) → kidsFrom n i f = kidsFrom n i g
  | 0, _, _, _, _ => rfl
  | n + 1, i, f, g, h => by
    simp only [kidsFrom, h i (Nat.le_refl _), kidsFrom_congr n (i + 1) f g (fun x hx => h x (by omega))]

theorem kidsFrom_set : ∀ (n i : Nat) (f : Nat → Option PTrie) (j : Nat) (key : List Nat) (v : Bytes)
    (c c' : PTrie), j < n → f (i + j) = some c → c.set key v = some c' →
    Kids.set (kidsFrom n i f) j key v =
      some (kidsFrom n i (fun x => if x = i + j then some c' else f x))
  | 0, _, _, _, _, _, _, _, hj, _, _ => by omega
  | n + 1, i, f, 0, key, v, c, c', _, hf, hc => by
    simp only [Nat.add_zero] at hf
    simp only [kidsFrom, hf, Kids.set, hc, Option.map_some, Nat.add_zero, ↓reduceIte]
    congr 2
    exact kidsFrom_congr n (i + 1) _ _ (fun x hx => by simp [show x ≠ i by omega])
  | n + 1, i, f, j + 1, key, v, c, c', hj, hf, hc => by
    have ih := kidsFrom_set n (i + 1) f j key v c c' (by omega)
      (by rw [show i + 1 + j = i + (j + 1) by omega]; exact hf) hc
    have e : (fun x => if x = i + 1 + j then some c' else f x) =
        (fun x => if x = i + (j + 1) then some c' else f x) := by
      funext x; rw [show i + 1 + j = i + (j + 1) by omega]
    rw [e] at ih
    have hi : (if i = i + (j + 1) then some c' else f i) = f i := by simp
    simp only [kidsFrom, hi]
    cases f i <;> simp [Kids.set, ih]

theorem set_kids1 {x : Nat} {c c' : PTrie} {key : List Nat} {v : Bytes} (hx : x < 16)
    (hc : c.set key v = some c') : Kids.set (kids1 x c) x key v = some (kids1 x c') := by
  unfold kids1
  rw [kidsFrom_set 16 0 _ x key v c c' hx (by simp) hc]
  congr 2; funext i; by_cases h : i = x <;> simp [h]

theorem set_kids2 {x y : Nat} {c c' d : PTrie} {key : List Nat} {v : Bytes} (hx : x < 16)
    (hc : c.set key v = some c') :
    Kids.set (kids2 x c y d) x key v = some (kids2 x c' y d) := by
  unfold kids2
  rw [kidsFrom_set 16 0 _ x key v c c' hx (by simp) hc]
  congr 2; funext i; by_cases h : i = x <;> simp [h]

theorem set_wrapExt (p r : List Nat) (b b' : PTrie) (v : Bytes) (hb : b.set r v = some b') :
    (wrapExt p b).set (p ++ r) v = some (wrapExt p b') := by
  cases p with
  | nil => simpa [wrapExt] using hb
  | cons a as =>
    simp only [wrapExt, PTrie.set, isPrefix_append, ↓reduceIte, drop_append_length, hb,
      Option.map_some, set_memD hb]

theorem set_splitLeaf {k key : List Nat} {old v1 v : Bytes} (hk : nibblesOk k = true)
    (hne : k ≠ key) (hl : old.length = v1.length) :
    (splitLeaf k (.val old) key v).set k v1 = some (splitLeaf k (.val v1) key v) := by
  have hcl := commonPrefix_left k key
  have hcr := commonPrefix_right k key
  unfold splitLeaf
  dsimp only
  generalize commonPrefix k key = p at hcl hcr ⊢
  generalize hkr : k.drop p.length = kr at hcl ⊢
  generalize hyr : key.drop p.length = yr at hcr ⊢
  have hkrOk : nibblesOk kr = true := by rw [hcl] at hk; exact (nibblesOk_append.1 hk).2
  cases kr with
  | nil =>
    cases yr with
    | nil => exact absurd (hcl.trans hcr.symm) hne
    | cons y ys =>
      simp only [Slot.len, hl]
      conv => lhs; rw [hcl, List.append_nil]
      have h := set_wrapExt p []
        (PTrie.branch (some (.val old)) (kids1 y (newLeaf ys v)) (50 + valueMem v1.length + leafMem ys v.length))
        (PTrie.branch (some (.val v1)) (kids1 y (newLeaf ys v)) (50 + valueMem v1.length + leafMem ys v.length))
        v1 (by simp [PTrie.set])
      simpa using h
  | cons x xs =>
    have hx := (nibblesOk_cons.1 hkrOk).1
    cases yr with
    | nil =>
      simp only [Slot.len, hl]
      conv => lhs; rw [hcl]
      apply set_wrapExt
      simp only [PTrie.set]
      rw [set_kids1 hx (c' := PTrie.leaf xs (.val v1) (leafMem xs v1.length))
        (by simp [PTrie.set, Slot.get])]
      rfl
    | cons y ys =>
      simp only [Slot.len, hl]
      conv => lhs; rw [hcl]
      apply set_wrapExt
      simp only [PTrie.set]
      rw [set_kids2 hx (c' := PTrie.leaf xs (.val v1) (leafMem xs v1.length))
        (by simp [PTrie.set, Slot.get])]
      rfl

theorem set_splitExt {k key r : List Nat} {c c1 : PTrie} {m : Nat} {v v1 : Bytes}
    (hk : nibblesOk k = true) (hnp : isPrefix k key = false) (hc : c.set r v1 = some c1) :
    (splitExt k c m key v).set (k ++ r) v1 = some (splitExt k c1 m key v) := by
  have hcl := commonPrefix_left k key
  have hcr := commonPrefix_right k key
  unfold splitExt
  dsimp only
  generalize commonPrefix k key = p at hcl hcr ⊢
  generalize hkr : k.drop p.length = kr at hcl ⊢
  generalize hyr : key.drop p.length = yr at hcr ⊢
  have hkrOk : nibblesOk kr = true := by rw [hcl] at hk; exact (nibblesOk_append.1 hk).2
  cases kr with
  | nil =>
    rw [hcl, hcr, List.append_nil, isPrefix_append] at hnp; exact absurd hnp (by simp)
  | cons x xs =>
    have hx := (nibblesOk_cons.1 hkrOk).1
    rw [show k ++ r = p ++ (x :: (xs ++ r)) by rw [hcl]; simp]
    cases xs with
    | nil =>
      cases yr with
      | nil =>
        dsimp only
        apply set_wrapExt; simp only [PTrie.set, List.nil_append]; rw [set_kids1 hx hc]; rfl
      | cons y ys =>
        dsimp only
        apply set_wrapExt; simp only [PTrie.set, List.nil_append]; rw [set_kids2 hx hc]; rfl
    | cons a as =>
      have hs : (PTrie.ext (a :: as) c (extOwnMem (a :: as) + (m - extOwnMem k))).set
          ((a :: as) ++ r) v1 = some (PTrie.ext (a :: as) c1 (extOwnMem (a :: as) + (m - extOwnMem k))) := by
        have : isPrefix (a :: as) (a :: (as ++ r)) = true := isPrefix_append (a :: as) r
        simp [PTrie.set, this, hc]
      cases yr with
      | nil =>
        dsimp only
        apply set_wrapExt; simp only [PTrie.set]; rw [set_kids1 hx hs]; rfl
      | cons y ys =>
        dsimp only
        apply set_wrapExt; simp only [PTrie.set]; rw [set_kids2 hx hs]; rfl

/-! ## `set_upsert_comm` -/

mutual
/-- **`set_upsert_comm`**: for distinct keys, a same-length `set` commutes with `upsert`. -/
theorem PTrie.set_upsert_comm : ∀ (t : PTrie) (k1 k2 : List Nat) (v1 v2 : Bytes) (t1 t2 : PTrie),
    t.wf = true → k1 ≠ k2 → (∀ old, t.find k1 = some (some old) → old.length = v1.length) →
    t.set k1 v1 = some t1 → t.upsert k2 v2 = some t2 →
    ∃ t12, t1.upsert k2 v2 = some t12 ∧ t2.set k1 v1 = some t12
  | .hash _, _, _, _, _, _, _, _, _, _, h1, _ => by simp [PTrie.set] at h1
  | .leaf k s m, k1, k2, v1, v2, t1, t2, hw, hne, hlen, h1, h2 => by
    simp only [PTrie.set] at h1
    split at h1
    · rename_i e
      have e' : k = k1 := by simpa using e
      subst e'
      cases s with
      | ref => simp [Slot.get] at h1
      | val old =>
        simp only [Slot.get, Option.map_some, Option.some.injEq] at h1; subst h1
        have hl := hlen old (by simp [PTrie.find, Slot.get])
        simp only [PTrie.upsert, hne, ↓reduceIte, Option.some.injEq] at h2; subst h2
        exact ⟨_, by simp [PTrie.upsert, hne], set_splitLeaf (wf_leaf hw) hne hl⟩
    · simp at h1
  | .ext k c m, k1, k2, v1, v2, t1, t2, hw, hne, hlen, h1, h2 => by
    simp only [PTrie.set] at h1
    split at h1
    · rename_i hp1
      cases hs : c.set (k1.drop k.length) v1 <;> simp [hs] at h1; subst h1
      obtain ⟨r1, rfl⟩ := (isPrefix_iff _ _).1 hp1
      rw [drop_append_length] at hs
      simp only [PTrie.upsert] at h2 ⊢
      by_cases hp2 : isPrefix k k2 = true
      · simp only [hp2, ↓reduceIte] at h2 ⊢
        cases hm : c.mem? <;> cases hu : c.upsert (k2.drop k.length) v2 <;> simp [hm, hu] at h2
        subst h2
        obtain ⟨r2, rfl⟩ := (isPrefix_iff _ _).1 hp2
        rw [drop_append_length] at hu ⊢
        rename_i cm c2
        obtain ⟨c12, hu12, hs12⟩ := PTrie.set_upsert_comm c r1 r2 v1 v2 _ _ (wf_ext hw).2
          (fun e => hne (by rw [e]))
          (fun old ho => hlen old (by
            simp only [PTrie.find, isPrefix_append, ↓reduceIte, drop_append_length]; exact ho)) hs hu
        refine ⟨PTrie.ext k c12 (m + c12.memD - cm), ?_, ?_⟩
        · simp [set_mem c _ _ _ hs, hm, hu12]
        · simp [PTrie.set, isPrefix_append, hs12, set_memD hs12]
      · have hp2' : isPrefix k k2 = false := by simpa using hp2
        simp only [hp2', Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h2 ⊢; subst h2
        exact ⟨_, rfl, set_splitExt (wf_ext hw).1 hp2' hs⟩
    · simp at h1
  | .branch bv cs m, [], k2, v1, v2, t1, t2, hw, hne, hlen, h1, h2 => by
    simp only [PTrie.set] at h1
    split at h1 <;> simp at h1; subst h1
    rename_i old hbv
    cases k2 with
    | nil => exact absurd rfl hne
    | cons n2 r2 =>
      simp only [PTrie.upsert] at h2 ⊢
      cases hu : Kids.upsert cs n2 r2 v2 <;> simp [hu] at h2; subst h2
      exact ⟨_, rfl, by simp [PTrie.set]⟩
  | .branch bv cs m, n1 :: r1, k2, v1, v2, t1, t2, hw, hne, hlen, h1, h2 => by
    simp only [PTrie.set] at h1
    cases hs : Kids.set cs n1 r1 v1 <;> simp [hs] at h1; subst h1
    cases k2 with
    | nil =>
      simp only [PTrie.upsert, Option.some.injEq] at h2; subst h2
      exact ⟨_, rfl, by simp [PTrie.set, hs]⟩
    | cons n2 r2 =>
      simp only [PTrie.upsert] at h2 ⊢
      cases hu : Kids.upsert cs n2 r2 v2 <;> simp [hu] at h2; subst h2
      rename_i res
      obtain ⟨cs12, hu12, hs12⟩ := Kids.set_upsert_comm cs 16 n1 r1 n2 r2 v1 v2 _ res.1 res.2.1 res.2.2
        (wf_branch hw) hne (fun old ho => hlen old (by simpa [PTrie.find] using ho)) hs hu
      exact ⟨PTrie.branch bv cs12 (m + res.2.2 - res.2.1), by simp [hu12], by simp [PTrie.set, hs12]⟩
theorem Kids.set_upsert_comm : ∀ (cs : Kids) (cnt n1 : Nat) (r1 : List Nat) (n2 : Nat) (r2 : List Nat)
    (v1 v2 : Bytes) (cs1 cs2 : Kids) (a b : Nat),
    Kids.wf cs cnt = true → (n1 :: r1) ≠ (n2 :: r2) →
    (∀ old, Kids.find cs n1 r1 = some (some old) → old.length = v1.length) →
    Kids.set cs n1 r1 v1 = some cs1 → Kids.upsert cs n2 r2 v2 = some (cs2, a, b) →
    ∃ cs12, Kids.upsert cs1 n2 r2 v2 = some (cs12, a, b) ∧ Kids.set cs2 n1 r1 v1 = some cs12
  | .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, _ => by simp [Kids.set] at h1
  | .none _, _, 0, _, _, _, _, _, _, _, _, _, _, _, _, h1, _ => by simp [Kids.set] at h1
  | .some c r, cnt, 0, r1, 0, r2, v1, v2, cs1, cs2, a, b, hw, hne, hlen, h1, h2 => by
    simp only [Kids.set] at h1
    cases hs : c.set r1 v1 <;> simp [hs] at h1; subst h1
    simp only [Kids.upsert] at h2 ⊢
    cases hm : c.mem? <;> cases hu : c.upsert r2 v2 <;> simp [hm, hu] at h2
    obtain ⟨rfl, rfl, rfl⟩ := h2
    rename_i cm c2
    obtain ⟨c12, hu12, hs12⟩ := PTrie.set_upsert_comm c r1 r2 v1 v2 _ _ (wf_kids_some hw).1
      (fun e => hne (by rw [e])) (fun old ho => hlen old (by simpa [Kids.find] using ho)) hs hu
    exact ⟨Kids.some c12 r, by simp [set_mem c _ _ _ hs, hm, hu12, set_memD hs12], by simp [Kids.set, hs12]⟩
  | .some c r, cnt, 0, r1, j + 1, r2, v1, v2, cs1, cs2, a, b, hw, hne, hlen, h1, h2 => by
    simp only [Kids.set] at h1
    cases hs : c.set r1 v1 <;> simp [hs] at h1; subst h1
    simp only [Kids.upsert] at h2 ⊢
    cases hu : Kids.upsert r j r2 v2 with
    | none => simp [hu] at h2
    | some x =>
      obtain ⟨x1, x2, x3⟩ := x
      simp only [hu, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl, rfl⟩ := h2
      exact ⟨_, rfl, by simp [Kids.set, hs]⟩
  | .some c r, cnt, i + 1, r1, 0, r2, v1, v2, cs1, cs2, a, b, hw, hne, hlen, h1, h2 => by
    simp only [Kids.set] at h1
    cases hs : Kids.set r i r1 v1 <;> simp [hs] at h1; subst h1
    simp only [Kids.upsert] at h2 ⊢
    cases hm : c.mem? <;> cases hu : c.upsert r2 v2 <;> simp [hm, hu] at h2
    obtain ⟨rfl, rfl, rfl⟩ := h2
    exact ⟨_, rfl, by simp [Kids.set, hs]⟩
  | .none r, cnt, i + 1, r1, 0, r2, v1, v2, cs1, cs2, a, b, hw, hne, hlen, h1, h2 => by
    simp only [Kids.set] at h1
    cases hs : Kids.set r i r1 v1 <;> simp [hs] at h1; subst h1
    simp only [Kids.upsert, Option.some.injEq, Prod.mk.injEq] at h2 ⊢
    obtain ⟨rfl, rfl, rfl⟩ := h2
    exact ⟨_, ⟨rfl, rfl, rfl⟩, by simp [Kids.set, hs]⟩
  | .none r, cnt, i + 1, r1, j + 1, r2, v1, v2, cs1, cs2, a, b, hw, hne, hlen, h1, h2 => by
    simp only [Kids.set] at h1
    cases hs : Kids.set r i r1 v1 <;> simp [hs] at h1; subst h1
    simp only [Kids.upsert] at h2 ⊢
    cases hu : Kids.upsert r j r2 v2 with
    | none => simp [hu] at h2
    | some x =>
      obtain ⟨x1, x2, x3⟩ := x
      simp only [hu, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl, rfl⟩ := h2
      obtain ⟨cs12, hu12, hs12⟩ := Kids.set_upsert_comm r (cnt - 1) i r1 j r2 v1 v2 _ x1 x2 x3
        (wf_kids_none hw) (fun e => hne (by simp at e; simp [e]))
        (fun old ho => hlen old (by simpa [Kids.find] using ho)) hs hu
      exact ⟨Kids.none cs12, by simp [hu12], by simp [Kids.set, hs12]⟩
  | .some c r, cnt, i + 1, r1, j + 1, r2, v1, v2, cs1, cs2, a, b, hw, hne, hlen, h1, h2 => by
    simp only [Kids.set] at h1
    cases hs : Kids.set r i r1 v1 <;> simp [hs] at h1; subst h1
    simp only [Kids.upsert] at h2 ⊢
    cases hu : Kids.upsert r j r2 v2 with
    | none => simp [hu] at h2
    | some x =>
      obtain ⟨x1, x2, x3⟩ := x
      simp only [hu, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl, rfl⟩ := h2
      obtain ⟨cs12, hu12, hs12⟩ := Kids.set_upsert_comm r (cnt - 1) i r1 j r2 v1 v2 _ x1 x2 x3
        (wf_kids_some hw).2 (fun e => hne (by simp at e; simp [e]))
        (fun old ho => hlen old (by simpa [Kids.find] using ho)) hs hu
      exact ⟨Kids.some c cs12, by simp [hu12], by simp [Kids.set, hs12]⟩
end

/-- The statement named in V3-D0-DESIGN §6.2: reads of other keys are unaffected by
`set` / `upsert`, and a same-length `set` commutes with `upsert` on another key. -/
def TrieOpsStmt : Prop :=
  (∀ (t t' : PTrie) (k k' : List Nat) (v : Bytes),
    t.set k v = some t' → k' ≠ k → t'.find k' = t.find k') ∧
  (∀ (t t' : PTrie) (k k' : List Nat) (v : Bytes), t.wf = true → nibblesOk k = true →
    t.upsert k v = some t' → k' ≠ k → t'.find k' = t.find k') ∧
  (∀ (t t1 t2 : PTrie) (k1 k2 : List Nat) (v1 v2 : Bytes), t.wf = true → k1 ≠ k2 →
    (∀ old, t.find k1 = some (some old) → old.length = v1.length) →
    t.set k1 v1 = some t1 → t.upsert k2 v2 = some t2 →
    ∃ t12, t1.upsert k2 v2 = some t12 ∧ t2.set k1 v1 = some t12)

theorem trieOpsStmt : TrieOpsStmt :=
  ⟨fun t t' k k' v h hne => PTrie.find_set_ne t k k' v t' h hne,
   fun _ _ _ _ _ hw hk h hne => find_upsert_ne hw hk hne h,
   fun t t1 t2 k1 k2 v1 v2 hw hne hl h1 h2 => PTrie.set_upsert_comm t k1 k2 v1 v2 t1 t2 hw hne hl h1 h2⟩

end ZkFormal.NearV3
