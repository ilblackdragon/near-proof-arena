import NearSpec.TrieUpsert

/-!
# Correctness of `PTrie.upsert` as a map update

For a well-formed partial trie `t` and a nibble key `k` (all nibbles `< 16`):

* `PTrie.find_upsert_self` : `t.upsert k v = some t' → t'.find k = some (some v)`
* `PTrie.find_upsert_other` : `t.upsert k v = some t' → k' ≠ k → t'.find k' = t.find k'`

i.e. on every key the updated partial trie answers exactly like the key→value
map updated at `k`, including *proven absence* (`some none`) and *unknown*
(`none`: unrevealed subtree or value) for all other keys.
-/

namespace NearSpec

/-! ## List helpers -/

theorem isPrefix_iff (p l : List Nat) : isPrefix p l = true ↔ ∃ r, l = p ++ r := by
  induction p generalizing l with
  | nil => simp [isPrefix]
  | cons a as ih =>
    cases l with
    | nil => simp [isPrefix]
    | cons b bs =>
      simp only [isPrefix, Bool.and_eq_true, beq_iff_eq, ih, List.cons_append, List.cons.injEq]
      constructor
      · rintro ⟨rfl, r, rfl⟩; exact ⟨r, rfl, rfl⟩
      · rintro ⟨r, rfl, rfl⟩; exact ⟨rfl, r, rfl⟩

theorem isPrefix_append (p r : List Nat) : isPrefix p (p ++ r) = true :=
  (isPrefix_iff _ _).2 ⟨r, rfl⟩

theorem drop_append_length (p r : List Nat) : (p ++ r).drop p.length = r := by
  simp

theorem commonPrefix_left (a b : List Nat) : a = commonPrefix a b ++ a.drop (commonPrefix a b).length := by
  induction a generalizing b with
  | nil => simp [commonPrefix]
  | cons x xs ih =>
    cases b with
    | nil => simp [commonPrefix]
    | cons y ys =>
      by_cases h : x = y
      · simp only [commonPrefix, h, ↓reduceIte, List.length_cons, List.drop_succ_cons,
          List.cons_append, List.cons.injEq, true_and]
        subst h; exact ih ys
      · simp [commonPrefix, h]

theorem commonPrefix_right (a b : List Nat) : b = commonPrefix a b ++ b.drop (commonPrefix a b).length := by
  induction a generalizing b with
  | nil => simp [commonPrefix]
  | cons x xs ih =>
    cases b with
    | nil => simp [commonPrefix]
    | cons y ys =>
      by_cases h : x = y
      · simp only [commonPrefix, h, ↓reduceIte, List.length_cons, List.drop_succ_cons,
          List.cons_append, List.cons.injEq, true_and]
        exact ih ys
      · simp [commonPrefix, h]

theorem commonPrefix_diverge (a b : List Nat) {x y : Nat} {xs ys : List Nat}
    (ha : a.drop (commonPrefix a b).length = x :: xs)
    (hb : b.drop (commonPrefix a b).length = y :: ys) : x ≠ y := by
  induction a generalizing b with
  | nil => simp [commonPrefix] at ha
  | cons u us ih =>
    cases b with
    | nil => simp [commonPrefix] at hb
    | cons w ws =>
      by_cases h : u = w
      · simp only [commonPrefix, h, ↓reduceIte, List.length_cons, List.drop_succ_cons] at ha hb
        exact ih ws (by subst h; exact ha) hb
      · simp only [commonPrefix, h, ↓reduceIte, List.length_nil, List.drop_zero,
          List.cons.injEq] at ha hb
        rw [← ha.1, ← hb.1]; exact h

theorem nibblesOk_append {a b : List Nat} : nibblesOk (a ++ b) = true ↔ nibblesOk a = true ∧ nibblesOk b = true := by
  simp [nibblesOk, List.all_append]

theorem nibblesOk_cons {x : Nat} {xs : List Nat} : nibblesOk (x :: xs) = true ↔ x < 16 ∧ nibblesOk xs = true := by
  simp [nibblesOk]

/-! ## `find` on the building blocks -/

theorem find_kidsFrom (n i : Nat) (f : Nat → Option PTrie) (j : Nat) (key : List Nat) :
    Kids.find (kidsFrom n i f) j key =
      if j < n then (match f (i + j) with | some c => c.find key | none => some none)
      else some none := by
  induction n generalizing i j with
  | zero => simp [kidsFrom, Kids.find]
  | succ n ih =>
    cases j with
    | zero =>
      simp only [kidsFrom, Nat.add_zero, Nat.zero_lt_succ, ↓reduceIte]
      cases f i <;> simp [Kids.find]
    | succ j =>
      have e : i + (j + 1) = (i + 1) + j := by omega
      simp only [kidsFrom]
      cases f i <;> simp [Kids.find, ih, e]

theorem find_kids1 {x : Nat} (c : PTrie) (j : Nat) (key : List Nat) (hx : x < 16) :
    Kids.find (kids1 x c) j key = if j = x then c.find key else some none := by
  unfold kids1
  rw [find_kidsFrom]
  by_cases hj : j = x
  · subst hj; simp [hx]
  · simp [hj]

theorem find_kids2 {x y : Nat} (c d : PTrie) (j : Nat) (key : List Nat) (hx : x < 16) (hy : y < 16) :
    Kids.find (kids2 x c y d) j key =
      if j = x then c.find key else if j = y then d.find key else some none := by
  unfold kids2
  rw [find_kidsFrom]
  by_cases hjx : j = x
  · subst hjx; simp [hx]
  · by_cases hjy : j = y
    · subst hjy; simp [hy, hjx]
    · simp [hjx, hjy]

theorem find_wrapExt (p : List Nat) (b : PTrie) (key : List Nat) :
    (wrapExt p b).find key = if isPrefix p key then b.find (key.drop p.length) else some none := by
  cases p with
  | nil => simp [wrapExt, isPrefix]
  | cons a as => simp [wrapExt, PTrie.find]

theorem find_leaf (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) :
    (PTrie.leaf k s m).find key = if k = key then s.get.map some else some none := by
  simp [PTrie.find]

theorem find_newLeaf (k : List Nat) (v : Bytes) (key : List Nat) :
    (newLeaf k v).find key = if k = key then some (some v) else some none := by
  simp [newLeaf, PTrie.find, Slot.get]

theorem find_ext (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) :
    (PTrie.ext k c m).find key = if isPrefix k key then c.find (key.drop k.length) else some none := by
  simp [PTrie.find]

theorem find_branch_nil (bv : Option Slot) (cs : Kids) (m : Nat) :
    (PTrie.branch bv cs m).find [] = (match bv with | none => some none | some s => s.get.map some) := by
  cases bv <;> simp [PTrie.find]

theorem find_branch_cons (bv : Option Slot) (cs : Kids) (m : Nat) (n : Nat) (rest : List Nat) :
    (PTrie.branch bv cs m).find (n :: rest) = Kids.find cs n rest := by
  simp [PTrie.find]

/-! ## Split lemmas -/

/-- Decompose two keys at their common prefix. -/
theorem split_keys (a b : List Nat) :
    ∃ p ra rb, p = commonPrefix a b ∧ a = p ++ ra ∧ b = p ++ rb ∧
      ra = a.drop p.length ∧ rb = b.drop p.length :=
  ⟨_, _, _, rfl, commonPrefix_left a b, commonPrefix_right a b, rfl, rfl⟩

theorem find_splitLeaf_self {k key : List Nat} (s : Slot) (v : Bytes)
    (hkey : nibblesOk key = true) (hne : k ≠ key) :
    (splitLeaf k s key v).find key = some (some v) := by
  have hl := commonPrefix_left k key
  have hr := commonPrefix_right k key
  have hdiv := @commonPrefix_diverge k key
  unfold splitLeaf
  generalize commonPrefix k key = p at hl hr hdiv ⊢
  generalize hkr : k.drop p.length = kr at hl hdiv ⊢
  generalize hyr : key.drop p.length = yr at hr hdiv ⊢
  have hpre : isPrefix p key = true := by rw [hr]; exact isPrefix_append _ _
  have hyrOk : nibblesOk yr = true := by rw [hr] at hkey; exact (nibblesOk_append.1 hkey).2
  cases kr with
  | nil =>
    cases yr with
    | nil => exact absurd (hl.trans hr.symm) hne
    | cons y ys =>
      simp only [hkr, find_wrapExt, hpre, hyr, ↓reduceIte, find_branch_cons]
      rw [find_kids1 _ _ _ (nibblesOk_cons.1 hyrOk).1]
      simp [find_newLeaf]
  | cons x xs =>
    cases yr with
    | nil =>
      simp [hkr, find_wrapExt, hpre, hyr, find_branch_nil, Slot.get]
    | cons y ys =>
      have hxy : x ≠ y := hdiv rfl rfl
      have hy := (nibblesOk_cons.1 hyrOk).1
      simp only [hkr, find_wrapExt, hpre, hyr, ↓reduceIte, find_branch_cons]
      unfold kids2; rw [find_kidsFrom]
      simp [hy, Ne.symm hxy, find_newLeaf]

theorem find_splitLeaf_other {k key key' : List Nat} (s : Slot) (v : Bytes) (m : Nat)
    (hk : nibblesOk k = true) (hkey : nibblesOk key = true) (hne : k ≠ key) (hne' : key' ≠ key) :
    (splitLeaf k s key v).find key' = (PTrie.leaf k s m).find key' := by
  have hl := commonPrefix_left k key
  have hr := commonPrefix_right k key
  have hdiv := @commonPrefix_diverge k key
  unfold splitLeaf
  generalize commonPrefix k key = p at hl hr hdiv ⊢
  generalize hkr : k.drop p.length = kr at hl hdiv ⊢
  generalize hyr : key.drop p.length = yr at hr hdiv ⊢
  have hyrOk : nibblesOk yr = true := by rw [hr] at hkey; exact (nibblesOk_append.1 hkey).2
  have hkrOk : nibblesOk kr = true := by rw [hl] at hk; exact (nibblesOk_append.1 hk).2
  rw [find_leaf]
  by_cases hpre : isPrefix p key' = true
  · obtain ⟨r', rfl⟩ := (isPrefix_iff _ _).1 hpre
    subst hl hr
    cases kr with
    | nil =>
      cases yr with
      | nil => exact absurd rfl hne
      | cons y ys =>
        have hy := (nibblesOk_cons.1 hyrOk).1
        simp only [hkr, find_wrapExt, hpre, ↓reduceIte, drop_append_length]
        cases r' with
        | nil => simp [find_branch_nil]
        | cons z zs =>
          rw [find_branch_cons, find_kids1 _ _ _ hy, find_newLeaf]
          by_cases hz : z = y
          · subst hz
            by_cases hzs : ys = zs
            · subst hzs; exact absurd rfl hne'
            · simp [hzs]
          · simp [hz]
    | cons x xs =>
      have hx := (nibblesOk_cons.1 hkrOk).1
      cases yr with
      | nil =>
        simp only [hkr, find_wrapExt, hpre, ↓reduceIte, drop_append_length]
        cases r' with
        | nil => exact absurd rfl hne'
        | cons z zs =>
          rw [find_branch_cons, find_kids1 _ _ _ hx, find_leaf]
          by_cases hz : z = x
          · subst hz; simp
          · simp [hz, Ne.symm hz]
      | cons y ys =>
        have hy := (nibblesOk_cons.1 hyrOk).1
        have hxy : x ≠ y := hdiv rfl rfl
        simp only [hkr, find_wrapExt, hpre, ↓reduceIte, drop_append_length]
        cases r' with
        | nil => simp [find_branch_nil]
        | cons z zs =>
          rw [find_branch_cons, find_kids2 _ _ _ _ hx hy, find_leaf, find_newLeaf]
          by_cases hzx : z = x
          · subst hzx; simp
          · by_cases hzy : z = y
            · subst hzy
              by_cases hzs : ys = zs
              · subst hzs; exact absurd rfl hne'
              · simp [hzs, hxy, hzx]
            · simp [hzx, hzy, Ne.symm hzx]
  · have hpre' : isPrefix p key' = false := by simpa using hpre
    have hk' : ¬ (p ++ kr = key') := by
      intro h; subst h; simp [isPrefix_append] at hpre'
    rw [← hl] at hk'
    simp only [hk', ↓reduceIte]
    cases kr <;> cases yr
    · exact absurd (hl.trans hr.symm) hne
    all_goals simp [hkr, hyr, find_wrapExt, hpre']

theorem isPrefix_append_append (p a b : List Nat) : isPrefix (p ++ a) (p ++ b) = isPrefix a b := by
  induction p with
  | nil => rfl
  | cons x xs ih => simp [isPrefix, ih]

theorem isPrefix_cons_cons (x z : Nat) (xs zs : List Nat) :
    isPrefix (x :: xs) (z :: zs) = (x == z && isPrefix xs zs) := rfl

theorem drop_len_cons (p xs zs : List Nat) (x z : Nat) :
    (p ++ z :: zs).drop (p ++ x :: xs).length = zs.drop xs.length := by
  simp [List.drop_append]

theorem find_splitExt_self {k key : List Nat} (c : PTrie) (m : Nat) (v : Bytes)
    (hkey : nibblesOk key = true) (hnp : isPrefix k key = false) :
    (splitExt k c m key v).find key = some (some v) := by
  have hl := commonPrefix_left k key
  have hr := commonPrefix_right k key
  have hdiv := @commonPrefix_diverge k key
  unfold splitExt
  generalize commonPrefix k key = p at hl hr hdiv ⊢
  generalize hkr : k.drop p.length = kr at hl hdiv ⊢
  generalize hyr : key.drop p.length = yr at hr hdiv ⊢
  have hpre : isPrefix p key = true := by rw [hr]; exact isPrefix_append _ _
  have hyrOk : nibblesOk yr = true := by rw [hr] at hkey; exact (nibblesOk_append.1 hkey).2
  cases kr with
  | nil =>
    rw [hl, hr, List.append_nil, isPrefix_append] at hnp; exact absurd hnp (by simp)
  | cons x xs =>
    cases yr with
    | nil => simp [hkr, hyr, find_wrapExt, hpre, find_branch_nil, Slot.get]
    | cons y ys =>
      have hxy : x ≠ y := hdiv rfl rfl
      have hy := (nibblesOk_cons.1 hyrOk).1
      simp only [hkr, hyr, find_wrapExt, hpre, ↓reduceIte, find_branch_cons]
      unfold kids2; rw [find_kidsFrom]
      simp [hy, Ne.symm hxy, find_newLeaf]

theorem find_splitExt_other {k key key' : List Nat} (c : PTrie) (m : Nat) (v : Bytes)
    (hk : nibblesOk k = true) (hkey : nibblesOk key = true) (hnp : isPrefix k key = false)
    (hne' : key' ≠ key) :
    (splitExt k c m key v).find key' = (PTrie.ext k c m).find key' := by
  have hl := commonPrefix_left k key
  have hr := commonPrefix_right k key
  have hdiv := @commonPrefix_diverge k key
  unfold splitExt
  generalize commonPrefix k key = p at hl hr hdiv ⊢
  generalize hkr : k.drop p.length = kr at hl hdiv ⊢
  generalize hyr : key.drop p.length = yr at hr hdiv ⊢
  have hyrOk : nibblesOk yr = true := by rw [hr] at hkey; exact (nibblesOk_append.1 hkey).2
  have hkrOk : nibblesOk kr = true := by rw [hl] at hk; exact (nibblesOk_append.1 hk).2
  rw [find_ext]
  cases kr with
  | nil =>
    rw [hl, hr, List.append_nil, isPrefix_append] at hnp; exact absurd hnp (by simp)
  | cons x xs =>
    have hx := (nibblesOk_cons.1 hkrOk).1
    subst hl
    by_cases hpre : isPrefix p key' = true
    · obtain ⟨r', rfl⟩ := (isPrefix_iff _ _).1 hpre
      subst hr
      have hsub : ∀ zs : List Nat,
          (match xs with
            | [] => c
            | _ :: _ => PTrie.ext xs c (extOwnMem xs + (m - extOwnMem (p ++ x :: xs)))).find zs =
          if isPrefix xs zs then c.find (zs.drop xs.length) else some none := by
        intro zs; cases xs with
        | nil => simp [isPrefix]
        | cons a as => simp [find_ext]
      cases yr with
      | nil =>
        simp only [hkr, hyr, find_wrapExt, hpre, ↓reduceIte, drop_append_length]
        cases r' with
        | nil => exact absurd rfl hne'
        | cons z zs =>
          rw [find_branch_cons, find_kids1 _ _ _ hx, isPrefix_append_append, isPrefix_cons_cons]
          by_cases hz : z = x
          · subst hz; simp only [↓reduceIte, beq_self_eq_true, Bool.true_and, drop_len_cons]
            exact hsub zs
          · simp [hz, Ne.symm hz]
      | cons y ys =>
        have hy := (nibblesOk_cons.1 hyrOk).1
        have hxy : x ≠ y := hdiv rfl rfl
        simp only [hkr, hyr, find_wrapExt, hpre, ↓reduceIte, drop_append_length]
        cases r' with
        | nil =>
          have : isPrefix (p ++ x :: xs) (p ++ []) = false := by
            rw [isPrefix_append_append]; rfl
          rw [List.append_nil] at this
          simp [find_branch_nil, this]
        | cons z zs =>
          rw [find_branch_cons, find_kids2 _ _ _ _ hx hy, isPrefix_append_append, isPrefix_cons_cons,
            find_newLeaf]
          by_cases hzx : z = x
          · subst hzx; simp only [↓reduceIte, beq_self_eq_true, Bool.true_and, drop_len_cons]
            exact hsub zs
          · by_cases hzy : z = y
            · subst hzy
              by_cases hzs : ys = zs
              · subst hzs; exact absurd rfl hne'
              · simp [hzs, hzx, Ne.symm hzx]
            · simp [hzx, hzy, Ne.symm hzx]
    · have hpre' : isPrefix p key' = false := by simpa using hpre
      have hk' : isPrefix (p ++ x :: xs) key' = false := by
        cases h : isPrefix (p ++ x :: xs) key' with
        | false => rfl
        | true =>
          obtain ⟨r, rfl⟩ := (isPrefix_iff _ _).1 h
          rw [List.append_assoc, isPrefix_append] at hpre'; exact absurd hpre' (by simp)
      simp only [hk']
      cases yr <;> simp [hkr, hyr, find_wrapExt, hpre']

theorem nibblesOk_drop {l : List Nat} (n : Nat) (h : nibblesOk l = true) : nibblesOk (l.drop n) = true := by
  induction l generalizing n with
  | nil => simp [nibblesOk]
  | cons x xs ih =>
    cases n with
    | zero => exact h
    | succ n => exact ih n (nibblesOk_cons.1 h).2

/-! ## Main theorems -/

mutual
/-- After `upsert k v`, looking up `k` yields `v`. -/
theorem PTrie.find_upsert_self : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (t' : PTrie),
    nibblesOk key = true → t.upsert key v = some t' → t'.find key = some (some v)
  | .hash _, _, _, _, _, h => by simp [PTrie.upsert] at h
  | .leaf k s m, key, v, t', hk, h => by
    simp only [PTrie.upsert] at h
    by_cases e : k = key
    · simp only [e, ↓reduceIte, Option.some.injEq] at h; subst h; simp [find_newLeaf]
    · simp only [e, ↓reduceIte, Option.some.injEq] at h; subst h; exact find_splitLeaf_self s v hk e
  | .ext k c m, key, v, t', hk, h => by
    simp only [PTrie.upsert] at h
    by_cases hp : isPrefix k key = true
    · simp only [hp, ↓reduceIte] at h
      cases hm : c.mem? <;> cases hu : c.upsert (key.drop k.length) v <;> simp [hm, hu] at h
      subst h
      rw [find_ext]; simp only [hp, ↓reduceIte]
      exact PTrie.find_upsert_self c _ v _ (nibblesOk_drop _ hk) hu
    · have hp' : isPrefix k key = false := by simpa using hp
      simp only [hp', Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h; subst h
      exact find_splitExt_self c m v hk hp'
  | .branch bv cs m, [], v, t', _, h => by
    simp only [PTrie.upsert] at h; cases h
    simp [find_branch_nil, Slot.get]
  | .branch bv cs m, n :: rest, v, t', hk, h => by
    simp only [PTrie.upsert] at h
    cases hu : Kids.upsert cs n rest v with
    | none => simp [hu] at h
    | some r =>
      simp only [hu, Option.map_some] at h; cases h
      rw [find_branch_cons]
      exact Kids.find_upsert_self cs n rest v r.1 r.2.1 r.2.2 (nibblesOk_cons.1 hk).2 hu

theorem Kids.find_upsert_self : ∀ (cs : Kids) (n : Nat) (key : List Nat) (v : Bytes) (cs' : Kids) (a b : Nat),
    nibblesOk key = true → Kids.upsert cs n key v = some (cs', a, b) → Kids.find cs' n key = some (some v)
  | .nil, _, _, _, _, _, _, _, h => by simp [Kids.upsert] at h
  | .none r, 0, key, v, cs', a, b, _, h => by
    simp only [Kids.upsert, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, -⟩ := h
    simp [Kids.find, find_newLeaf]
  | .some c r, 0, key, v, cs', a, b, hk, h => by
    simp only [Kids.upsert] at h
    cases hm : c.mem? <;> cases hu : c.upsert key v <;> simp [hm, hu] at h
    obtain ⟨rfl, -, -⟩ := h
    simp only [Kids.find]
    exact PTrie.find_upsert_self c key v _ hk hu
  | .none r, i + 1, key, v, cs', a, b, hk, h => by
    simp only [Kids.upsert] at h
    cases hu : Kids.upsert r i key v with
    | none => simp [hu] at h
    | some x =>
      simp only [hu, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp only [Kids.find]
      exact Kids.find_upsert_self r i key v x.1 x.2.1 x.2.2 hk hu
  | .some c r, i + 1, key, v, cs', a, b, hk, h => by
    simp only [Kids.upsert] at h
    cases hu : Kids.upsert r i key v with
    | none => simp [hu] at h
    | some x =>
      simp only [hu, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp only [Kids.find]
      exact Kids.find_upsert_self r i key v x.1 x.2.1 x.2.2 hk hu
end

theorem wf_leaf {k : List Nat} {s : Slot} {m : Nat} (h : (PTrie.leaf k s m).wf = true) :
    nibblesOk k = true := by
  simp only [PTrie.wf, Bool.and_eq_true] at h; exact h.1.1.1

theorem wf_ext {k : List Nat} {c : PTrie} {m : Nat} (h : (PTrie.ext k c m).wf = true) :
    nibblesOk k = true ∧ c.wf = true := by
  simp only [PTrie.wf, Bool.and_eq_true] at h; exact ⟨h.1.1.1, h.1.1.2⟩

theorem wf_branch {bv : Option Slot} {cs : Kids} {m : Nat} (h : (PTrie.branch bv cs m).wf = true) :
    Kids.wf cs 16 = true := by
  simp only [PTrie.wf, Bool.and_eq_true] at h; exact h.1.2

theorem wf_kids_some {c : PTrie} {r : Kids} {n : Nat} (h : Kids.wf (.some c r) n = true) :
    c.wf = true ∧ Kids.wf r (n - 1) = true := by
  simp only [Kids.wf, Bool.and_eq_true] at h; exact ⟨h.1.2, h.2⟩

theorem wf_kids_none {r : Kids} {n : Nat} (h : Kids.wf (.none r) n = true) :
    Kids.wf r (n - 1) = true := by
  simp only [Kids.wf, Bool.and_eq_true] at h; exact h.2

mutual
/-- After `upsert k v`, every other key looks up exactly as before. -/
theorem PTrie.find_upsert_other : ∀ (t : PTrie) (key key' : List Nat) (v : Bytes) (t' : PTrie),
    t.wf = true → nibblesOk key = true → key' ≠ key → t.upsert key v = some t' →
    t'.find key' = t.find key'
  | .hash _, _, _, _, _, _, _, _, h => by simp [PTrie.upsert] at h
  | .leaf k s m, key, key', v, t', hw, hk, hne, h => by
    simp only [PTrie.upsert] at h
    by_cases e : k = key
    · simp only [e, ↓reduceIte, Option.some.injEq] at h; subst h e
      rw [find_newLeaf, find_leaf]
      simp [Ne.symm hne]
    · simp only [e, ↓reduceIte, Option.some.injEq] at h; subst h
      exact find_splitLeaf_other s v m (wf_leaf hw) hk e hne
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
        exact PTrie.find_upsert_other c a b v _ (wf_ext hw).2
          (nibblesOk_append.1 hk).2 hab hu
      · simp [hp']
    · have hp' : isPrefix k key = false := by simpa using hp
      simp only [hp', Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h; subst h
      exact find_splitExt_other c m v (wf_ext hw).1 hk hp' hne
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
        exact Kids.find_upsert_other cs 16 n rest n' rest' v r.1 r.2.1 r.2.2 (wf_branch hw)
          (nibblesOk_cons.1 hk).2 hne hu

theorem Kids.find_upsert_other : ∀ (cs : Kids) (cnt n : Nat) (key : List Nat) (n' : Nat)
    (key' : List Nat) (v : Bytes) (cs' : Kids) (a b : Nat),
    Kids.wf cs cnt = true → nibblesOk key = true → (n' :: key') ≠ (n :: key) →
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
      exact PTrie.find_upsert_other c key key' v _ (wf_kids_some hw).1 hk this hu
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
        exact Kids.find_upsert_other r (cnt - 1) i key j key' v x.1 x.2.1 x.2.2 (wf_kids_none hw)
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
        exact Kids.find_upsert_other r (cnt - 1) i key j key' v x.1 x.2.1 x.2.2
          (wf_kids_some hw).2 hk this hu
end

/-! ## Independence from how much of the trie is revealed

`t₁.refinedBy t₂`: `t₁` is `t₂` with some subtrees replaced by their hash and
some values by their `ValueRef`. Refinement preserves the root hash, and
`upsert` commutes with it: the post-root computed on any partial witness equals
the post-root computed on the fully revealed trie. -/

def SlotRefines (s₁ s₂ : Slot) : Prop :=
  s₁ = s₂ ∨ ∃ v, s₁ = .ref v.length (sha256 v) ∧ s₂ = .val v

def OptSlotRefines : Option Slot → Option Slot → Prop
  | none, none => True
  | some a, some b => SlotRefines a b
  | _, _ => False

mutual
def PTrie.refinedBy : PTrie → PTrie → Prop
  | .hash h, t => h = t.hashOf
  | .leaf k s m, .leaf k' s' m' => k = k' ∧ m = m' ∧ SlotRefines s s'
  | .ext k c m, .ext k' c' m' => k = k' ∧ m = m' ∧ c.refinedBy c'
  | .branch v cs m, .branch v' cs' m' => m = m' ∧ OptSlotRefines v v' ∧ Kids.refinedBy cs cs'
  | .leaf .., .hash _ | .leaf .., .ext .. | .leaf .., .branch .. => False
  | .ext .., .hash _ | .ext .., .leaf .. | .ext .., .branch .. => False
  | .branch .., .hash _ | .branch .., .leaf .. | .branch .., .ext .. => False
def Kids.refinedBy : Kids → Kids → Prop
  | .nil, .nil => True
  | .none r, .none r' => Kids.refinedBy r r'
  | .some c r, .some c' r' => c.refinedBy c' ∧ Kids.refinedBy r r'
  | .nil, .none _ | .nil, .some .. => False
  | .none _, .nil | .none _, .some .. => False
  | .some .., .nil | .some .., .none _ => False
end

theorem SlotRefines.valueRef {s₁ s₂ : Slot} (h : SlotRefines s₁ s₂) : s₁.valueRef = s₂.valueRef := by
  rcases h with rfl | ⟨v, rfl, rfl⟩
  · rfl
  · rfl

theorem SlotRefines.len {s₁ s₂ : Slot} (h : SlotRefines s₁ s₂) : s₁.len = s₂.len := by
  rcases h with rfl | ⟨v, rfl, rfl⟩
  · rfl
  · rfl

mutual
theorem PTrie.refinedBy_refl : ∀ t : PTrie, t.refinedBy t
  | .hash h => by simp [PTrie.refinedBy, PTrie.hashOf]
  | .leaf k s m => by simp [PTrie.refinedBy, SlotRefines]
  | .ext k c m => by simp only [PTrie.refinedBy, true_and]; exact PTrie.refinedBy_refl c
  | .branch v cs m => by
    simp only [PTrie.refinedBy, true_and]
    refine ⟨?_, Kids.refinedBy_refl cs⟩
    cases v <;> simp [OptSlotRefines, SlotRefines]
theorem Kids.refinedBy_refl : ∀ cs : Kids, Kids.refinedBy cs cs
  | .nil => by simp [Kids.refinedBy]
  | .none r => by simp only [Kids.refinedBy]; exact Kids.refinedBy_refl r
  | .some c r => by simp only [Kids.refinedBy]; exact ⟨PTrie.refinedBy_refl c, Kids.refinedBy_refl r⟩
end

mutual
/-- Refinement preserves the node hash. -/
theorem PTrie.hashOf_refinedBy : ∀ (t₁ t₂ : PTrie), t₁.refinedBy t₂ → t₁.hashOf = t₂.hashOf
  | .hash h, t₂, hr => by simp only [PTrie.refinedBy] at hr; simp [PTrie.hashOf, hr]
  | .leaf k s m, t₂, hr => by
    cases t₂ <;> simp only [PTrie.refinedBy] at hr
    obtain ⟨rfl, rfl, hs⟩ := hr
    simp [PTrie.hashOf, hs.valueRef]
  | .ext k c m, t₂, hr => by
    cases t₂ <;> simp only [PTrie.refinedBy] at hr
    obtain ⟨rfl, rfl, hc⟩ := hr
    simp [PTrie.hashOf, PTrie.hashOf_refinedBy c _ hc]
  | .branch v cs m, t₂, hr => by
    cases t₂ with
    | branch v' cs' m' =>
      simp only [PTrie.refinedBy] at hr
      obtain ⟨rfl, hv, hcs⟩ := hr
      have ⟨hb, hh⟩ := Kids.hashOf_refinedBy cs cs' 0 hcs
      cases v <;> cases v' <;> simp only [OptSlotRefines] at hv
      · simp [PTrie.hashOf, hb, hh]
      · simp [PTrie.hashOf, hb, hh, hv.valueRef]
    | _ => simp [PTrie.refinedBy] at hr
theorem Kids.hashOf_refinedBy : ∀ (cs₁ cs₂ : Kids) (i : Nat), Kids.refinedBy cs₁ cs₂ →
    kidsBitmap cs₁ i = kidsBitmap cs₂ i ∧ Kids.hashes cs₁ = Kids.hashes cs₂
  | .nil, cs₂, i, hr => by cases cs₂ <;> simp [Kids.refinedBy] at hr; simp [kidsBitmap, Kids.hashes]
  | .none r, cs₂, i, hr => by
    cases cs₂ <;> simp only [Kids.refinedBy] at hr
    have := Kids.hashOf_refinedBy r _ (i + 1) hr
    simp [kidsBitmap, Kids.hashes, this.1, this.2]
  | .some c r, cs₂, i, hr => by
    cases cs₂ <;> simp only [Kids.refinedBy] at hr
    have := Kids.hashOf_refinedBy r _ (i + 1) hr.2
    simp [kidsBitmap, Kids.hashes, this.1, this.2, PTrie.hashOf_refinedBy c _ hr.1]
end

theorem refinedBy_mem {t₁ t₂ : PTrie} {m : Nat} (hr : t₁.refinedBy t₂) (hm : t₁.mem? = some m) :
    t₂.mem? = some m := by
  cases t₁ <;> cases t₂ <;> simp_all [PTrie.refinedBy, PTrie.mem?]

theorem refinedBy_memD {t₁ t₂ : PTrie} (hr : t₁.refinedBy t₂) (hm : t₁.mem?.isSome = true) :
    t₁.memD = t₂.memD := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 hm
  simp [PTrie.memD, hm, refinedBy_mem hr hm]

theorem kidsFrom_refinedBy (n i : Nat) (f g : Nat → Option PTrie)
    (h : ∀ j, (f j = none ∧ g j = none) ∨ ∃ a b, f j = some a ∧ g j = some b ∧ a.refinedBy b) :
    Kids.refinedBy (kidsFrom n i f) (kidsFrom n i g) := by
  induction n generalizing i with
  | zero => simp [kidsFrom, Kids.refinedBy]
  | succ n ih =>
    rcases h i with ⟨hf, hg⟩ | ⟨a, b, hf, hg, hab⟩
    · simp only [kidsFrom, hf, hg, Kids.refinedBy]; exact ih (i + 1)
    · simp only [kidsFrom, hf, hg, Kids.refinedBy]; exact ⟨hab, ih (i + 1)⟩

theorem kids1_refinedBy (x : Nat) {c₁ c₂ : PTrie} (h : c₁.refinedBy c₂) :
    Kids.refinedBy (kids1 x c₁) (kids1 x c₂) := by
  apply kidsFrom_refinedBy; intro j
  by_cases hj : j = x
  · right; exact ⟨c₁, c₂, by simp [hj], by simp [hj], h⟩
  · left; simp [hj]

theorem kids2_refinedBy (x y : Nat) {c₁ c₂ d₁ d₂ : PTrie} (hc : c₁.refinedBy c₂) (hd : d₁.refinedBy d₂) :
    Kids.refinedBy (kids2 x c₁ y d₁) (kids2 x c₂ y d₂) := by
  apply kidsFrom_refinedBy; intro j
  by_cases hjx : j = x
  · right; exact ⟨c₁, c₂, by simp [hjx], by simp [hjx], hc⟩
  · by_cases hjy : j = y
    · subst hjy; right; exact ⟨d₁, d₂, by simp [hjx], by simp [hjx], hd⟩
    · left; simp [hjx, hjy]

theorem wrapExt_refinedBy (p : List Nat) {b₁ b₂ : PTrie} (h : b₁.refinedBy b₂) (hm : b₁.memD = b₂.memD) :
    (wrapExt p b₁).refinedBy (wrapExt p b₂) := by
  cases p with
  | nil => exact h
  | cons a as => simp [wrapExt, PTrie.refinedBy, hm, h]

theorem branch_refinedBy {v₁ v₂ : Option Slot} {cs₁ cs₂ : Kids} (m : Nat)
    (hv : OptSlotRefines v₁ v₂) (hcs : Kids.refinedBy cs₁ cs₂) :
    (PTrie.branch v₁ cs₁ m).refinedBy (.branch v₂ cs₂ m) := by
  simp [PTrie.refinedBy, hv, hcs]

theorem splitLeaf_refinedBy (k key : List Nat) {s₁ s₂ : Slot} (v : Bytes) (hs : SlotRefines s₁ s₂) :
    (splitLeaf k s₁ key v).refinedBy (splitLeaf k s₂ key v) := by
  unfold splitLeaf; dsimp only
  have hl : s₁.len = s₂.len := hs.len
  generalize k.drop (commonPrefix k key).length = kr
  generalize key.drop (commonPrefix k key).length = yr
  cases kr <;> cases yr <;> simp only [hl]
  · exact PTrie.refinedBy_refl _
  · exact wrapExt_refinedBy _ (branch_refinedBy _ (by simpa [OptSlotRefines] using hs)
      (kids1_refinedBy _ (PTrie.refinedBy_refl _))) rfl
  · exact wrapExt_refinedBy _ (branch_refinedBy _ (by simp [OptSlotRefines, SlotRefines])
      (kids1_refinedBy _ (by simp [PTrie.refinedBy, hs]))) rfl
  · exact wrapExt_refinedBy _ (branch_refinedBy _ trivial
      (kids2_refinedBy _ _ (by simp [PTrie.refinedBy, hs]) (PTrie.refinedBy_refl _))) rfl

theorem splitExt_refinedBy (k : List Nat) {c₁ c₂ : PTrie} (m : Nat) (key : List Nat) (v : Bytes)
    (hc : c₁.refinedBy c₂) :
    (splitExt k c₁ m key v).refinedBy (splitExt k c₂ m key v) := by
  unfold splitExt; dsimp only
  generalize k.drop (commonPrefix k key).length = kr
  generalize key.drop (commonPrefix k key).length = yr
  cases kr with
  | nil => simp [PTrie.refinedBy, hc]
  | cons x xs =>
    have hsub : (match xs with
          | [] => c₁
          | _ :: _ => PTrie.ext xs c₁ (extOwnMem xs + (m - extOwnMem k))).refinedBy
        (match xs with
          | [] => c₂
          | _ :: _ => PTrie.ext xs c₂ (extOwnMem xs + (m - extOwnMem k))) := by
      cases xs <;> simp [PTrie.refinedBy, hc]
    cases yr with
    | nil =>
      exact wrapExt_refinedBy _ (branch_refinedBy _ (by simp [OptSlotRefines, SlotRefines])
        (kids1_refinedBy _ hsub)) rfl
    | cons y ys =>
      exact wrapExt_refinedBy _ (branch_refinedBy _ trivial
        (kids2_refinedBy _ _ hsub (PTrie.refinedBy_refl _))) rfl

mutual
theorem PTrie.upsert_mem : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (t' : PTrie),
    t.upsert key v = some t' → t'.mem?.isSome = true
  | .hash _, _, _, _, h => by simp [PTrie.upsert] at h
  | .leaf k s m, key, v, t', h => by
    simp only [PTrie.upsert] at h
    split at h <;> simp only [Option.some.injEq] at h <;> subst h
    · simp [newLeaf, PTrie.mem?]
    · unfold splitLeaf; dsimp only
      generalize k.drop (commonPrefix k key).length = kr
      generalize key.drop (commonPrefix k key).length = yr
      generalize commonPrefix k key = p
      cases kr <;> cases yr <;> cases p <;> simp [newLeaf, wrapExt, PTrie.mem?]
  | .ext k c m, key, v, t', h => by
    simp only [PTrie.upsert] at h
    split at h
    · cases hm : c.mem? <;> cases hu : c.upsert (key.drop k.length) v <;> simp [hm, hu] at h
      subst h; simp [PTrie.mem?]
    · simp only [Option.some.injEq] at h; subst h
      unfold splitExt; dsimp only
      generalize k.drop (commonPrefix k key).length = kr
      generalize key.drop (commonPrefix k key).length = yr
      generalize commonPrefix k key = p
      cases kr <;> cases yr <;> cases p <;> simp [wrapExt, PTrie.mem?]
  | .branch bv cs m, [], v, t', h => by
    simp only [PTrie.upsert, Option.some.injEq] at h; subst h; simp [PTrie.mem?]
  | .branch bv cs m, n :: rest, v, t', h => by
    simp only [PTrie.upsert] at h
    cases hu : Kids.upsert cs n rest v <;> simp [hu] at h
    subst h; simp [PTrie.mem?]
end

mutual
/-- `upsert` commutes with refinement: whatever is revealed, the result refines
the result on a more revealed trie (in particular on the full trie). -/
theorem PTrie.upsert_refinedBy : ∀ (t₁ t₂ : PTrie) (key : List Nat) (v : Bytes) (t₁' : PTrie),
    t₁.refinedBy t₂ → t₁.upsert key v = some t₁' →
    ∃ t₂', t₂.upsert key v = some t₂' ∧ t₁'.refinedBy t₂'
  | .hash _, _, _, _, _, _, h => by simp [PTrie.upsert] at h
  | .leaf k s m, t₂, key, v, t₁', hr, h => by
    cases t₂ <;> simp only [PTrie.refinedBy] at hr
    obtain ⟨rfl, rfl, hs⟩ := hr
    simp only [PTrie.upsert] at h ⊢
    by_cases e : k = key
    · simp only [e, ↓reduceIte, Option.some.injEq] at h ⊢; subst h
      exact ⟨_, rfl, PTrie.refinedBy_refl _⟩
    · simp only [e, ↓reduceIte, Option.some.injEq] at h ⊢; subst h
      exact ⟨_, rfl, splitLeaf_refinedBy k key v hs⟩
  | .ext k c m, t₂, key, v, t₁', hr, h => by
    cases t₂ <;> simp only [PTrie.refinedBy] at hr
    rename_i k₂ c₂ m₂
    obtain ⟨rfl, rfl, hc⟩ := hr
    simp only [PTrie.upsert] at h ⊢
    by_cases hp : isPrefix k key = true
    · simp only [hp, ↓reduceIte] at h ⊢
      cases hm : c.mem? <;> cases hu : c.upsert (key.drop k.length) v <;> simp [hm, hu] at h
      rename_i cm c'
      obtain ⟨c₂', hu₂, hc'⟩ := PTrie.upsert_refinedBy c c₂ _ v c' hc hu
      have hm₂ := refinedBy_mem hc hm
      have hd := refinedBy_memD hc' (PTrie.upsert_mem c _ v c' hu)
      subst h
      refine ⟨.ext k c₂' (m + c₂'.memD - cm), by simp [hm₂, hu₂], ?_⟩
      simp [PTrie.refinedBy, hc', hd]
    · have hp' : isPrefix k key = false := by simpa using hp
      simp only [hp', Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h ⊢; subst h
      exact ⟨_, rfl, splitExt_refinedBy k m key v hc⟩
  | .branch bv cs m, t₂, [], v, t₁', hr, h => by
    cases t₂ <;> simp only [PTrie.refinedBy] at hr
    rename_i bv₂ cs₂ m₂
    obtain ⟨rfl, hv, hcs⟩ := hr
    simp only [PTrie.upsert, Option.some.injEq] at h ⊢; subst h
    refine ⟨_, rfl, ?_⟩
    cases bv <;> cases bv₂ <;> simp only [OptSlotRefines] at hv
    · exact branch_refinedBy _ (by simp [OptSlotRefines, SlotRefines]) hcs
    · simp only [hv.len]
      exact branch_refinedBy _ (by simp [OptSlotRefines, SlotRefines]) hcs
  | .branch bv cs m, t₂, n :: rest, v, t₁', hr, h => by
    cases t₂ <;> simp only [PTrie.refinedBy] at hr
    rename_i bv₂ cs₂ m₂
    obtain ⟨rfl, hv, hcs⟩ := hr
    simp only [PTrie.upsert] at h ⊢
    cases hu : Kids.upsert cs n rest v with
    | none => simp [hu] at h
    | some r =>
      obtain ⟨cs', a, b⟩ := r
      simp only [hu, Option.map_some, Option.some.injEq] at h; subst h
      obtain ⟨cs₂', hu₂, hr'⟩ := Kids.upsert_refinedBy cs cs₂ n rest v cs' a b hcs hu
      exact ⟨_, by simp [hu₂], branch_refinedBy _ hv hr'⟩

theorem Kids.upsert_refinedBy : ∀ (cs₁ cs₂ : Kids) (n : Nat) (key : List Nat) (v : Bytes)
    (cs₁' : Kids) (a b : Nat), Kids.refinedBy cs₁ cs₂ → Kids.upsert cs₁ n key v = some (cs₁', a, b) →
    ∃ cs₂', Kids.upsert cs₂ n key v = some (cs₂', a, b) ∧ Kids.refinedBy cs₁' cs₂'
  | .nil, _, _, _, _, _, _, _, _, h => by simp [Kids.upsert] at h
  | .none r, cs₂, 0, key, v, cs₁', a, b, hr, h => by
    cases cs₂ <;> simp only [Kids.refinedBy] at hr
    simp only [Kids.upsert, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨_, ⟨rfl, rfl, rfl⟩, by simp [Kids.refinedBy, PTrie.refinedBy_refl, hr]⟩
  | .some c r, cs₂, 0, key, v, cs₁', a, b, hr, h => by
    cases cs₂ <;> simp only [Kids.refinedBy] at hr
    rename_i c₂ r₂
    simp only [Kids.upsert] at h ⊢
    cases hm : c.mem? <;> cases hu : c.upsert key v <;> simp [hm, hu] at h
    rename_i cm c'
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨c₂', hu₂, hc'⟩ := PTrie.upsert_refinedBy c c₂ key v c' hr.1 hu
    have hm₂ := refinedBy_mem hr.1 hm
    have hd := refinedBy_memD hc' (PTrie.upsert_mem c key v c' hu)
    exact ⟨.some c₂' r₂, by simp [hm₂, hu₂, hd], by simp [Kids.refinedBy, hc', hr.2]⟩
  | .none r, cs₂, i + 1, key, v, cs₁', a, b, hr, h => by
    cases cs₂ <;> simp only [Kids.refinedBy] at hr
    rename_i r₂
    simp only [Kids.upsert] at h ⊢
    cases hu : Kids.upsert r i key v with
    | none => simp [hu] at h
    | some x =>
      obtain ⟨x1, x2, x3⟩ := x
      simp only [hu, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨r₂', hu₂, hr'⟩ := Kids.upsert_refinedBy r r₂ i key v x1 x2 x3 hr hu
      exact ⟨.none r₂', by simp [hu₂], by simp [Kids.refinedBy, hr']⟩
  | .some c r, cs₂, i + 1, key, v, cs₁', a, b, hr, h => by
    cases cs₂ <;> simp only [Kids.refinedBy] at hr
    rename_i c₂ r₂
    simp only [Kids.upsert] at h ⊢
    cases hu : Kids.upsert r i key v with
    | none => simp [hu] at h
    | some x =>
      obtain ⟨x1, x2, x3⟩ := x
      simp only [hu, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨r₂', hu₂, hr'⟩ := Kids.upsert_refinedBy r r₂ i key v x1 x2 x3 hr.2 hu
      exact ⟨.some c₂ r₂', by simp [hu₂], by simp [Kids.refinedBy, hr.1, hr']⟩
end

/-- **Post-root independence.** If a partial trie `t₁` refines `t₂` (e.g. the
fully revealed pre-state trie), the post-root computed by `upsert` on `t₁` is
the post-root `upsert` computes on `t₂`, and the pre-roots agree. -/
theorem PTrie.upsert_hashOf_congr {t₁ t₂ t₁' : PTrie} {key : List Nat} {v : Bytes}
    (hr : t₁.refinedBy t₂) (h : t₁.upsert key v = some t₁') :
    t₁.hashOf = t₂.hashOf ∧ ∃ t₂', t₂.upsert key v = some t₂' ∧ t₁'.hashOf = t₂'.hashOf := by
  refine ⟨PTrie.hashOf_refinedBy _ _ hr, ?_⟩
  obtain ⟨t₂', h₂, hr'⟩ := PTrie.upsert_refinedBy t₁ t₂ key v t₁' hr h
  exact ⟨t₂', h₂, PTrie.hashOf_refinedBy _ _ hr'⟩

theorem SlotRefines.get {s₁ s₂ : Slot} {x : Bytes} (h : SlotRefines s₁ s₂) (hg : s₁.get = some x) :
    s₂.get = some x := by
  rcases h with rfl | ⟨v, rfl, rfl⟩
  · exact hg
  · simp [Slot.get] at hg

mutual
/-- Whatever a partial trie determines (presence with value, or absence), the
more revealed trie determines identically. -/
theorem PTrie.find_refinedBy : ∀ (t₁ t₂ : PTrie) (key : List Nat) (x : Option Bytes),
    t₁.refinedBy t₂ → t₁.find key = some x → t₂.find key = some x
  | .hash _, _, _, _, _, h => by simp [PTrie.find] at h
  | .leaf k s m, t₂, key, x, hr, h => by
    cases t₂ <;> simp only [PTrie.refinedBy] at hr
    obtain ⟨rfl, rfl, hs⟩ := hr
    rw [find_leaf] at h ⊢
    by_cases e : k = key
    · simp only [e, ↓reduceIte] at h ⊢
      cases hg : Slot.get s <;> simp [hg] at h
      subst h; simp [hs.get hg]
    · simpa [e] using h
  | .ext k c m, t₂, key, x, hr, h => by
    cases t₂ <;> simp only [PTrie.refinedBy] at hr
    obtain ⟨rfl, rfl, hc⟩ := hr
    rw [find_ext] at h ⊢
    by_cases hp : isPrefix k key = true
    · simp only [hp, ↓reduceIte] at h ⊢; exact PTrie.find_refinedBy c _ _ x hc h
    · simpa [hp] using h
  | .branch v cs m, t₂, [], x, hr, h => by
    cases t₂ with
    | branch v₂ cs₂ m₂ =>
      simp only [PTrie.refinedBy] at hr
      obtain ⟨rfl, hv, -⟩ := hr
      rw [find_branch_nil] at h ⊢
      cases v <;> cases v₂ <;> simp only [OptSlotRefines] at hv
      · exact h
      · rename_i s₁ s₂
        cases hg : Slot.get s₁ <;> simp [hg] at h
        subst h; simp [hv.get hg]
    | _ => simp [PTrie.refinedBy] at hr
  | .branch v cs m, t₂, n :: rest, x, hr, h => by
    cases t₂ <;> simp only [PTrie.refinedBy] at hr
    obtain ⟨rfl, -, hcs⟩ := hr
    rw [find_branch_cons] at h ⊢
    exact Kids.find_refinedBy cs _ n rest x hcs h
theorem Kids.find_refinedBy : ∀ (cs₁ cs₂ : Kids) (n : Nat) (key : List Nat) (x : Option Bytes),
    Kids.refinedBy cs₁ cs₂ → Kids.find cs₁ n key = some x → Kids.find cs₂ n key = some x
  | .nil, cs₂, _, _, _, hr, h => by cases cs₂ <;> simp [Kids.refinedBy] at hr; exact h
  | .none r, cs₂, 0, _, _, hr, h => by cases cs₂ <;> simp [Kids.refinedBy] at hr; exact h
  | .some c r, cs₂, 0, key, x, hr, h => by
    cases cs₂ <;> simp only [Kids.refinedBy] at hr
    simp only [Kids.find] at h ⊢; exact PTrie.find_refinedBy c _ key x hr.1 h
  | .none r, cs₂, i + 1, key, x, hr, h => by
    cases cs₂ <;> simp only [Kids.refinedBy] at hr
    simp only [Kids.find] at h ⊢; exact Kids.find_refinedBy r _ i key x hr h
  | .some c r, cs₂, i + 1, key, x, hr, h => by
    cases cs₂ <;> simp only [Kids.refinedBy] at hr
    simp only [Kids.find] at h ⊢; exact Kids.find_refinedBy r _ i key x hr.2 h
end

end NearSpec
