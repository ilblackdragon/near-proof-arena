import NearSpecV3.D2.Trie
import NearSpec.TrieUpsertProofs

/-!
# Properties of the D2 trie operations (proved)

* `PTrie.del_false` — a deletion that does not delete (`deleted = false`) returns the trie
  unchanged, so a removal of an absent key never changes the state root.
* `PTrie.find_del` — `PTrie.del` is a map deletion: after `t.del k = some (true, x)` the key
  `k` is absent and every other key answers exactly as before (present with value, proven
  absent, or undetermined), where `x = none` is the empty trie. Hence the post-state of a
  deletion is the key→value map with `k` removed; with `PTrie.find_upsert_*` (v2) this covers
  every write of `finalize`. Not proved: that the squashed node shapes and memory usages are
  nearcore's canonical ones (tested: `nearspec-v3-test-trie-d2`).
-/

namespace NearSpec

theorem PTrie.del_false (t : PTrie) (k : List Nat) (x : Option PTrie)
    (h : t.del k = some (false, x)) : x = some t := by
  cases t with
  | hash h' => simp [PTrie.del] at h
  | leaf k' s m =>
    unfold PTrie.del at h
    split at h <;> simp_all
  | ext k' c m =>
    unfold PTrie.del at h
    split at h
    · split at h
      · split at h
        · simp at h
        · rename_i c'' _
          cases hx : extendChild k' c'' <;> simp_all
      · simp_all
      · simp at h
    · simp_all
  | branch v cs m =>
    cases k with
    | nil =>
      cases v with
      | none => simp [PTrie.del] at h; exact h.symm
      | some s =>
        simp only [PTrie.del] at h
        cases hx : squashBranch none cs (m - valueMem s.len) <;> simp_all
    | cons n rest =>
      unfold PTrie.del at h
      split at h
      · simp at h
      · simp_all
      · rename_i cs' old new _
        cases hx : squashBranch v cs' (m - old + new) <;> simp_all


/-- Lookup in a possibly empty trie. -/
def findOpt : Option PTrie → List Nat → Option (Option Bytes)
  | none, _ => some none
  | some t, k => t.find k

theorem isPrefix_append_iff (k k2 key : List Nat) :
    isPrefix (k ++ k2) key = (isPrefix k key && isPrefix k2 (key.drop k.length)) := by
  induction k generalizing key with
  | nil => simp [isPrefix]
  | cons a as ih =>
    cases key with
    | nil => simp [isPrefix]
    | cons b bs => simp [isPrefix, ih, Bool.and_assoc]

theorem append_eq_iff_prefix (k k2 key : List Nat) :
    (k ++ k2 = key) ↔ (isPrefix k key = true ∧ k2 = key.drop k.length) := by
  constructor
  · rintro rfl; exact ⟨isPrefix_append _ _, by simp⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨r, rfl⟩ := (isPrefix_iff _ _).1 h1
    simp at h2; subst h2; rfl

/-- `extendChild` behaves like an extension over the child. -/
theorem find_extendChild (k : List Nat) (c : PTrie) (r : Option PTrie)
    (h : extendChild k c = some r) (key : List Nat) :
    findOpt r key = if isPrefix k key then c.find (key.drop k.length) else some none := by
  cases c with
  | hash _ => simp [extendChild] at h
  | leaf k2 s m =>
    simp only [extendChild, Option.some.injEq] at h; subst h
    simp only [findOpt, find_leaf]
    by_cases hp : isPrefix k key = true
    · obtain ⟨rq, rfl⟩ := (isPrefix_iff _ _).1 hp
      simp only [isPrefix_append, ↓reduceIte, List.drop_left, List.append_cancel_left_eq]
    · have : ¬ (k ++ k2 = key) := fun h' => hp ((append_eq_iff_prefix k k2 key).1 h').1
      simp [this, hp]
  | ext k2 cc m =>
    simp only [extendChild, Option.some.injEq] at h; subst h
    simp only [findOpt, find_ext, isPrefix_append_iff, List.length_append, List.drop_drop]
    by_cases hp : isPrefix k key = true
    · simp [hp, Nat.add_comm]
    · simp [hp]
  | branch v cs m =>
    simp only [extendChild, Option.some.injEq] at h; subst h
    simp [findOpt, find_ext]

theorem Kids.present_ge : ∀ (cs : Kids) (j : Nat) (i : Nat) (c : PTrie),
    (i, c) ∈ Kids.present cs j → j ≤ i
  | .nil, _, _, _, h => by simp [Kids.present] at h
  | .none r, j, i, c, h => by
    simp only [Kids.present] at h
    have := Kids.present_ge r (j + 1) i c h; omega
  | .some c' r, j, i, c, h => by
    simp only [Kids.present, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, -⟩ | h
    · omega
    · have := Kids.present_ge r (j + 1) i c h; omega

theorem Kids.find_present_nil : ∀ (cs : Kids) (j n : Nat) (rest : List Nat),
    Kids.present cs j = [] → Kids.find cs n rest = Option.some Option.none
  | .nil, _, _, _, _ => by simp [Kids.find]
  | .none r, j, n, rest, h => by
    simp only [Kids.present] at h
    cases n with
    | zero => simp [Kids.find]
    | succ n => simp only [Kids.find]; exact Kids.find_present_nil r (j + 1) n rest h
  | .some _ _, _, _, _, h => by simp [Kids.present] at h

theorem Kids.find_present_one : ∀ (cs : Kids) (j n : Nat) (rest : List Nat) (i : Nat) (c : PTrie),
    Kids.present cs j = [(i, c)] → Kids.find cs n rest = if n + j = i then c.find rest else Option.some Option.none
  | .nil, _, _, _, _, _, h => by simp [Kids.present] at h
  | .none r, j, n, rest, i, c, h => by
    simp only [Kids.present] at h
    have hge := Kids.present_ge r (j + 1) i c (by rw [h]; simp)
    cases n with
    | zero =>
      simp only [Kids.find]
      have : ¬ (j = i) := by omega
      simp [this]
    | succ n =>
      simp only [Kids.find]
      rw [Kids.find_present_one r (j + 1) n rest i c h]
      have : (n + (j + 1) = i) ↔ (n + 1 + j = i) := by omega
      simp only [this]
  | .some c' r, j, n, rest, i, c, h => by
    simp only [Kids.present, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, h2⟩ := h
    cases n with
    | zero => simp [Kids.find]
    | succ n =>
      simp only [Kids.find]
      rw [Kids.find_present_nil r (j + 1) n rest h2]
      have : ¬ (n + 1 + j = j) := by omega
      simp [this]

/-- `squashBranch` preserves every lookup of the branch it replaces. -/
theorem find_squashBranch (v : Option Slot) (cs : Kids) (m : Nat) (r : Option PTrie)
    (h : squashBranch v cs m = some r) (key : List Nat) :
    findOpt r key = (PTrie.branch v cs m).find key := by
  unfold squashBranch at h
  split at h
  · -- no children, no value
    rename_i hp
    simp only [Option.some.injEq] at h; subst h
    cases key with
    | nil => simp [findOpt, PTrie.find]
    | cons n rest => simp [findOpt, PTrie.find, Kids.find_present_nil cs 0 n rest hp]
  · rename_i hp
    simp only [Option.some.injEq] at h; subst h
    cases key with
    | nil => simp [findOpt, PTrie.find]
    | cons n rest =>
      simp [findOpt, PTrie.find, Kids.find_present_nil cs 0 n rest hp, isPrefix]
  · rename_i i c hp
    rw [find_extendChild [i] c r h key]
    cases key with
    | nil => simp [isPrefix, PTrie.find]
    | cons n rest =>
      simp only [PTrie.find, Kids.find_present_one cs 0 n rest i c hp, Nat.add_zero, isPrefix,
        Bool.and_true, beq_iff_eq, List.length_cons, List.length_nil, Nat.zero_add,
        List.drop_succ_cons, List.drop_zero]
      by_cases e : i = n
      · simp [e]
      · have : ¬ n = i := fun h => e h.symm
        simp [e, this]
  · simp only [Option.some.injEq] at h; subst h; rfl

mutual
/-- `PTrie.del` is a map deletion (see the module docstring). -/
theorem PTrie.find_del : ∀ (t : PTrie) (k : List Nat) (x : Option PTrie),
    t.del k = some (true, x) → ∀ key, findOpt x key = if key = k then some none else t.find key
  | .hash _, _, _, h => by simp [PTrie.del] at h
  | .leaf k' s m, k, x, h => by
    intro key
    simp only [PTrie.del] at h
    by_cases e : k' = k
    · simp only [e, ↓reduceIte, Option.some.injEq, Prod.mk.injEq, true_and] at h; subst h; subst e
      by_cases e2 : key = k'
      · simp [e2, findOpt]
      · have : ¬ k' = key := fun h => e2 h.symm
        simp [e2, findOpt, find_leaf, this]
    · simp [e] at h
  | .ext k' c m, k, x, h => by
    intro key
    simp only [PTrie.del] at h
    by_cases hp : isPrefix k' k = true
    · simp only [hp, ↓reduceIte] at h
      cases hm : c.mem? <;> cases hd : c.del (k.drop k'.length) <;> simp [hm, hd] at h
      rename_i cm r
      obtain ⟨b, c'⟩ := r
      cases b with
      | false => simp at h
      | true =>
        have ih := PTrie.find_del c (k.drop k'.length) c' hd
        obtain ⟨rk, rfl⟩ := (isPrefix_iff _ _).1 hp
        have hfx : findOpt x key = if isPrefix k' key then findOpt c' (key.drop k'.length) else some none := by
          cases c' with
          | none => simp at h; subst h; by_cases hq : isPrefix k' key = true <;> simp [findOpt, hq]
          | some c'' =>
            simp only [Option.map_eq_some_iff] at h
            obtain ⟨r', hr', hx⟩ := h
            simp only [Prod.mk.injEq, true_and] at hx; subst hx
            rw [find_extendChild k' c'' r' hr' key]; simp [findOpt]
        rw [hfx, find_ext]
        by_cases hq : isPrefix k' key = true
        · obtain ⟨rq, rfl⟩ := (isPrefix_iff _ _).1 hq
          simp only [isPrefix_append, ↓reduceIte, List.drop_left] at ih ⊢
          rw [ih rq]
          by_cases e : rq = rk
          · subst e; simp
          · have : ¬ (k' ++ rq = k' ++ rk) := by simpa using e
            simp [e, this]
        · have : ¬ (key = k' ++ rk) := by
            rintro rfl; exact hq (isPrefix_append _ _)
          simp [hq, this]
    · simp [hp] at h
  | .branch v cs m, [], x, h => by
    intro key
    cases v with
    | none => simp [PTrie.del] at h
    | some s =>
      simp only [PTrie.del, Option.map_eq_some_iff, Prod.mk.injEq, true_and] at h
      obtain ⟨r, hr, rfl⟩ := h
      rw [find_squashBranch none cs _ r hr key]
      cases key with
      | nil => simp [PTrie.find]
      | cons n rest => simp [PTrie.find]
  | .branch v cs m, n :: rest, x, h => by
    intro key
    simp only [PTrie.del] at h
    cases hk : Kids.delAt cs n rest with
    | none => simp [hk] at h
    | some o =>
      cases o with
      | none => simp [hk] at h
      | some q =>
        obtain ⟨cs', a, b⟩ := q
        simp only [hk, Option.map_eq_some_iff, Prod.mk.injEq, true_and] at h
        obtain ⟨r, hr, rfl⟩ := h
        rw [find_squashBranch v cs' _ r hr key]
        cases key with
        | nil => cases v <;> simp [PTrie.find]
        | cons n2 rest2 =>
          simp only [PTrie.find]
          rw [Kids.find_delAt cs n rest cs' a b hk n2 rest2]

theorem Kids.find_delAt : ∀ (cs : Kids) (n : Nat) (rest : List Nat) (cs' : Kids) (a b : Nat),
    Kids.delAt cs n rest = some (some (cs', a, b)) → ∀ n2 rest2,
      Kids.find cs' n2 rest2 = if n2 :: rest2 = n :: rest then Option.some Option.none else Kids.find cs n2 rest2
  | .nil, _, _, _, _, _, h => by simp [Kids.delAt] at h
  | .none _, 0, _, _, _, _, h => by simp [Kids.delAt] at h
  | .some c r, 0, rest, cs', a, b, h => by
    intro n2 rest2
    simp only [Kids.delAt] at h
    cases hm : c.mem? <;> cases hd : c.del rest <;> simp [hm, hd] at h
    rename_i cm q
    obtain ⟨d, c'⟩ := q
    cases d with
    | false => simp at h
    | true =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -, -⟩ := h
      have ih := PTrie.find_del c rest c' hd
      cases n2 with
      | zero =>
        have := ih rest2
        cases c' with
        | none => simp only [findOpt] at this; simp [Kids.find, ← this]
        | some c'' => simp only [findOpt] at this; simp [Kids.find, this]
      | succ n2 => cases c' <;> simp [Kids.find]
  | .none r, i + 1, rest, cs', a, b, h => by
    intro n2 rest2
    simp only [Kids.delAt] at h
    cases hd : Kids.delAt r i rest with
    | none => simp [hd] at h
    | some o =>
      cases o with
      | none => simp [hd] at h
      | some q =>
        obtain ⟨k, a', b'⟩ := q
        simp only [hd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -, -⟩ := h
        cases n2 with
        | zero => simp [Kids.find]
        | succ n2 =>
          simp only [Kids.find]
          rw [Kids.find_delAt r i rest k a' b' hd n2 rest2]
          simp
  | .some c r, i + 1, rest, cs', a, b, h => by
    intro n2 rest2
    simp only [Kids.delAt] at h
    cases hd : Kids.delAt r i rest with
    | none => simp [hd] at h
    | some o =>
      cases o with
      | none => simp [hd] at h
      | some q =>
        obtain ⟨k, a', b'⟩ := q
        simp only [hd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -, -⟩ := h
        cases n2 with
        | zero => simp [Kids.find]
        | succ n2 =>
          simp only [Kids.find]
          rw [Kids.find_delAt r i rest k a' b' hd n2 rest2]
          simp
end


/-! ## Prefix iteration returns present keys (soundness) -/

mutual
theorem PTrie.allKeys_sound : ∀ (t : PTrie) (acc : List Nat) (ks : List (List Nat)),
    t.allKeys acc = some ks → ∀ k ∈ ks, ∃ r v, k = acc ++ r ∧ t.find r = some (some v)
  | .hash _, _, _, h => by simp [PTrie.allKeys] at h
  | .leaf k s m, acc, ks, h => by
    intro k' hk
    cases s with
    | val v =>
      simp only [PTrie.allKeys, Option.some.injEq] at h; subst h
      simp only [List.mem_singleton] at hk; subst hk
      exact ⟨k, v, rfl, by simp [PTrie.find, Slot.get]⟩
    | ref _ _ => simp [PTrie.allKeys] at h
  | .ext k c m, acc, ks, h => by
    intro k' hk
    simp only [PTrie.allKeys] at h
    obtain ⟨r, v, rfl, hf⟩ := PTrie.allKeys_sound c (acc ++ k) ks h k' hk
    refine ⟨k ++ r, v, by simp, ?_⟩
    simp [PTrie.find, isPrefix_append, hf]
  | .branch bv cs m, acc, ks, h => by
    intro k' hk
    simp only [PTrie.allKeys] at h
    cases bv with
    | none =>
      cases hc : Kids.allKeys cs 0 acc with
      | none => simp [hc] at h
      | some kids =>
        simp only [hc, Option.bind_eq_bind, Option.bind_some, List.nil_append, Option.pure_def,
          Option.some.injEq] at h
        subst h
        obtain ⟨n, r, v, rfl, -, hf⟩ := Kids.allKeys_sound cs 0 acc kids hc k' hk
        exact ⟨n :: r, v, rfl, by simpa [PTrie.find] using hf⟩
    | some sl =>
      cases sl with
      | ref _ _ => simp [PTrie.allKeys] at h
      | val v =>
        cases hc : Kids.allKeys cs 0 acc with
        | none => simp [hc] at h
        | some kids =>
          simp only [hc, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq] at h
          subst h
          simp only [List.singleton_append, List.mem_cons] at hk
          rcases hk with rfl | hk
          · exact ⟨[], v, by simp, by simp [PTrie.find, Slot.get]⟩
          · obtain ⟨n, r, v', rfl, -, hf⟩ := Kids.allKeys_sound cs 0 acc kids hc k' hk
            exact ⟨n :: r, v', rfl, by simpa [PTrie.find] using hf⟩

theorem Kids.allKeys_sound : ∀ (cs : Kids) (i : Nat) (acc : List Nat) (ks : List (List Nat)),
    Kids.allKeys cs i acc = some ks → ∀ k ∈ ks,
      ∃ n r v, k = acc ++ n :: r ∧ i ≤ n ∧ Kids.find cs (n - i) r = Option.some (Option.some v)
  | .nil, _, _, ks, h => by
    simp only [Kids.allKeys, Option.some.injEq] at h; subst h; simp
  | .none rest, i, acc, ks, h => by
    intro k hk
    simp only [Kids.allKeys] at h
    obtain ⟨n, r, v, rfl, hn, hf⟩ := Kids.allKeys_sound rest (i + 1) acc ks h k hk
    refine ⟨n, r, v, rfl, by omega, ?_⟩
    have : n - i = (n - (i + 1)) + 1 := by omega
    rw [this]; simpa [Kids.find] using hf
  | .some c rest, i, acc, ks, h => by
    intro k hk
    simp only [Kids.allKeys] at h
    cases ha : c.allKeys (acc ++ [i]) with
    | none => simp [ha] at h
    | some a =>
      cases hb : Kids.allKeys rest (i + 1) acc with
      | none => simp [ha, hb] at h
      | some b =>
        simp only [ha, hb, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        rcases List.mem_append.1 hk with hk | hk
        · obtain ⟨r, v, rfl, hf⟩ := PTrie.allKeys_sound c (acc ++ [i]) a ha k hk
          exact ⟨i, r, v, by simp, Nat.le_refl _, by simpa [Kids.find] using hf⟩
        · obtain ⟨n, r, v, rfl, hn, hf⟩ := Kids.allKeys_sound rest (i + 1) acc b hb k hk
          refine ⟨n, r, v, rfl, by omega, ?_⟩
          have : n - i = (n - (i + 1)) + 1 := by omega
          rw [this]; simpa [Kids.find] using hf
end

theorem isPrefix_trans {a b c : List Nat} (h1 : isPrefix a b = true) (h2 : isPrefix b c = true) :
    isPrefix a c = true := by
  obtain ⟨r1, rfl⟩ := (isPrefix_iff _ _).1 h1
  obtain ⟨r2, rfl⟩ := (isPrefix_iff _ _).1 h2
  rw [List.append_assoc]; exact isPrefix_append _ _

theorem isPrefix_of_find_ext {k r : List Nat} {c : PTrie} {m : Nat} {v : Bytes}
    (h : (PTrie.ext k c m).find r = some (some v)) : isPrefix k r = true := by
  cases hn : isPrefix k r with
  | true => rfl
  | false => simp [PTrie.find, hn] at h

mutual
/-- Every key returned by the prefix iteration has the prefix and is present with a value. -/
theorem PTrie.prefixKeys_sound : ∀ (t : PTrie) (pre acc : List Nat) (ks : List (List Nat)),
    t.prefixKeys pre acc = some ks → ∀ k ∈ ks,
      ∃ r v, k = acc ++ r ∧ isPrefix pre r = true ∧ t.find r = some (some v)
  | .hash _, _, _, _, h => by simp [PTrie.prefixKeys] at h
  | .leaf k s m, pre, acc, ks, h => by
    intro k' hk
    simp only [PTrie.prefixKeys] at h
    by_cases hp : isPrefix pre k = true
    · simp only [hp, ↓reduceIte] at h
      obtain ⟨r, v, rfl, hf⟩ := PTrie.allKeys_sound _ acc ks h k' hk
      have hkr : k = r := by
        by_cases hne : k = r
        · exact hne
        · simp [PTrie.find, hne] at hf
      subst hkr
      exact ⟨k, v, rfl, hp, hf⟩
    · simp [hp] at h; subst h; simp at hk
  | .ext k c m, pre, acc, ks, h => by
    intro k' hk
    simp only [PTrie.prefixKeys] at h
    by_cases hp : isPrefix k pre = true
    · simp only [hp, ↓reduceIte] at h
      obtain ⟨r, v, rfl, hpr, hf⟩ := PTrie.prefixKeys_sound c (pre.drop k.length) (acc ++ k) ks h k' hk
      refine ⟨k ++ r, v, by simp, ?_, by simp [PTrie.find, isPrefix_append, hf]⟩
      obtain ⟨p', rfl⟩ := (isPrefix_iff _ _).1 hp
      simp only [List.drop_left] at hpr
      simpa [isPrefix_append_append] using hpr
    · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
      by_cases hq : isPrefix pre k = true
      · simp only [hq, ↓reduceIte] at h
        obtain ⟨r, v, rfl, hf⟩ := PTrie.allKeys_sound _ acc ks h k' hk
        exact ⟨r, v, rfl, isPrefix_trans hq (isPrefix_of_find_ext hf), hf⟩
      · simp [hq] at h; subst h; simp at hk
  | .branch bv cs m, [], acc, ks, h => by
    intro k' hk
    simp only [PTrie.prefixKeys] at h
    obtain ⟨r, v, rfl, hf⟩ := PTrie.allKeys_sound _ acc ks h k' hk
    exact ⟨r, v, rfl, by simp [isPrefix], hf⟩
  | .branch bv cs m, n :: rest, acc, ks, h => by
    intro k' hk
    simp only [PTrie.prefixKeys] at h
    obtain ⟨r, v, rfl, hpr, hf⟩ := Kids.prefixKeys_sound cs n rest (acc ++ [n]) ks h k' hk
    exact ⟨n :: r, v, by simp, by simpa [isPrefix] using hpr, by simpa [PTrie.find] using hf⟩

theorem Kids.prefixKeys_sound : ∀ (cs : Kids) (n : Nat) (rest acc : List Nat) (ks : List (List Nat)),
    Kids.prefixKeys cs n rest acc = Option.some ks → ∀ k ∈ ks,
      ∃ r v, k = acc ++ r ∧ isPrefix rest r = true ∧ Kids.find cs n r = Option.some (Option.some v)
  | .nil, _, _, _, ks, h => by
    simp only [Kids.prefixKeys, Option.some.injEq] at h; subst h; simp
  | .none _, 0, _, _, ks, h => by
    simp only [Kids.prefixKeys, Option.some.injEq] at h; subst h; simp
  | .some c _, 0, rest, acc, ks, h => by
    intro k hk
    simp only [Kids.prefixKeys] at h
    obtain ⟨r, v, rfl, hpr, hf⟩ := PTrie.prefixKeys_sound c rest acc ks h k hk
    exact ⟨r, v, rfl, hpr, by simpa [Kids.find] using hf⟩
  | .none r', i + 1, rest, acc, ks, h => by
    intro k hk
    simp only [Kids.prefixKeys] at h
    obtain ⟨r, v, rfl, hpr, hf⟩ := Kids.prefixKeys_sound r' i rest acc ks h k hk
    exact ⟨r, v, rfl, hpr, by simpa [Kids.find] using hf⟩
  | .some _ r', i + 1, rest, acc, ks, h => by
    intro k hk
    simp only [Kids.prefixKeys] at h
    obtain ⟨r, v, rfl, hpr, hf⟩ := Kids.prefixKeys_sound r' i rest acc ks h k hk
    exact ⟨r, v, rfl, hpr, by simpa [Kids.find] using hf⟩
end

/-! ## Prefix iteration returns every present key with the prefix (completeness) -/

theorem isPrefix_comparable {a b r : List Nat} (ha : isPrefix a r = true) (hb : isPrefix b r = true) :
    isPrefix a b = true ∨ isPrefix b a = true := by
  induction a generalizing b r with
  | nil => left; simp [isPrefix]
  | cons x xs ih =>
    cases b with
    | nil => right; simp [isPrefix]
    | cons y ys =>
      cases r with
      | nil => simp [isPrefix] at ha
      | cons z zs =>
        simp only [isPrefix, Bool.and_eq_true, beq_iff_eq] at ha hb ⊢
        obtain ⟨rfl, ha⟩ := ha
        obtain ⟨rfl, hb⟩ := hb
        simpa using ih ha hb

mutual
theorem PTrie.allKeys_complete : ∀ (t : PTrie) (acc : List Nat) (ks : List (List Nat)),
    t.allKeys acc = some ks → ∀ r v, t.find r = some (some v) → acc ++ r ∈ ks
  | .hash _, _, _, h => by simp [PTrie.allKeys] at h
  | .leaf k s m, acc, ks, h => by
    intro r v hf
    have hkr : k = r := by
      by_cases hne : k = r
      · exact hne
      · simp [PTrie.find, hne] at hf
    subst hkr
    cases s with
    | val _ => simp only [PTrie.allKeys, Option.some.injEq] at h; subst h; simp
    | ref _ _ => simp [PTrie.allKeys] at h
  | .ext k c m, acc, ks, h => by
    intro r v hf
    have hp := isPrefix_of_find_ext hf
    obtain ⟨r', rfl⟩ := (isPrefix_iff _ _).1 hp
    simp only [PTrie.allKeys] at h
    have hf' : c.find r' = some (some v) := by simpa [PTrie.find, isPrefix_append] using hf
    simpa using PTrie.allKeys_complete c (acc ++ k) ks h r' v hf'
  | .branch bv cs m, acc, ks, h => by
    intro r v hf
    simp only [PTrie.allKeys] at h
    cases hc : Kids.allKeys cs 0 acc with
    | none =>
      cases bv with
      | none => simp [hc] at h
      | some sl => cases sl <;> simp [hc] at h
    | some kids =>
      have hkids : ∀ n r', Kids.find cs n r' = Option.some (Option.some v) → acc ++ n :: r' ∈ kids := by
        intro n r' hk
        have := Kids.allKeys_complete cs 0 acc kids hc n r' v hk
        simpa using this
      cases bv with
      | none =>
        simp only [hc, Option.bind_eq_bind, Option.bind_some, List.nil_append, Option.pure_def,
          Option.some.injEq] at h
        subst h
        cases r with
        | nil => simp [PTrie.find] at hf
        | cons n r' => exact hkids n r' (by simpa [PTrie.find] using hf)
      | some sl =>
        cases sl with
        | ref _ _ => simp [PTrie.allKeys] at h
        | val w =>
          simp only [hc, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq] at h
          subst h
          cases r with
          | nil => simp
          | cons n r' => exact List.mem_append_right _ (hkids n r' (by simpa [PTrie.find] using hf))

theorem Kids.allKeys_complete : ∀ (cs : Kids) (i : Nat) (acc : List Nat) (ks : List (List Nat)),
    Kids.allKeys cs i acc = Option.some ks → ∀ n r v,
      Kids.find cs n r = Option.some (Option.some v) → acc ++ (n + i) :: r ∈ ks
  | .nil, _, _, _, _, n, r, v, hf => by simp [Kids.find] at hf
  | .none rest, i, acc, ks, h, n, r, v, hf => by
    simp only [Kids.allKeys] at h
    cases n with
    | zero => simp [Kids.find] at hf
    | succ n =>
      have := Kids.allKeys_complete rest (i + 1) acc ks h n r v (by simpa [Kids.find] using hf)
      have e : n + (i + 1) = n + 1 + i := by omega
      rwa [e] at this
  | .some c rest, i, acc, ks, h, n, r, v, hf => by
    simp only [Kids.allKeys] at h
    cases ha : c.allKeys (acc ++ [i]) with
    | none => simp [ha] at h
    | some a =>
      cases hb : Kids.allKeys rest (i + 1) acc with
      | none => simp [ha, hb] at h
      | some b =>
        simp only [ha, hb, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        cases n with
        | zero =>
          have := PTrie.allKeys_complete c (acc ++ [i]) a ha r v (by simpa [Kids.find] using hf)
          exact List.mem_append_left _ (by simpa using this)
        | succ n =>
          have := Kids.allKeys_complete rest (i + 1) acc b hb n r v (by simpa [Kids.find] using hf)
          have e : n + (i + 1) = n + 1 + i := by omega
          rw [e] at this
          exact List.mem_append_right _ this
end

mutual
/-- Every present key with the prefix is returned by the prefix iteration. -/
theorem PTrie.prefixKeys_complete : ∀ (t : PTrie) (pre acc : List Nat) (ks : List (List Nat)),
    t.prefixKeys pre acc = some ks → ∀ r v, isPrefix pre r = true →
      t.find r = some (some v) → acc ++ r ∈ ks
  | .hash _, _, _, _, h => by simp [PTrie.prefixKeys] at h
  | .leaf k s m, pre, acc, ks, h => by
    intro r v hpr hf
    have hkr : k = r := by
      by_cases hne : k = r
      · exact hne
      · simp [PTrie.find, hne] at hf
    subst hkr
    simp only [PTrie.prefixKeys, hpr, ↓reduceIte] at h
    exact PTrie.allKeys_complete _ acc ks h k v hf
  | .ext k c m, pre, acc, ks, h => by
    intro r v hpr hf
    have hkr := isPrefix_of_find_ext hf
    simp only [PTrie.prefixKeys] at h
    by_cases hp : isPrefix k pre = true
    · simp only [hp, ↓reduceIte] at h
      obtain ⟨r', rfl⟩ := (isPrefix_iff _ _).1 hkr
      obtain ⟨p', rfl⟩ := (isPrefix_iff _ _).1 hp
      have hf' : c.find r' = some (some v) := by simpa [PTrie.find, isPrefix_append] using hf
      have hpr' : isPrefix p' r' = true := by simpa [isPrefix_append_append] using hpr
      have := PTrie.prefixKeys_complete c ((k ++ p').drop k.length) (acc ++ k) ks h r' v
        (by simpa using hpr') hf'
      simpa using this
    · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
      have hq : isPrefix pre k = true := by
        rcases isPrefix_comparable hkr hpr with h1 | h1
        · exact absurd h1 hp
        · exact h1
      simp only [hq, ↓reduceIte] at h
      exact PTrie.allKeys_complete _ acc ks h r v hf
  | .branch bv cs m, [], acc, ks, h => by
    intro r v _ hf
    simp only [PTrie.prefixKeys] at h
    exact PTrie.allKeys_complete _ acc ks h r v hf
  | .branch bv cs m, n :: rest, acc, ks, h => by
    intro r v hpr hf
    simp only [PTrie.prefixKeys] at h
    cases r with
    | nil => simp [isPrefix] at hpr
    | cons n2 r' =>
      simp only [isPrefix, Bool.and_eq_true, beq_iff_eq] at hpr
      obtain ⟨rfl, hpr⟩ := hpr
      have := Kids.prefixKeys_complete cs n rest (acc ++ [n]) ks h r' v hpr (by simpa [PTrie.find] using hf)
      simpa using this

theorem Kids.prefixKeys_complete : ∀ (cs : Kids) (n : Nat) (rest acc : List Nat) (ks : List (List Nat)),
    Kids.prefixKeys cs n rest acc = Option.some ks → ∀ r v, isPrefix rest r = true →
      Kids.find cs n r = Option.some (Option.some v) → acc ++ r ∈ ks
  | .nil, _, _, _, _, _, r, v, _, hf => by simp [Kids.find] at hf
  | .none _, 0, _, _, _, _, r, v, _, hf => by simp [Kids.find] at hf
  | .some c _, 0, rest, acc, ks, h, r, v, hpr, hf => by
    simp only [Kids.prefixKeys] at h
    exact PTrie.prefixKeys_complete c rest acc ks h r v hpr (by simpa [Kids.find] using hf)
  | .none r', i + 1, rest, acc, ks, h, r, v, hpr, hf => by
    simp only [Kids.prefixKeys] at h
    exact Kids.prefixKeys_complete r' i rest acc ks h r v hpr (by simpa [Kids.find] using hf)
  | .some _ r', i + 1, rest, acc, ks, h, r, v, hpr, hf => by
    simp only [Kids.prefixKeys] at h
    exact Kids.prefixKeys_complete r' i rest acc ks h r v hpr (by simpa [Kids.find] using hf)
end

end NearSpec
