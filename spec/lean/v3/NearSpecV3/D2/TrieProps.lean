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

end NearSpec
