import ZkFormal.Near.Spec.Prune

/-!
# ZkFormal.Near.Spec.PruneLemmas — `prune` keeps hashes, `get`, `set`

* `prune_hashOf` — pruning keeps the node hash;
* `prune_nil` — pruning to no key is the hash stub;
* `prune_wf`, `prune_revealed` — widths are kept, revealed bytes do not grow;
* `prune_get`, `prune_set` — for a key of `keys`, `get`/`set` commute with
  pruning;
* `vl_prune` — every revealed value of a pruned trie is the slot of a key.
-/

namespace ZkFormal.Near.Prune

open NearSpec NearSpec.TransferV1

theorem toRef_valueRef (s : Slot) : (toRef s).valueRef = s.valueRef := by cases s <;> rfl

theorem toRef_get (s : Slot) : (toRef s).get = none := by cases s <;> rfl

theorem kidsBitmap_pruneKids (keys : List (List Nat)) :
    ∀ (j : Nat) (cs : Kids) (i : Nat), kidsBitmap (pruneKids keys j cs) i = kidsBitmap cs i
  | _, .nil, _ => rfl
  | j, .none r, i => by
    simp only [pruneKids, kidsBitmap]; exact kidsBitmap_pruneKids keys _ r _
  | j, .some c r, i => by
    simp only [pruneKids, kidsBitmap]; rw [kidsBitmap_pruneKids keys _ r]

theorem count_pruneKids (keys : List (List Nat)) :
    ∀ (j : Nat) (cs : Kids), Kids.count (pruneKids keys j cs) = Kids.count cs
  | _, .nil => rfl
  | j, .none r => by simp only [pruneKids, Kids.count]; exact count_pruneKids keys _ r
  | j, .some c r => by simp only [pruneKids, Kids.count]; rw [count_pruneKids keys _ r]

theorem isEmpty_false_of_mem {α : Type} {l : List α} {a : α} (h : a ∈ l) : l.isEmpty = false := by
  cases l with
  | nil => cases h
  | cons _ _ => rfl

theorem mem_afterExt {k key : List Nat} {keys : List (List Nat)} (h : key ∈ keys)
    (hp : isPrefix k key = true) : key.drop k.length ∈ afterExt k keys := by
  simp only [afterExt, List.mem_filterMap]; exact ⟨key, h, by simp [hp]⟩

theorem mem_afterNib {j : Nat} {rest : List Nat} {keys : List (List Nat)} (h : (j :: rest) ∈ keys) :
    rest ∈ afterNib j keys := by
  simp only [afterNib, List.mem_filterMap]; exact ⟨_, h, by simp⟩

theorem of_mem_afterExt {k key' : List Nat} {keys : List (List Nat)} (h : key' ∈ afterExt k keys) :
    ∃ key ∈ keys, isPrefix k key = true ∧ key' = key.drop k.length := by
  simp only [afterExt, List.mem_filterMap] at h
  obtain ⟨key, hk, he⟩ := h
  by_cases hp : isPrefix k key = true
  · simp only [hp, ↓reduceIte, Option.some.injEq] at he; exact ⟨key, hk, hp, he.symm⟩
  · simp [hp] at he

theorem of_mem_afterNib {j : Nat} {rest : List Nat} {keys : List (List Nat)}
    (h : rest ∈ afterNib j keys) : (j :: rest) ∈ keys := by
  simp only [afterNib, List.mem_filterMap] at h
  obtain ⟨key, hk, he⟩ := h
  match key, he with
  | x :: r, he =>
    by_cases hx : x = j
    · subst hx; simp only [↓reduceIte, Option.some.injEq] at he; subst he; exact hk
    · simp [hx] at he

/-! ## Hash -/

mutual
theorem prune_hashOf : ∀ (keys : List (List Nat)) (t : PTrie), (prune keys t).hashOf = t.hashOf
  | _, .hash _ => rfl
  | keys, .leaf k v mem => by
    simp only [prune]; split <;> rfl
  | keys, .ext k c mem => by
    simp only [prune]; split
    · rfl
    · simp only [PTrie.hashOf]; rw [prune_hashOf]
  | keys, .branch v cs mem => by
    simp only [prune]; split
    · rfl
    · have hk := pruneKids_hashes keys 0 cs
      cases v with
      | none => simp only [Option.map, ite_self, PTrie.hashOf, hk, kidsBitmap_pruneKids]
      | some s =>
        split <;> simp only [Option.map_some, PTrie.hashOf, hk, kidsBitmap_pruneKids,
          toRef_valueRef]
theorem pruneKids_hashes : ∀ (keys : List (List Nat)) (j : Nat) (cs : Kids),
    Kids.hashes (pruneKids keys j cs) = Kids.hashes cs
  | _, _, .nil => rfl
  | keys, j, .none r => by
    simp only [pruneKids, Kids.hashes]; exact pruneKids_hashes keys _ r
  | keys, j, .some c r => by
    simp only [pruneKids, Kids.hashes]; rw [prune_hashOf, pruneKids_hashes]
end

theorem prune_nil (t : PTrie) : prune [] t = .hash t.hashOf := by
  cases t with
  | hash h => rfl
  | leaf k v mem => simp [prune]
  | ext k c mem => simp [prune, afterExt]
  | branch v cs mem => simp [prune]

/-! ## Widths and revealed bytes -/

theorem hashOf_length : ∀ (t : PTrie), t.wf = true → t.hashOf.length = 32
  | .hash h, hw => by simpa [PTrie.wf, PTrie.hashOf] using hw
  | .leaf _ _ _, _ => ArenaCore.sha256_length _
  | .ext _ _ _, _ => ArenaCore.sha256_length _
  | .branch none _ _, _ => ArenaCore.sha256_length _
  | .branch (some _) _ _, _ => ArenaCore.sha256_length _

theorem slotOk_toRef (s : Slot) (h : slotOk s = true) : slotOk (toRef s) = true := by
  cases s with
  | val v => simp only [slotOk, decide_eq_true_eq] at h; simp [toRef, slotOk, h, ArenaCore.sha256_length]
  | ref len hh => exact h

mutual
theorem prune_wf : ∀ (keys : List (List Nat)) (t : PTrie), t.wf = true → (prune keys t).wf = true
  | _, .hash _, hw => hw
  | keys, .leaf k v mem, hw => by
    simp only [prune]; split
    · exact hw
    · simp [PTrie.wf, hashOf_length _ hw]
  | keys, .ext k c mem, hw => by
    simp only [prune]; split
    · simp [PTrie.wf, hashOf_length _ hw]
    · simp only [PTrie.wf, Bool.and_eq_true] at hw ⊢
      exact ⟨⟨⟨hw.1.1.1, prune_wf _ c hw.1.1.2⟩, hw.1.2⟩, hw.2⟩
  | keys, .branch v cs mem, hw => by
    simp only [prune]; split
    · simp [PTrie.wf, hashOf_length _ hw]
    · simp only [PTrie.wf, Bool.and_eq_true] at hw ⊢
      refine ⟨⟨?_, pruneKids_wf keys 0 cs 16 hw.1.2⟩, hw.2⟩
      have h1 := hw.1.1
      by_cases hc : keys.contains [] = true
      · simp only [hc, ↓reduceIte]; exact h1
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        cases v with
        | none => rfl
        | some s => exact slotOk_toRef s h1
theorem pruneKids_wf : ∀ (keys : List (List Nat)) (j : Nat) (cs : Kids) (n : Nat),
    Kids.wf cs n = true → Kids.wf (pruneKids keys j cs) n = true
  | _, _, .nil, _, h => h
  | keys, j, .none r, n, h => by
    simp only [pruneKids, Kids.wf, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, pruneKids_wf keys _ r _ h.2⟩
  | keys, j, .some c r, n, h => by
    simp only [pruneKids, Kids.wf, Bool.and_eq_true] at h ⊢
    exact ⟨⟨h.1.1, prune_wf _ c h.1.2⟩, pruneKids_wf keys _ r _ h.2⟩
end

mutual
theorem prune_revealed : ∀ (keys : List (List Nat)) (t : PTrie),
    (prune keys t).revealedBytes ≤ t.revealedBytes
  | _, .hash _ => Nat.le_refl _
  | keys, .leaf k v mem => by
    simp only [prune]; split
    · exact Nat.le_refl _
    · simp [PTrie.revealedBytes]
  | keys, .ext k c mem => by
    simp only [prune]; split
    · simp [PTrie.revealedBytes]
    · simp only [PTrie.revealedBytes]; have := prune_revealed (afterExt k keys) c; omega
  | keys, .branch v cs mem => by
    simp only [prune]; split
    · simp [PTrie.revealedBytes]
    · simp only [PTrie.revealedBytes, count_pruneKids]
      have := pruneKids_revealed keys 0 cs
      by_cases hc : keys.contains [] = true
      · simp only [hc, ↓reduceIte]; omega
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        cases v with
        | none => simp only [Option.map_none]; omega
        | some s => cases s <;> simp only [Option.map_some, toRef] <;> omega
theorem pruneKids_revealed : ∀ (keys : List (List Nat)) (j : Nat) (cs : Kids),
    Kids.revealedBytes (pruneKids keys j cs) ≤ Kids.revealedBytes cs
  | _, _, .nil => Nat.le_refl _
  | keys, j, .none r => by
    simp only [pruneKids, Kids.revealedBytes]; exact pruneKids_revealed keys _ r
  | keys, j, .some c r => by
    simp only [pruneKids, Kids.revealedBytes]
    have := prune_revealed (afterNib j keys) c
    have := pruneKids_revealed keys (j + 1) r
    omega
end

/-! ## `get` and `set` -/

mutual
theorem prune_get : ∀ (keys : List (List Nat)) (t : PTrie) (key : List Nat), key ∈ keys →
    (prune keys t).get key = t.get key
  | _, .hash _, _, _ => rfl
  | keys, .leaf k v mem, key, hk => by
    simp only [prune]
    split
    · rfl
    · rename_i hc
      by_cases e : k = key
      · subst e; simp at hc; exact absurd hk hc
      · simp [PTrie.get, e]
  | keys, .ext k c mem, key, hk => by
    by_cases hp : isPrefix k key = true
    · have hm := mem_afterExt hk hp
      simp only [prune, isEmpty_false_of_mem hm, Bool.false_eq_true, ↓reduceIte, PTrie.get, hp]
      exact prune_get _ c _ hm
    · simp only [prune]; split <;> simp [PTrie.get, hp]
  | keys, .branch v cs mem, [], hk => by
    have hc : keys.contains [] = true := by simpa using hk
    simp [prune, isEmpty_false_of_mem hk, hk, PTrie.get]
  | keys, .branch v cs mem, n :: rest, hk => by
    simp only [prune, isEmpty_false_of_mem hk, Bool.false_eq_true, ↓reduceIte, PTrie.get]
    exact pruneKids_get keys 0 cs n rest (by simpa using hk)
theorem pruneKids_get : ∀ (keys : List (List Nat)) (j : Nat) (cs : Kids) (n : Nat) (rest : List Nat),
    (j + n) :: rest ∈ keys → Kids.get (pruneKids keys j cs) n rest = Kids.get cs n rest
  | _, _, .nil, _, _, _ => rfl
  | _, _, .none _, 0, _, _ => rfl
  | keys, j, .some c r, 0, rest, h => by
    simp only [pruneKids, Kids.get]; exact prune_get _ c rest (mem_afterNib (by simpa using h))
  | keys, j, .none r, n + 1, rest, h => by
    simp only [pruneKids, Kids.get]
    exact pruneKids_get keys (j + 1) r n rest (by rwa [show j + 1 + n = j + (n + 1) by omega])
  | keys, j, .some c r, n + 1, rest, h => by
    simp only [pruneKids, Kids.get]
    exact pruneKids_get keys (j + 1) r n rest (by rwa [show j + 1 + n = j + (n + 1) by omega])
end

mutual
theorem prune_set : ∀ (keys : List (List Nat)) (t : PTrie) (key : List Nat) (nv : Bytes) (t' : PTrie),
    key ∈ keys → t.set key nv = some t' → (prune keys t).set key nv = some (prune keys t')
  | _, .hash _, _, _, _, _, h => by simp [PTrie.set] at h
  | keys, .leaf k v mem, key, nv, t', hk, h => by
    simp only [PTrie.set] at h
    by_cases e : k = key
    · subst e
      cases v with
      | ref _ _ => simp [Slot.get] at h
      | val b =>
        simp only [beq_self_eq_true, ↓reduceIte, Slot.get, Option.map_some, Option.some.injEq] at h
        subst h
        have hc : keys.contains k = true := by simpa using hk
        simp [prune, hk, PTrie.set, Slot.get]
    · simp [e] at h
  | keys, .ext k c mem, key, nv, t', hk, h => by
    simp only [PTrie.set] at h
    by_cases hp : isPrefix k key = true
    · have hm := mem_afterExt hk hp
      simp only [hp, ↓reduceIte] at h
      cases hs : c.set (key.drop k.length) nv with
      | none => simp [hs] at h
      | some c' =>
        simp only [hs, Option.map_some, Option.some.injEq] at h
        subst h
        simp only [prune, isEmpty_false_of_mem hm, Bool.false_eq_true, ↓reduceIte, PTrie.set, hp,
          prune_set _ c _ nv c' hm hs, Option.map_some]
    · simp [hp] at h
  | keys, .branch v cs mem, [], nv, t', hk, h => by
    have hc : keys.contains [] = true := by simpa using hk
    simp only [PTrie.set] at h
    match v, h with
    | some (.val _), h =>
      simp only [Option.some.injEq] at h; subst h
      simp [prune, isEmpty_false_of_mem hk, hk, PTrie.set]
  | keys, .branch v cs mem, n :: rest, nv, t', hk, h => by
    simp only [PTrie.set] at h
    cases hs : Kids.set cs n rest nv with
    | none => simp [hs] at h
    | some cs' =>
      simp only [hs, Option.map_some, Option.some.injEq] at h
      subst h
      simp only [prune, isEmpty_false_of_mem hk, Bool.false_eq_true, ↓reduceIte, PTrie.set,
        pruneKids_set keys 0 cs n rest nv cs' (by simpa using hk) hs, Option.map_some]
theorem pruneKids_set : ∀ (keys : List (List Nat)) (j : Nat) (cs : Kids) (n : Nat) (rest : List Nat)
    (nv : Bytes) (cs' : Kids), (j + n) :: rest ∈ keys → Kids.set cs n rest nv = some cs' →
    Kids.set (pruneKids keys j cs) n rest nv = some (pruneKids keys j cs')
  | _, _, .nil, _, _, _, _, _, h => by simp [Kids.set] at h
  | _, _, .none _, 0, _, _, _, _, h => by simp [Kids.set] at h
  | keys, j, .some c r, 0, rest, nv, cs', hk, h => by
    simp only [Kids.set] at h
    cases hs : c.set rest nv with
    | none => simp [hs] at h
    | some c' =>
      simp only [hs, Option.map_some, Option.some.injEq] at h
      subst h
      simp only [pruneKids, Kids.set,
        prune_set _ c rest nv c' (mem_afterNib (by simpa using hk)) hs, Option.map_some]
  | keys, j, .none r, n + 1, rest, nv, cs', hk, h => by
    simp only [Kids.set] at h
    cases hs : Kids.set r n rest nv with
    | none => simp [hs] at h
    | some r' =>
      simp only [hs, Option.map_some, Option.some.injEq] at h
      subst h
      simp only [pruneKids, Kids.set, Option.map_some,
        pruneKids_set keys (j + 1) r n rest nv r'
          (by rwa [show j + 1 + n = j + (n + 1) by omega]) hs]
  | keys, j, .some c r, n + 1, rest, nv, cs', hk, h => by
    simp only [Kids.set] at h
    cases hs : Kids.set r n rest nv with
    | none => simp [hs] at h
    | some r' =>
      simp only [hs, Option.map_some, Option.some.injEq] at h
      subst h
      simp only [pruneKids, Kids.set, Option.map_some,
        pruneKids_set keys (j + 1) r n rest nv r'
          (by rwa [show j + 1 + n = j + (n + 1) by omega]) hs]
end

/-! ## Revealed values of a pruned trie are slots of keys -/

mutual
theorem vl_length : ∀ p : PTrie, (vl p).length = cnt p
  | .hash _ => rfl
  | .leaf _ _ _ => rfl
  | .ext _ c _ => by simp only [vl, cnt, List.length_cons, vl_length c]; omega
  | .branch _ cs _ => by simp only [vl, cnt, List.length_cons, vlKids_length cs]; omega
theorem vlKids_length : ∀ cs : Kids, (vlKids cs).length = cntKids cs
  | .nil => rfl
  | .none r => by simp only [vlKids, cntKids]; exact vlKids_length r
  | .some c r => by simp only [vlKids, cntKids, List.length_append, vl_length c, vlKids_length r]
end

theorem lt_of_getElem? {α : Type} {l : List α} {i : Nat} {x : α} (h : l[i]? = some x) :
    i < l.length := by
  rcases Nat.lt_or_ge i l.length with hi | hi
  · exact hi
  · rw [List.getElem?_eq_none hi] at h; cases h

mutual
theorem vl_prune : ∀ (keys : List (List Nat)) (t : PTrie) (i : Nat) (v : Bytes),
    (vl (prune keys t))[i]? = some (some v) → ∃ key ∈ keys, slotIdx (prune keys t) key = i
  | _, .hash _, i, v, h => by simp [prune, vl] at h
  | keys, .leaf k s mem, i, v, h => by
    by_cases hc : keys.contains k = true
    · simp only [prune, hc, ↓reduceIte] at h ⊢
      have hi := lt_of_getElem? h
      simp only [vl, List.length_singleton] at hi
      exact ⟨k, by simpa using hc, by simp [slotIdx]; omega⟩
    · simp only [prune, hc, Bool.false_eq_true, ↓reduceIte, vl] at h; simp at h
  | keys, .ext k c mem, i, v, h => by
    by_cases he : (afterExt k keys).isEmpty = true
    · simp only [prune, he, ↓reduceIte, vl] at h; simp at h
    · simp only [prune, he, Bool.false_eq_true, ↓reduceIte, vl] at h ⊢
      match i, h with
      | i + 1, h =>
        simp only [List.getElem?_cons_succ] at h
        obtain ⟨key', hk', hs⟩ := vl_prune _ c i v h
        obtain ⟨key, hk, -, rfl⟩ := of_mem_afterExt hk'
        exact ⟨key, hk, by simp only [slotIdx, hs]; omega⟩
  | keys, .branch bv cs mem, i, v, h => by
    by_cases he : keys.isEmpty = true
    · simp only [prune, he, ↓reduceIte, vl] at h; simp at h
    · simp only [prune, he, Bool.false_eq_true, ↓reduceIte, vl] at h ⊢
      match i, h with
      | 0, h =>
        by_cases hc : keys.contains [] = true
        · exact ⟨[], by simpa using hc, rfl⟩
        · simp only [hc, Bool.false_eq_true, ↓reduceIte, List.getElem?_cons_zero,
            Option.some.injEq] at h
          cases bv with
          | none => simp at h
          | some s => simp [toRef_get] at h
      | i + 1, h =>
        simp only [List.getElem?_cons_succ] at h
        obtain ⟨m, rest, hk, hs⟩ := vlKids_prune keys 0 cs i v h
        exact ⟨m :: rest, by simpa using hk, by simp only [slotIdx, hs]; omega⟩
theorem vlKids_prune : ∀ (keys : List (List Nat)) (j : Nat) (cs : Kids) (i : Nat) (v : Bytes),
    (vlKids (pruneKids keys j cs))[i]? = some (some v) →
    ∃ m rest, (j + m) :: rest ∈ keys ∧ slotIdxKids (pruneKids keys j cs) m rest = i
  | _, _, .nil, i, v, h => by simp [pruneKids, vlKids] at h
  | keys, j, .none r, i, v, h => by
    simp only [pruneKids, vlKids] at h ⊢
    obtain ⟨m, rest, hk, hs⟩ := vlKids_prune keys (j + 1) r i v h
    exact ⟨m + 1, rest, by rwa [show j + (m + 1) = j + 1 + m by omega], by simp only [slotIdxKids, hs]⟩
  | keys, j, .some c r, i, v, h => by
    simp only [pruneKids, vlKids] at h ⊢
    rcases Nat.lt_or_ge i (vl (prune (afterNib j keys) c)).length with hi | hi
    · rw [List.getElem?_append_left hi] at h
      obtain ⟨key', hk', hs⟩ := vl_prune _ c i v h
      exact ⟨0, key', by simpa using of_mem_afterNib hk', by simp only [slotIdxKids, hs]⟩
    · rw [List.getElem?_append_right hi] at h
      obtain ⟨m, rest, hk, hs⟩ := vlKids_prune keys (j + 1) r _ v h
      rw [vl_length] at hi
      exact ⟨m + 1, rest, by rwa [show j + (m + 1) = j + 1 + m by omega],
        by simp only [slotIdxKids, hs, vl_length]; omega⟩
end

end ZkFormal.Near.Prune
