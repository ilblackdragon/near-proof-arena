import ZkFormal.Near.Spec.CompleteWalk

/-!
# ZkFormal.Near.Spec.CompleteSize — widths and revealed size of the records

* `prune_recs_wf` — the records of a pruned well-formed trie are `NodeRec.wf`
  when every key is shorter than 512 nibbles;
* `revealedOf_recs` — `revealedOf (recs p b) ≤ p.revealedBytes` when every
  revealed value has at least 72 bytes.
-/

namespace ZkFormal.Near.Prune

open NearSpec NearSpec.TransferV1

theorem isPrefix_length {k key : List Nat} (h : isPrefix k key = true) : k.length ≤ key.length := by
  rw [isPrefix_eq h, List.length_append]; omega

theorem kidOf_ne_none (p : PTrie) (id : Nat) : kidOf p id ≠ .none := by
  cases p <;> simp [kidOf]

theorem kidOf_wf (p : PTrie) (id : Nat) (h : p.wf = true) : (kidOf p id).wf := by
  cases p with
  | hash hh => simpa [kidOf, Kid.wf, PTrie.wf] using h
  | _ => trivial

theorem kidsList_length_wf : ∀ (cs : Kids) (n id : Nat), Kids.wf cs n = true → (kidsList cs id).length = n
  | .nil, n, _, h => by simp [Kids.wf] at h; simp [kidsList, h]
  | .none r, n, id, h => by
    simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp only [kidsList, List.length_cons, kidsList_length_wf r _ id h.2]; omega
  | .some c r, n, id, h => by
    simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp only [kidsList, List.length_cons, kidsList_length_wf r _ _ h.2]; omega

theorem kidsList_wf : ∀ (cs : Kids) (n id : Nat), Kids.wf cs n = true → ∀ kid ∈ kidsList cs id, kid.wf
  | .nil, _, _, _ => by simp [kidsList]
  | .none r, n, id, h => by
    simp only [Kids.wf, Bool.and_eq_true] at h
    intro kid hk
    simp only [kidsList, List.mem_cons] at hk
    rcases hk with rfl | hk
    · trivial
    · exact kidsList_wf r _ id h.2 kid hk
  | .some c r, n, id, h => by
    simp only [Kids.wf, Bool.and_eq_true] at h
    intro kid hk
    simp only [kidsList, List.mem_cons] at hk
    rcases hk with rfl | hk
    · exact kidOf_wf c id h.1.2
    · exact kidsList_wf r _ _ h.2 kid hk

theorem vslot_wf (s : Slot) (h : slotOk s = true) : (vslot s).wf := by
  cases s with
  | val _ => trivial
  | ref len hh =>
    simp only [slotOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact ⟨by simpa using h.1, h.2⟩

theorem mem_afterExt_short {k : List Nat} {keys : List (List Nat)}
    (hk : ∀ key ∈ keys, key.length < 512) : ∀ key ∈ afterExt k keys, key.length < 512 := by
  intro key' h
  obtain ⟨key, hm, _, rfl⟩ := of_mem_afterExt h
  have := hk key hm; simp; omega

theorem mem_afterNib_short {j : Nat} {keys : List (List Nat)}
    (hk : ∀ key ∈ keys, key.length < 512) : ∀ key ∈ afterNib j keys, key.length < 512 := by
  intro key' h
  have := hk _ (of_mem_afterNib h); simp at this; omega

mutual
theorem prune_recs_wf : ∀ (keys : List (List Nat)) (t : PTrie) (b : Nat), t.wf = true →
    (∀ key ∈ keys, key.length < 512) → ∀ nr ∈ recs (prune keys t) b, nr.wf
  | _, .hash _, _, _, _ => by simp [prune, recs]
  | keys, .leaf k v mem, b, hw, hk => by
    by_cases hc : keys.contains k = true
    · simp only [prune, hc, ↓reduceIte, recs, List.mem_singleton]
      rintro nr rfl
      simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
      exact ⟨hw.1.1.1, hk k (by simpa using hc), vslot_wf v hw.1.1.2, by simpa using hw.1.2⟩
    · have hc' : k ∉ keys := by simpa using hc
      simp [prune, hc', recs]
  | keys, .ext k c mem, b, hw, hk => by
    by_cases he : (afterExt k keys).isEmpty = true
    · simp [prune, he, recs]
    · simp only [prune, he, Bool.false_eq_true, ↓reduceIte, recs, List.mem_cons]
      simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
      rintro nr (rfl | hnr)
      · obtain ⟨key', hm⟩ : ∃ key', key' ∈ afterExt k keys := by
          cases h : afterExt k keys with
          | nil => simp [h] at he
          | cons a _ => exact ⟨a, by simp⟩
        obtain ⟨key, hkey, hp, -⟩ := of_mem_afterExt hm
        have := isPrefix_length hp
        have := hk key hkey
        exact ⟨hw.1.1.1, by omega, kidOf_ne_none _ _, kidOf_wf _ _ (prune_wf _ c hw.1.1.2),
          by simpa using hw.1.2⟩
      · exact prune_recs_wf _ c (b + 1) hw.1.1.2 (mem_afterExt_short hk) nr hnr
  | keys, .branch v cs mem, b, hw, hk => by
    by_cases he : keys.isEmpty = true
    · simp [prune, he, recs]
    · simp only [prune, he, Bool.false_eq_true, ↓reduceIte, recs, List.mem_cons]
      simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
      have hkw := pruneKids_wf keys 0 cs 16 hw.1.2
      rintro nr (rfl | hnr)
      · refine ⟨kidsList_length_wf _ 16 _ hkw, ?_, kidsList_wf _ 16 _ hkw, by simpa using hw.2⟩
        intro s hs
        have h1 := hw.1.1
        by_cases hc : keys.contains [] = true
        · simp only [hc, ↓reduceIte] at hs
          cases v with
          | none => simp at hs
          | some s' => simp at hs; subst hs; exact vslot_wf s' h1
        · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hs
          cases v with
          | none => simp at hs
          | some s' => simp at hs; subst hs; exact vslot_wf _ (slotOk_toRef s' h1)
      · exact pruneKids_recs_wf keys 0 cs (b + 1) 16 hw.1.2 hk nr hnr
theorem pruneKids_recs_wf : ∀ (keys : List (List Nat)) (j : Nat) (cs : Kids) (b n : Nat),
    Kids.wf cs n = true → (∀ key ∈ keys, key.length < 512) →
    ∀ nr ∈ recsKids (pruneKids keys j cs) b, nr.wf
  | _, _, .nil, _, _, _, _ => by simp [pruneKids, recsKids]
  | keys, j, .none r, b, n, hw, hk => by
    simp only [Kids.wf, Bool.and_eq_true] at hw
    simp only [pruneKids, recsKids]
    exact pruneKids_recs_wf keys (j + 1) r b _ hw.2 hk
  | keys, j, .some c r, b, n, hw, hk => by
    simp only [Kids.wf, Bool.and_eq_true] at hw
    simp only [pruneKids, recsKids, List.mem_append]
    rintro nr (hnr | hnr)
    · exact prune_recs_wf _ c b hw.1.2 (mem_afterNib_short hk) nr hnr
    · exact pruneKids_recs_wf keys (j + 1) r _ _ hw.2 hk nr hnr
end

/-! ## Revealed size -/

theorem revealedOf_cons (a : NodeRec) (l : List NodeRec) :
    revealedOf (a :: l) = nodeSize a + revealedOf l := by simp [revealedOf]

theorem revealedOf_append (l₁ l₂ : List NodeRec) :
    revealedOf (l₁ ++ l₂) = revealedOf l₁ + revealedOf l₂ := by simp [revealedOf]

theorem zeros_length : ∀ n, (zeros n).length = n
  | 0 => rfl
  | n + 1 => by simp [zeros, zeros_length n]

theorem kidBytes_length (p : PTrie) (id : Nat) (h : p.wf = true) :
    (kidBytes (fun _ => zeros 32) (kidOf p id)).length = 32 := by
  cases p with
  | hash hh => simpa [kidOf, kidBytes, PTrie.wf] using h
  | _ => simp [kidOf, kidBytes, zeros_length]

theorem concatAll_length (l : List Bytes) : (concatAll l).length = (l.map List.length).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [concatAll, ih]

theorem kidsList_bytes : ∀ (cs : Kids) (n id : Nat), Kids.wf cs n = true →
    (concatAll ((kidsList cs id).map (kidBytes fun _ => zeros 32))).length = 32 * Kids.count cs
  | .nil, _, _, _ => rfl
  | .none r, n, id, h => by
    simp only [Kids.wf, Bool.and_eq_true] at h
    have := kidsList_bytes r _ id h.2
    simp only [concatAll_length] at this ⊢
    simp only [kidsList, List.map_cons, List.sum_cons, kidBytes, List.length_nil, Nat.zero_add,
      Kids.count]
    exact this
  | .some c r, n, id, h => by
    simp only [Kids.wf, Bool.and_eq_true] at h
    have := kidsList_bytes r _ (id + cnt c) h.2
    simp only [concatAll_length] at this ⊢
    simp only [kidsList, List.map_cons, List.sum_cons, this, kidBytes_length c id h.1.2, Kids.count]
    omega

theorem vref_length (s : Slot) (h : slotOk s = true) : (vrefBytes (zeros 32) (vslot s)).length = 36 := by
  cases s with
  | val _ => simp [vslot, vrefBytes, leN_length, u32, zeros_length]
  | ref len hh =>
    simp only [slotOk, Bool.and_eq_true, beq_iff_eq] at h
    simp [vslot, vrefBytes, leN_length, u32, h.2]

mutual
theorem revealedOf_recs : ∀ (p : PTrie) (b : Nat), p.wf = true →
    (∀ (i : Nat) (v : Bytes), (vl p)[i]? = some (some v) → 72 ≤ v.length) → revealedOf (recs p b) ≤ p.revealedBytes
  | .hash _, _, _, _ => by simp [recs, revealedOf]
  | .leaf k s mem, b, hw, hv => by
    simp only [PTrie.wf, Bool.and_eq_true] at hw
    have e : revealedOf (recs (.leaf k s mem) b) = nodeSize (.leaf k (vslot s) mem) := by
      simp [recs, revealedOf]
    rw [e]
    simp only [nodeSize, ser, PTrie.revealedBytes, List.length_append, List.length_singleton,
      vref_length s hw.1.1.2, u32, u64, leN_length]
    cases s with
    | val x =>
      have := hv 0 x (by simp [vl, Slot.get])
      simp [vslot, NodeRec.touched]; omega
    | ref _ _ => simp [vslot, NodeRec.touched]
  | .ext k c mem, b, hw, hv => by
    simp only [PTrie.wf, Bool.and_eq_true] at hw
    have ih := revealedOf_recs c (b + 1) hw.1.1.2 (fun i v h => hv (i + 1) v (by simpa [vl] using h))
    simp only [recs, revealedOf_cons, nodeSize, ser, PTrie.revealedBytes]
    simp only [List.length_append, List.length_singleton, kidBytes_length c _ hw.1.1.2, u32, u64,
      leN_length, NodeRec.touched]
    simp; omega
  | .branch bv cs mem, b, hw, hv => by
    simp only [PTrie.wf, Bool.and_eq_true] at hw
    have ih := revealedOf_recsKids cs (b + 1) hw.1.2 (fun i v h => hv (i + 1) v (by simpa [vl] using h))
    have hk := kidsList_bytes cs 16 (b + 1) hw.1.2
    simp only [recs, revealedOf_cons, PTrie.revealedBytes]
    cases bv with
    | none =>
      simp only [Option.map_none, nodeSize, ser, List.length_append, List.length_singleton, hk,
        u16, u64, leN_length, NodeRec.touched]
      simp; omega
    | some s =>
      have hs : slotOk s = true := by simpa using hw.1.1
      simp only [Option.map_some, nodeSize, ser, List.length_append, List.length_singleton, hk,
        u16, u64, leN_length, vref_length s hs]
      cases s with
      | val x =>
        have := hv 0 x (by simp [vl, Slot.get])
        simp [vslot, NodeRec.touched]; omega
      | ref _ _ => simp [vslot, NodeRec.touched]; omega
theorem revealedOf_recsKids : ∀ (cs : Kids) (b : Nat) {n : Nat}, Kids.wf cs n = true →
    (∀ (i : Nat) (v : Bytes), (vlKids cs)[i]? = some (some v) → 72 ≤ v.length) →
    revealedOf (recsKids cs b) ≤ Kids.revealedBytes cs
  | .nil, _, _, _, _ => by simp [recsKids, revealedOf]
  | .none r, b, _, hw, hv => by
    simp only [Kids.wf, Bool.and_eq_true] at hw
    simp only [recsKids, Kids.revealedBytes]
    exact revealedOf_recsKids r b hw.2 (by simpa [vlKids] using hv)
  | .some c r, b, _, hw, hv => by
    simp only [Kids.wf, Bool.and_eq_true] at hw
    simp only [recsKids, Kids.revealedBytes, revealedOf_append]
    have h1 := revealedOf_recs c b hw.1.2 (fun i v h => hv i v (by
      simp only [vlKids]; rw [List.getElem?_append_left (lt_of_getElem? h)]; exact h))
    have h2 := revealedOf_recsKids r (b + cnt c) hw.2 (fun i v h => hv (cnt c + i) v (by
      simp only [vlKids]
      rw [List.getElem?_append_right (by rw [vl_length]; omega), vl_length]
      simpa using h))
    omega
end

end ZkFormal.Near.Prune
