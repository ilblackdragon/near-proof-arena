import ZkFormal.NearV3.Assembly.ForestStore

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

private theorem filter_add_partition {α : Type} (p q : α → Bool)
    (h : ∀ x, !(p x && q x) = true) : ∀ xs : List α,
    (xs.filter p).length + (xs.filter q).length = (xs.filter fun x => p x || q x).length
  | [] => rfl
  | x :: xs => by
    have ih := filter_add_partition p q h xs
    have hx := h x
    cases hp : p x <;> cases hq : q x <;> simp [hp, hq] at hx ⊢ <;> omega

private def headGe (i : Nat) (k : List Nat) : Bool :=
  match k.head? with | some n => decide (i ≤ n) | none => false

private theorem head_partition (i : Nat) (keys : List (List Nat)) :
    (keys.filter (fun k => k.head? == some i)).length + (keys.filter (headGe (i+1))).length =
      (keys.filter (headGe i)).length := by
  have he := filter_add_partition (fun k : List Nat => k.head? == some i) (headGe (i+1))
    (fun k => by cases k with
                 | nil => simp [headGe]
                 | cons n ns => simp [headGe]; omega) keys
  have hp : (fun k : List Nat => (k.head? == some i) || headGe (i+1) k) = headGe i := by
    funext k
    cases k with
    | nil => rfl
    | cons n ns =>
      apply Bool.eq_iff_iff.mpr
      simp [headGe]
      omega
  rw [hp] at he
  exact he

private theorem empty_partition (keys : List (List Nat)) :
    (keys.filter (· == [])).length + (keys.filter (headGe 0)).length = keys.length := by
  induction keys with
  | nil => rfl
  | cons k ks ih => cases k <;> simp [headGe] at * <;> omega

 theorem mkSlot_value_count (s : Store) (len : Nat) (vh : Bytes) (want : Bool) :
    (slotVal (mkSlot s len vh want)).length ≤ if want then 1 else 0 := by
  cases want <;> simp only [mkSlot, Bool.false_eq_true, ite_false, slotVal, List.length_nil,
    Bool.true_eq, ite_true]
  · omega
  · split <;> simp [slotVal] <;> split <;> simp [slotVal]

theorem buildKidsWith_value_count (g : Bytes → List (List Nat) → PTrie)
    (hg : ∀ root keys, (valsOf (g root keys)).length ≤ keys.length) :
    ∀ hs i keys, (kvals (buildKidsWith g i hs keys)).length ≤ (keys.filter (headGe i)).length
  | [], _, _ => by simp [buildKidsWith, kvals_nil]
  | none :: hs, i, keys => by
    have ih := buildKidsWith_value_count g hg hs (i+1) keys
    have he := head_partition i keys
    simpa only [buildKidsWith, kvals_none] using (show
      (kvals (buildKidsWith g (i+1) hs keys)).length ≤ (keys.filter (headGe i)).length by omega)
  | some root :: hs, i, keys => by
    have ih := buildKidsWith_value_count g hg hs (i+1) keys
    have hc := hg root ((keys.filter (fun k => k.head? == some i)).map (·.drop 1))
    have he := head_partition i keys
    simp only [List.length_map] at hc
    simp only [buildKidsWith, kvals_some, List.length_append]
    omega

private theorem any_filter_count {α : Type} (p : α → Bool) (xs : List α) :
    (if xs.any p then 1 else 0) ≤ (xs.filter p).length := by
  split
  · rename_i h
    obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp h
    have hm : x ∈ xs.filter p := List.mem_filter.mpr ⟨hx, hp⟩
    exact List.length_pos_of_mem hm
  · omega

theorem branchWith_value_count (g : Bytes → List (List Nat) → PTrie)
    (hg : ∀ root keys, (valsOf (g root keys)).length ≤ keys.length)
    (root : Bytes) (v : Option Slot) (rest : Bytes) (keys : List (List Nat)) (mem : Nat)
    (hv : (optSlotVal v).length ≤ (keys.filter (· == [])).length) :
    (valsOf (branchWith g root v rest keys mem)).length ≤ keys.length := by
  unfold branchWith
  dsimp only
  split
  · simp [valsOf, occs]
  · have hc := buildKidsWith_value_count g hg (kidHashes 16 (leNat (rest.take 2)) (rest.drop 2)) 0 keys
    have hp := empty_partition keys
    simp only [valsOf_branch, List.length_append]
    omega

/-- A native builder reveals at most one value occurrence for each requested key. -/
theorem buildFor_value_count (s : Store) : ∀ fuel root keys,
    (valsOf (buildFor s fuel root keys)).length ≤ keys.length := by
  intro fuel
  induction fuel with
  | zero => intro root keys; simp [buildFor, valsOf, occs]
  | succ f ih =>
    intro root keys
    rw [buildFor]
    split
    · simp [valsOf, occs]
    · split
      · simp [valsOf, occs]
      · rename_i node hn
        split
        · simp [valsOf, occs]
        · dsimp only
          split
          · rename_i rest hb
            split
            · rename_i k hp
              split
              · simp [valsOf, occs]
              · have hs := mkSlot_value_count s (leNat ((rest.drop (4 + leNat (rest.take 4))).take 4))
                  ((rest.drop (4 + leNat (rest.take 4))).drop 4) (keys.any (· == k))
                have ha := any_filter_count (· == k) keys
                have hf := List.length_filter_le (fun x => x == k) keys
                simp only [valsOf_leaf]
                omega
            · simp [valsOf, occs]
          · rename_i rest hb
            split
            · rename_i k hp
              split
              · simp [valsOf, occs]
              · have hc := ih (rest.drop (4 + leNat (rest.take 4)))
                  ((keys.filter (isPrefix k)).map (·.drop k.length))
                have hf := List.length_filter_le (isPrefix k) keys
                simp only [valsOf_ext, List.length_map] at hc ⊢
                omega
            · simp [valsOf, occs]
          · exact branchWith_value_count _ ih _ none _ _ _ (by simp [optSlotVal])
          · rename_i rest hb
            split
            · simp [valsOf, occs]
            · apply branchWith_value_count _ ih
              have hs := mkSlot_value_count s (leNat (rest.take 4)) ((rest.drop 4).take 32)
                (keys.any (· == []))
              have ha := any_filter_count (· == []) keys
              exact Nat.le_trans hs ha
          · simp [valsOf, occs]

 theorem partialTrie_value_count (ws : List Bytes) (root : Bytes) (keys : List (List Nat)) :
    (valsOf (partialTrie ws root keys)).length ≤ keys.length :=
  buildFor_value_count (mkStore ws) trieFuel root keys

end ZkFormal.NearV3.Assembly
