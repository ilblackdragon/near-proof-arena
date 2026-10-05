import ZkFormal.Near.Spec.Small
import ZkFormal.Near.Spec.Complete

/-!
# ZkFormal.Near.Spec.SmallComplete — the pruned records are `Small`

`small_complete : NearRelation c w → Small (extOf c w)`: in `prune keys t`
every touched slot / dead branch ends the walk of some key, and distinct
terminal nodes end distinct keys, so there are at most `|keys|` of them
(`tc_prune`, by the same mutual recursion as `prune`).
-/

namespace ZkFormal.Near

open NearSpec NearSpec.TransferV1

namespace Prune

/-- Number of terminal records. -/
def tc (l : List NodeRec) : Nat := (l.filter NodeRec.terminal).length

theorem tc_cons (a : NodeRec) (l : List NodeRec) :
    tc (a :: l) = (if a.terminal then 1 else 0) + tc l := by
  simp only [tc, List.filter_cons]; split <;> simp <;> omega

theorem tc_append (l₁ l₂ : List NodeRec) : tc (l₁ ++ l₂) = tc l₁ + tc l₂ := by
  simp [tc, List.filter_append]

/-- `key` starts with a nibble `≥ j`. -/
def nibGe (j : Nat) : List Nat → Bool
  | x :: _ => decide (j ≤ x)
  | [] => false

def nibEq (j : Nat) : List Nat → Bool
  | x :: _ => decide (x = j)
  | [] => false

theorem afterNib_length (j : Nat) :
    ∀ keys : List (List Nat), (afterNib j keys).length = keys.countP (nibEq j)
  | [] => rfl
  | key :: keys => by
    have ih := afterNib_length j keys
    simp only [afterNib] at ih ⊢
    rw [List.filterMap_cons, List.countP_cons]
    match key with
    | [] => simp [nibEq, ih]
    | x :: rest =>
      by_cases hx : x = j
      · simp [nibEq, hx, ih]
      · simp [nibEq, hx, ih]

theorem countP_nibGe (j : Nat) :
    ∀ keys : List (List Nat), keys.countP (nibGe j) = keys.countP (nibEq j) + keys.countP (nibGe (j + 1))
  | [] => rfl
  | key :: keys => by
    have ih := countP_nibGe j keys
    simp only [List.countP_cons]
    match key with
    | [] => simp [nibGe, nibEq, ih]
    | x :: rest =>
      simp only [nibGe, nibEq, decide_eq_true_eq]
      by_cases h1 : x = j
      · subst h1; simp [Nat.not_succ_le_self]; omega
      · by_cases h2 : j ≤ x
        · have : j + 1 ≤ x := by omega
          simp [h1, h2, this]; omega
        · have : ¬ j + 1 ≤ x := by omega
          simp [h1, h2, this]; omega

theorem countP_nibGe0 :
    ∀ keys : List (List Nat), keys.countP (nibGe 0) + keys.countP List.isEmpty = keys.length
  | [] => rfl
  | key :: keys => by
    have ih := countP_nibGe0 keys
    simp only [List.countP_cons, List.length_cons]
    match key with
    | [] => simp [nibGe]; omega
    | x :: rest => simp [nibGe]; omega

theorem countP_nil_pos {keys : List (List Nat)} (h : keys.contains [] = true) :
    1 ≤ keys.countP List.isEmpty := by
  have : [] ∈ keys := by simpa using h
  exact List.countP_pos_iff.2 ⟨[], this, by simp⟩

theorem length_pos_of_isEmpty {keys : List (List Nat)} (h : ¬ keys.isEmpty = true) :
    1 ≤ keys.length := by
  cases keys with
  | nil => simp at h
  | cons _ _ => simp

theorem kidOf_beq_none (p : PTrie) (id : Nat) : (kidOf p id == Kid.none) = false := by
  cases p <;> rfl

theorem recsKids_nil_of_dead :
    ∀ (cs : Kids) (id b : Nat), (kidsList cs id).all (· == Kid.none) = true → recsKids cs b = []
  | .nil, _, _, _ => rfl
  | .none r, id, b, h => by
    simp only [kidsList, List.all_cons] at h
    simp only [recsKids]
    exact recsKids_nil_of_dead r id b (by simpa using h)
  | .some c r, id, _, h => by
    simp [kidsList, List.all_cons, kidOf_beq_none] at h

theorem vslot_toRef_touched (v : Option Slot) (kids : List Kid) (mem : Nat) :
    (NodeRec.branch ((v.map toRef).map vslot) kids mem).touched = false := by
  cases v with
  | none => rfl
  | some s => cases s <;> rfl

mutual
theorem tc_prune : ∀ (keys : List (List Nat)) (t : PTrie) (b : Nat),
    tc (recs (prune keys t) b) ≤ keys.length
  | _, .hash _, _ => by simp [prune, recs, tc]
  | keys, .leaf k v mem, b => by
    simp only [prune]; split
    · rename_i hk
      have : 1 ≤ keys.length := by
        cases keys with
        | nil => simp at hk
        | cons _ _ => simp
      simp only [recs, tc_cons]; simp [tc]; split <;> omega
    · simp [recs, tc]
  | keys, .ext k c mem, b => by
    simp only [prune]; split
    · simp [recs, tc]
    · simp only [recs, tc_cons]
      have h1 := tc_prune (afterExt k keys) c (b + 1)
      have h2 : (afterExt k keys).length ≤ keys.length := List.length_filterMap_le _ _
      simp [NodeRec.terminal, NodeRec.touched, NodeRec.dead]; omega
  | keys, .branch v cs mem, b => by
    simp only [prune]; split
    · simp [recs, tc]
    · rename_i hne
      have hk := tc_pruneKids keys 0 cs (b + 1)
      have h0 := countP_nibGe0 keys
      simp only [recs, tc_cons]
      by_cases hc : keys.contains [] = true
      · have := countP_nil_pos hc
        have : ∀ x : Bool, (if x = true then 1 else 0) ≤ 1 := by intro x; split <;> omega
        have := this (NodeRec.terminal (NodeRec.branch (Option.map vslot (if keys.contains [] = true then v else Option.map toRef v))
          (kidsList (pruneKids keys 0 cs) (b + 1)) mem))
        omega
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        have hpos := length_pos_of_isEmpty hne
        by_cases hd : (NodeRec.branch ((v.map toRef).map vslot)
            (kidsList (pruneKids keys 0 cs) (b + 1)) mem).dead = true
        · have hnil : recsKids (pruneKids keys 0 cs) (b + 1) = [] := by
            cases v with
            | none => exact recsKids_nil_of_dead _ _ _ hd
            | some s => simp [NodeRec.dead] at hd
          rw [hnil]; simp [tc]; split <;> omega
        · have ht : (NodeRec.branch ((v.map toRef).map vslot)
              (kidsList (pruneKids keys 0 cs) (b + 1)) mem).terminal = false := by
            simp only [NodeRec.terminal, vslot_toRef_touched, Bool.false_or]
            simpa using hd
          rw [ht]; simp only [Bool.false_eq_true, ↓reduceIte]; omega
theorem tc_pruneKids : ∀ (keys : List (List Nat)) (j : Nat) (cs : Kids) (b : Nat),
    tc (recsKids (pruneKids keys j cs) b) ≤ keys.countP (nibGe j)
  | _, _, .nil, _ => by simp [pruneKids, recsKids, tc]
  | keys, j, .none r, b => by
    simp only [pruneKids, recsKids]
    have := tc_pruneKids keys (j + 1) r b
    have := countP_nibGe j keys
    omega
  | keys, j, .some c r, b => by
    simp only [pruneKids, recsKids, tc_append]
    have h1 := tc_prune (afterNib j keys) c b
    have h2 := tc_pruneKids keys (j + 1) r (b + cnt (prune (afterNib j keys) c))
    have h3 := countP_nibGe j keys
    rw [afterNib_length] at h1
    omega
end

/-! ## Key lengths -/

theorem isPrefix_len : ∀ (k key : List Nat), isPrefix k key = true → k.length ≤ key.length
  | [], _, _ => Nat.zero_le _
  | _ :: _, [], h => by simp [isPrefix] at h
  | a :: k, b :: key, h => by
    simp only [isPrefix, Bool.and_eq_true] at h
    have := isPrefix_len k key h.2; simp; omega

mutual
theorem keys_prune : ∀ (keys : List (List Nat)) (t : PTrie) (b M : Nat), (∀ key ∈ keys, key.length ≤ M) →
    ∀ nr ∈ recs (prune keys t) b, nr.key.length ≤ M
  | _, .hash _, _, _, _, nr, h => by simp [prune, recs] at h
  | keys, .leaf k v mem, b, M, hk, nr, h => by
    simp only [prune] at h; split at h
    · rename_i hc
      simp only [recs, List.mem_singleton] at h; subst h
      exact hk k (by simpa using hc)
    · simp [recs] at h
  | keys, .ext k c mem, b, M, hk, nr, h => by
    simp only [prune] at h; split at h
    · simp [recs] at h
    · rename_i hne
      have hk' : ∀ key ∈ afterExt k keys, key.length ≤ M := by
        intro key hm
        simp only [afterExt, List.mem_filterMap] at hm
        obtain ⟨key', hm', he⟩ := hm
        split at he
        · simp at he; subst he; have := hk key' hm'; simp; omega
        · cases he
      simp only [recs, List.mem_cons] at h
      rcases h with rfl | h
      · obtain ⟨key, hm⟩ := List.exists_mem_of_ne_nil _ (by simpa using hne)
        simp only [afterExt, List.mem_filterMap] at hm
        obtain ⟨key', hm', he⟩ := hm
        split at he
        · rename_i hp
          have := isPrefix_len k key' hp; have := hk key' hm'; simp [NodeRec.key]; omega
        · cases he
      · exact keys_prune _ c (b + 1) M hk' nr h
  | keys, .branch v cs mem, b, M, hk, nr, h => by
    simp only [prune] at h; split at h
    · simp [recs] at h
    · simp only [recs, List.mem_cons] at h
      rcases h with rfl | h
      · simp [NodeRec.key]
      · exact keys_pruneKids keys 0 cs (b + 1) M hk nr h
theorem keys_pruneKids : ∀ (keys : List (List Nat)) (j : Nat) (cs : Kids) (b M : Nat),
    (∀ key ∈ keys, key.length ≤ M) → ∀ nr ∈ recsKids (pruneKids keys j cs) b, nr.key.length ≤ M
  | _, _, .nil, _, _, _, nr, h => by simp [pruneKids, recsKids] at h
  | keys, j, .none r, b, M, hk, nr, h => by
    simp only [pruneKids, recsKids] at h
    exact keys_pruneKids keys (j + 1) r b M hk nr h
  | keys, j, .some c r, b, M, hk, nr, h => by
    simp only [pruneKids, recsKids, List.mem_append] at h
    rcases h with h | h
    · refine keys_prune (afterNib j keys) c b M (fun key hm => ?_) nr h
      simp only [afterNib, List.mem_filterMap] at hm
      obtain ⟨key', hm', he⟩ := hm
      cases key' with
      | nil => simp at he
      | cons x rest =>
        simp at he; obtain ⟨_, rfl⟩ := he; have := hk _ hm'; simp at this; omega
    · exact keys_pruneKids keys (j + 1) r _ M hk nr h
end

end Prune

open Prune in
/-- **The pruned records are `Small`.** -/
theorem small_complete (c : Claim) (w : Witness) (h : NearRelation c w) : Small (extOf c w) := by
  have hg := good_complete c w h
  refine ⟨?_, ?_⟩
  rotate_left
  · intro nr hnr
    have hk : ∀ key ∈ keysOf w, key.length ≤ 130 := by
      intro key hm
      simp only [keysOf, List.mem_map] at hm
      obtain ⟨r, hr, rfl⟩ := hm
      have hin : r.inSlice = true := List.all_eq_true.1 hg.inSlice r (by simpa [extOf] using hr)
      have := inSlice_receiver_length hin
      simp [accountKeyPath, nibbles_length]; omega
    have := keys_prune (keysOf w) w.trie 0 130 hk nr (by simpa [extOf, prunedOf] using hnr)
    omega
  have h1 := tc_prune (keysOf w) w.trie 0
  have h2 : (keysOf w).length = (extOf c w).rs.length := by simp [keysOf, extOf]
  have := hg.len; have := hg.n_le
  show tc (recs (prunedOf w) 0) ≤ _
  simp only [prunedOf]; omega

end ZkFormal.Near
