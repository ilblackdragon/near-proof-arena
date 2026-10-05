import ZkFormal.Near.Render.Proof.MrkRecs

/-!
# ZkFormal.Near.Render.Proof.MrkFacts — merkle levels and `MRK` indices

`levels I j` has `size n j` nodes, all with 32-byte digests; the `MRK` index
of hashed node `(j, i)` (`qBase n j + i`) is its index among the hashed nodes
of `mrkShape n` (`hashedBefore`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near

namespace MrkGen

theorem shaN_length (b : List Nat) : (shaN b).length = 32 := by
  simp [shaN, toNats, ArenaCore.sha256_length]

theorem levelsI_len (I : Info) : ∀ j, (levels I j).length = size I.nRcpt j
  | 0 => by simp [levels, size]
  | j + 1 => by simp [levels, size, levelsI_len I j]

theorem levels_dig (I : Info) : ∀ j, ∀ m ∈ levels I j, m.dig.length = 32
  | 0, m, hm => by
    simp only [levels, List.mem_map, List.mem_range] at hm
    obtain ⟨r, _, rfl⟩ := hm; exact shaN_length _
  | j + 1, m, hm => by
    simp only [levels, List.mem_map, List.mem_range] at hm
    obtain ⟨i, hi, rfl⟩ := hm
    split
    · exact shaN_length _
    · rename_i h
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact levels_dig I j _ (List.getElem_mem _)

theorem levels_getD_dig (I : Info) (j k : Nat) (hk : k < size I.nRcpt j) :
    ((levels I j).getD k default).dig.length = 32 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [levelsI_len]; exact hk), Option.getD_some]
  exact levels_dig I j _ (List.getElem_mem _)

theorem lv_getD (I : Info) {j : Nat} (hj : j < I.nRcpt + 2) :
    ((List.range (I.nRcpt + 2)).map (levels I)).getD j [] = levels I j := by
  simp [List.getD_eq_getElem?_getD, hj]

/-! ## hashed indices -/

variable (n : Nat)

theorem level_hashed (sp : Nat) : ∀ s, 2 * s ≤ sp + 1 →
    (((List.range s).map fun i => decide (2 * i + 1 < sp)).filter id).length = min s (sp / 2)
  | 0, _ => by simp
  | s + 1, h => by
    rw [List.range_succ, List.map_append, List.filter_append, List.length_append, level_hashed sp s (by omega)]
    simp only [List.map_cons, List.map_nil]
    by_cases hh : 2 * s + 1 < sp <;> simp [hh] <;> omega

/-- In `mrkLevels f (j0+1) (size n j0)`, the hashed nodes before position `k`. -/
theorem levels_hashedBefore : ∀ f j0, 1 ≤ size n j0 → size n j0 ≤ f → ∀ k
    (hk : k < (mrkLevels f (j0 + 1) (size n j0)).length),
    (mrkLevels f (j0 + 1) (size n j0))[k].2.2 = true →
    (((mrkLevels f (j0 + 1) (size n j0)).take k).filter (·.2.2)).length + qBase n (j0 + 1) =
      qBase n (mrkLevels f (j0 + 1) (size n j0))[k].1 + (mrkLevels f (j0 + 1) (size n j0))[k].2.1
  | 0, _, h1, h2, _, hk, _ => absurd hk (by simp [mrkLevels])
  | f + 1, j0, h1, h2, k, hk, hh => by
    have hs : size n (j0 + 1) = (size n j0 + 1) / 2 := rfl
    have e : mrkLevels (f + 1) (j0 + 1) (size n j0) =
        ((List.range (size n (j0 + 1))).map fun i => (j0 + 1, i, decide (2 * i + 1 < size n j0))) ++
          (if size n (j0 + 1) = 1 then [] else mrkLevels f (j0 + 1 + 1) (size n (j0 + 1))) := by
      simp only [mrkLevels, ← hs]
    simp only [e] at hk hh ⊢
    by_cases hkl : k < size n (j0 + 1)
    · rw [List.getElem_append_left (by simpa using hkl)] at hh ⊢
      simp only [List.getElem_map, List.getElem_range] at hh ⊢
      rw [List.take_append_of_le_length (by simp; omega), ← List.map_take, List.take_range, List.filter_map]
      simp only [decide_eq_true_eq] at hh
      have : ((List.range (min k (size n (j0 + 1)))).filter
          ((fun x : Nat × Nat × Bool => x.2.2) ∘ fun i => (j0 + 1, i, decide (2 * i + 1 < size n j0)))) =
          List.range (min k (size n (j0 + 1))) := by
        apply List.filter_eq_self.2; intro i hi; simp at hi ⊢; omega
      rw [this]; simp; omega
    · have hne : ¬ size n (j0 + 1) = 1 := by
        intro h1'; simp [h1'] at hk; omega
      simp only [hne, if_false] at hk hh ⊢
      have hk' : k - size n (j0 + 1) < (mrkLevels f (j0 + 1 + 1) (size n (j0 + 1))).length := by
        simp at hk; omega
      rw [List.getElem_append_right (by simp; omega)] at hh ⊢
      simp only [List.length_map, List.length_range] at hh ⊢
      have ih := levels_hashedBefore f (j0 + 1) (by omega) (by omega) (k - size n (j0 + 1)) hk' hh
      rw [List.take_append, List.filter_append, List.length_append, List.take_of_length_le (by simp; omega)]
      simp only [List.length_map, List.length_range]
      rw [List.filter_map, List.length_map]
      have hc := level_hashed (size n j0) (size n (j0 + 1)) (by omega)
      rw [List.filter_map, List.length_map] at hc
      have hq : qBase n (j0 + 1 + 1) = qBase n (j0 + 1) + size n j0 / 2 := by
        cases j0 with
        | zero => simp [qBase, size]
        | succ j0 => rfl
      simp only [Function.comp_def, id] at hc ⊢
      omega

end MrkGen

end ZkFormal.Near.Render
