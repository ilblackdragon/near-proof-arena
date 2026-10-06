import ZkFormal.NearV3.Sched.Model
import ZkFormal.NearV3.Sched.Spec.Buckets

/-!
# ZkFormal.NearV3.Sched.Spec.CanonDup — `allow0` of a canonical state for any layout

The spec maps a previous-state link `(sender, receiver, a)` to link `indexOf sender · n +
indexOf receiver`, where `indexOf` is the **first** index of the id, and a later link overwrites an
earlier one. For the canonical list (record `k` = `(ids[k/n], ids[k%n], a k)`), record `k`
goes to `tgt ids k`, so `allow0[l] = a (srcOf ids l)`, the **last** record `k` with `tgt k = l`,
or 0 if there is none (`allow0_src`). Both `tgt` and `srcOf` depend on the layout only
(claim-only; the AIR's codec gets them as public data). With distinct ids, `tgt k = k` and
`srcOf l = l`.

Faithfulness note (STATUS-V3-SCHED §11): on a layout with duplicate shard ids nearcore's
`get_shard_index` uses `id_to_index_map` (the last index, `shard_layout/v2.rs:199-215`,
`v3.rs:205-216`), while the pinned spec's `indexOf` uses the first. This is unreachable on real
layouts. The AIR follows the spec.
-/

namespace ZkFormal.NearV3.Sched

open NearSpecV3 NearSpecV3.Scheduler

/-- Index of record `k`'s link under the spec's `indexOf`. -/
def tgt (ids : List Nat) (k : Nat) : Nat :=
  (indexOf ids (ids.getD (k / ids.length) 0)).getD 0 * ids.length +
    (indexOf ids (ids.getD (k % ids.length) 0)).getD 0

/-- The last record mapped to link `l`. -/
def srcOf (ids : List Nat) (l : Nat) : Option Nat :=
  ((List.range (ids.length * ids.length)).filter fun k => tgt ids k == l).getLast?

/-- `allow0` as the AIR reads it: through the source map. -/
def srcArr (ids : List Nat) (a : Nat → Nat) : Array Nat :=
  (List.range (ids.length * ids.length)).toArray.map fun l =>
    match srcOf ids l with
    | some k => a k
    | none => 0

theorem indexOf_go_some : ∀ (xs : List Nat) (s i : Nat), s ∈ xs →
    ∃ j, indexOf.go s xs i = some j ∧ i ≤ j ∧ j < i + xs.length
  | [], _, _, h => absurd h (by simp)
  | x :: xs, s, i, h => by
    unfold indexOf.go
    by_cases hx : x = s
    · exact ⟨i, by simp [hx], Nat.le_refl _, by simp⟩
    · rw [if_neg hx]
      have : s ∈ xs := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm hx
        · exact h
      obtain ⟨j, h1, h2, h3⟩ := indexOf_go_some xs s (i + 1) this
      exact ⟨j, h1, by omega, by simp; omega⟩

theorem indexOf_some_lt {ids : List Nat} {s : Nat} (h : s ∈ ids) :
    ∃ j, indexOf ids s = some j ∧ j < ids.length := by
  obtain ⟨j, h1, -, h3⟩ := indexOf_go_some ids s 0 h
  exact ⟨j, h1, by omega⟩

theorem getD_mem {ids : List Nat} {i : Nat} (h : i < ids.length) : ids.getD i 0 ∈ ids := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; exact List.getElem_mem h

theorem tgt_lt {ids : List Nat} {k : Nat} (hk : k < ids.length * ids.length) :
    tgt ids k < ids.length * ids.length := by
  have hn : 0 < ids.length := by
    rcases Nat.eq_zero_or_pos ids.length with h | h
    · rw [h] at hk; omega
    · exact h
  obtain ⟨s, hs, hsl⟩ := indexOf_some_lt (getD_mem (ids := ids) (i := k / ids.length)
    (Nat.div_lt_of_lt_mul hk))
  obtain ⟨r, hr, hrl⟩ := indexOf_some_lt (getD_mem (ids := ids) (i := k % ids.length)
    (Nat.mod_lt _ hn))
  unfold tgt; rw [hs, hr]; simp only [Option.getD_some]
  have : s * ids.length + r < (s + 1) * ids.length := by rw [Nat.succ_mul]; omega
  exact Nat.lt_of_lt_of_le this (Nat.mul_le_mul_right _ hsl)

/-- Folding `set!` over a list of in-bounds writes: the last write to `i` wins. -/
theorem foldl_set (l : List (Nat × Nat)) (arr : Array Nat) (hlt : ∀ p ∈ l, p.1 < arr.size) (i : Nat) :
    (l.foldl (fun a p => a.set! p.1 p.2) arr)[i]? =
      match (l.filter fun p => p.1 == i).getLast? with
      | some p => some p.2
      | none => arr[i]? := by
  induction l using snoc_induction with
  | h0 => simp
  | hs l p ih =>
    have hsz : (l.foldl (fun a p => a.set! p.1 p.2) arr).size = arr.size := by
      clear ih hlt
      induction l generalizing arr with
      | nil => rfl
      | cons q l ihl => simp only [List.foldl_cons]; rw [ihl]; simp
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds, List.filter_append]
    by_cases hp : p.1 = i
    · subst hp
      simp only [ite_true, hsz, hlt p (by simp), List.filter_cons, beq_self_eq_true,
        List.filter_nil, List.getLast?_append, List.getLast?_singleton]
      simp
    · rw [if_neg hp, ih (fun q hq => hlt q (by simp [hq]))]
      have : ([p].filter fun q => q.1 == i) = [] := by simp [hp]
      rw [this, List.append_nil]

theorem foldl_ext {α β : Type} (f g : α → β → α) : ∀ (l : List β) (a : α),
    (∀ x ∈ l, ∀ b, f b x = g b x) → l.foldl f a = l.foldl g a
  | [], _, _ => rfl
  | x :: l, a, h => by
    simp only [List.foldl_cons]
    rw [h x (by simp) a]
    exact foldl_ext f g l _ (fun y hy b => h y (by simp [hy]) b)

/-- **`allow0` of a canonical state, any layout.** -/
theorem allow0_src (ids : List Nat) (a : Nat → Nat) :
    let n := ids.length
    let links : List NearSpec.Bandwidth.LinkAllowance :=
      (List.range (n * n)).map fun l => ⟨ids.getD (l / n) 0, ids.getD (l % n) 0, a l⟩
    links.foldl (fun (arr : Array Nat) la =>
        match indexOf ids la.sender, indexOf ids la.receiver with
        | some s, some r => arr.set! (s * n + r) la.allowance
        | _, _ => arr) (Array.replicate (n * n) 0)
      = srcArr ids a := by
  intro n links
  have hfold : links.foldl (fun (arr : Array Nat) la =>
        match indexOf ids la.sender, indexOf ids la.receiver with
        | some s, some r => arr.set! (s * n + r) la.allowance
        | _, _ => arr) (Array.replicate (n * n) 0) =
      ((List.range (n * n)).map fun k => (tgt ids k, a k)).foldl (fun arr p => arr.set! p.1 p.2)
        (Array.replicate (n * n) 0) := by
    simp only [links, List.foldl_map]
    apply foldl_ext
    intro k hk arr
    have hk' := List.mem_range.1 hk
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · simp only [n] at h hk'; rw [h] at hk'; omega
      · exact h
    obtain ⟨s', hs, -⟩ := indexOf_some_lt (getD_mem (ids := ids) (i := k / n) (Nat.div_lt_of_lt_mul hk'))
    obtain ⟨r', hr, -⟩ := indexOf_some_lt (getD_mem (ids := ids) (i := k % n) (Nat.mod_lt _ hn))
    simp only [hs, hr, tgt, n, Option.getD_some]
  rw [hfold]
  apply Array.ext_getElem?
  intro l
  rw [foldl_set _ _ (fun p hp => by
    simp only [List.mem_map, List.mem_range] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    simpa using tgt_lt hk)]
  unfold srcArr srcOf
  rw [List.filter_map, List.getLast?_map]
  simp only [n] at *
  generalize hf : (List.filter ((fun p => p.1 == l) ∘ fun k => (tgt ids k, a k))
    (List.range (ids.length * ids.length))).getLast? = o
  have ho : (List.filter (fun k => tgt ids k == l) (List.range (ids.length * ids.length))).getLast? = o := by
    rw [← hf]; rfl
  by_cases hl : l < ids.length * ids.length
  · simp only [Array.getElem?_map, Array.getElem?_replicate, hl, ite_true, List.getElem?_toArray,
      List.getElem?_range, Option.map_some, ho]
    cases o <;> rfl
  · have : o = none := by
      rw [← ho, List.getLast?_eq_none_iff, List.filter_eq_nil_iff]
      intro k hk h
      have := tgt_lt (List.mem_range.1 hk)
      simp at h; omega
    subst this
    simp [hl]

end ZkFormal.NearV3.Sched
