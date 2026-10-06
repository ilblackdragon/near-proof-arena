import ZkFormal.NearV3.Link.Post3

/-!
# ZkFormal.NearV3.Link.Post3Writes — `valsPost` as a list of value replacements

`valsPost vs es pv = setVals (valsOf3 vs es) (writesOf vs es pv)`, where `writesOf` lists
`(t, pv vid_t)` for every written value record position `t` (increasing, so distinct): the
post value records of `post_tau` are the replacements of `post_eq_sets` (`Post3Spec`).
-/

namespace ZkFormal.NearV3

open NearSpec

theorem lookup_mem {j : Nat} {w : Bytes} : ∀ (ws : List (Nat × Bytes)), ws.lookup j = some w → j ∈ ws.map Prod.fst
  | [], h => by simp [List.lookup] at h
  | (a, b) :: r, h => by
    by_cases e : j = a
    · subst e; simp
    · have : (j == a) = false := by simpa using e
      simp only [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (lookup_mem r h)

/-- `setVals` at distinct positions: position `j` takes the value written to it, if any. -/
theorem setVals_get? : ∀ (ws : List (Nat × Bytes)) (V : List ValRec3), (ws.map Prod.fst).Nodup →
    ∀ j, (setVals V ws)[j]? =
      match ws.lookup j with
      | some v => V[j]?.map fun r => ⟨r.tau, v⟩
      | none => V[j]?
  | [], V, _, j => by simp [setVals, List.lookup]
  | (i, v) :: ws, V, hd, j => by
    simp only [List.map_cons, List.nodup_cons] at hd
    simp only [setVals]
    rw [setVals_get? ws _ hd.2 j]
    by_cases hj : j = i
    · subst hj
      have hn : ws.lookup j = none := by
        cases hl : ws.lookup j with
        | none => rfl
        | some w => exact absurd (lookup_mem ws hl) hd.1
      simp [List.lookup, hn, setVal_get?]
    · have hji : (j == i) = false := by simpa using hj
      simp only [List.lookup, hji]
      cases ws.lookup j <;> simp [setVal_get?, hj]

theorem lookup_filter_map (p : Nat → Bool) (h : Nat → Bytes) (j : Nat) : ∀ (l : List Nat),
    ((l.filter p).map fun t => (t, h t)).lookup j = if j ∈ l ∧ p j = true then some (h j) else none
  | [] => by simp
  | a :: r => by
    have ih := lookup_filter_map p h j r
    by_cases e : j = a
    · subst e
      cases hp : p j <;> simp [List.filter, hp, ih]
    · have : (j == a) = false := by simpa using e
      cases hp : p a <;> simp [List.filter, hp, List.lookup, this, ih, e]

end ZkFormal.NearV3

namespace ZkFormal.NearV3.Link3

open NearSpec ZkFormal.Near

/-- The writes of the instance tables: `(t, pv vid_t)` for every written value record. -/
def writesOf (vs : List NodeS3) (es : List ValE) (pv : Nat → Bytes) : List (Nat × Bytes) :=
  ((List.range es.length).filter fun t => wrote vs (es.getD t default).vid).map
    fun t => (t, pv (es.getD t default).vid)

theorem writesOf_nodup (vs : List NodeS3) (es : List ValE) (pv : Nat → Bytes) :
    ((writesOf vs es pv).map Prod.fst).Nodup := by
  unfold writesOf
  rw [List.map_map]
  have : (Prod.fst ∘ fun t => (t, pv (es.getD t default).vid)) = id := by funext t; rfl
  rw [this, List.map_id]
  exact (List.nodup_range).filter _

/-- **The post value records are the writes applied to the pre value records.** -/
theorem valsPost_eq_setVals (vs : List NodeS3) (es : List ValE) (pv : Nat → Bytes) :
    valsPost vs es pv = setVals (valsOf3 vs es) (writesOf vs es pv) := by
  apply List.ext_getElem?; intro j
  rw [setVals_get? _ _ (writesOf_nodup vs es pv) j]
  unfold writesOf
  rw [lookup_filter_map]
  by_cases hj : j < es.length
  · have hg : es.getD j default = es[j] := by simp [List.getD_eq_getElem?_getD, hj]
    rw [hg]
    cases hw : wrote vs es[j].vid <;> simp [valsPost, valsOf3, hj, hw]
  · have h1 : (valsPost vs es pv)[j]? = none := by simp [valsPost]; omega
    have h2 : (valsOf3 vs es)[j]? = none := by simp [valsOf3]; omega
    rw [h1, h2]
    split <;> simp

end ZkFormal.NearV3.Link3
