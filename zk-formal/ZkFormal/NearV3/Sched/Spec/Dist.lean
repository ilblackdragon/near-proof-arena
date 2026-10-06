import ZkFormal.NearV3.Sched.Spec.DistDefs

/-!
# ZkFormal.NearV3.Sched.Spec.Dist — `distribute` is the grid

Proofs about the definitions of `Sched/Spec/DistDefs.lean`:

* `distReceivers_eq_gridRow` — the inner receiver loop of `distribute` never `break`s while the
  sender's `links_num` counts its allowed links still to visit and every allowed receiver still
  has `links_num ≥ 1`; `distFold_eq_gridFold` carries this invariant across the senders;
* `sortByKey_perm` (and `sortByKey_nodup`, `mem_sortByKey`, `length_sortByKey`) — the stable
  sort permutes its input;
* `distribute_eq_grid` — `distribute` = `applyGrants` of the grid grants;
* `sortByKey_eq_of_sorted` — for `n ≤ 64`, `sortByKey key (range n)` is the unique permutation
  of `[0, n)` with strictly increasing `sortKey (key x) x`;
* `applyGrants_granted`, `applyGrants_fields`, `applyGrants_size` — the effect of `applyGrants`;
* `gridGrants_get` — the grid grants cell by cell, through the per-cell recurrences `SE i j`
  (sender endpoint of `sord[i]` before receiver position `j`) and `RE i j` (receiver endpoint of
  `rord[j]` before sender position `i`), as the AIR checks them row by row.
-/

namespace ZkFormal.NearV3.Sched

open NearSpecV3 NearSpecV3.Scheduler

/-! ## Array helpers -/

theorem getElem!_set!_ne {α : Type} [Inhabited α] (a : Array α) {i j : Nat} (v : α)
    (h : i ≠ j) : (a.set! i v)[j]! = a[j]! := by
  simp [Array.set!_eq_setIfInBounds, getElem!_def, h]

theorem getElem!_set!_self {α : Type} [Inhabited α] (a : Array α) (i : Nat) (v : α) :
    (a.set! i v)[i]! = if i < a.size then v else a[i]! := by
  by_cases h : i < a.size
  · simp [Array.set!_eq_setIfInBounds, h]
  · simp [Array.set!_eq_setIfInBounds, h]

theorem getElem!_oob {α : Type} [Inhabited α] (a : Array α) {i : Nat} (h : a.size ≤ i) :
    a[i]! = default := by
  simp [getElem!_def, Array.getElem?_eq_none h]

theorem getElem!_toArray_map_range {α : Type} [Inhabited α] (n : Nat) (f : Nat → α) {i : Nat}
    (h : i < n) : (((List.range n).map f).toArray)[i]! = f i := by
  simp [getElem!_def, List.getElem?_toArray, List.getElem?_map, List.getElem?_range h]

/-! ## `sortByKey` permutes its input -/

theorem insertStable_perm (key : Nat → Nat) (x : Nat) (l : List Nat) :
    (insertStable key x l).Perm (x :: l) := by
  induction l with
  | nil => simp [insertStable]
  | cons y ys ih =>
    unfold insertStable
    split
    · exact List.Perm.refl _
    · exact (ih.cons y).trans (List.Perm.swap x y ys)

theorem foldl_insertStable_perm (key : Nat → Nat) (l acc : List Nat) :
    (l.foldl (fun acc x => insertStable key x acc) acc).Perm (l ++ acc) := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    refine (ih _).trans ?_
    exact ((insertStable_perm key x acc).append_left xs).trans List.perm_middle

theorem sortByKey_perm (key : Nat → Nat) (l : List Nat) : (sortByKey key l).Perm l := by
  have := foldl_insertStable_perm key l []
  simpa [sortByKey] using this

theorem mem_sortByKey (key : Nat → Nat) (l : List Nat) (x : Nat) :
    x ∈ sortByKey key l ↔ x ∈ l :=
  (sortByKey_perm key l).mem_iff

theorem length_sortByKey (key : Nat → Nat) (l : List Nat) :
    (sortByKey key l).length = l.length :=
  (sortByKey_perm key l).length_eq

theorem sortByKey_nodup (key : Nat → Nat) (l : List Nat) (h : l.Nodup) :
    (sortByKey key l).Nodup :=
  (sortByKey_perm key l).nodup_iff.2 h

theorem sortByKey_range_nodup (key : Nat → Nat) (n : Nat) :
    (sortByKey key (List.range n)).Nodup :=
  sortByKey_nodup key _ List.nodup_range

theorem mem_sortByKey_range (key : Nat → Nat) (n x : Nat) :
    x ∈ sortByKey key (List.range n) ↔ x < n := by
  rw [mem_sortByKey, List.mem_range]

theorem length_sortByKey_range (key : Nat → Nat) (n : Nat) :
    (sortByKey key (List.range n)).length = n := by
  rw [length_sortByKey, List.length_range]

/-- The sort only looks at the keys of the elements it sorts. -/
theorem insertStable_congr (k1 k2 : Nat → Nat) (x : Nat) (l : List Nat)
    (h : ∀ y ∈ x :: l, k1 y = k2 y) : insertStable k1 x l = insertStable k2 x l := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    simp only [insertStable]
    rw [h x (by simp), h y (by simp), ih (fun z hz => h z (by
      rcases List.mem_cons.1 hz with rfl | hz
      · simp
      · simp [hz]))]

theorem foldl_insertStable_congr (k1 k2 : Nat → Nat) (l : List Nat) :
    ∀ acc : List Nat, (∀ y ∈ acc, k1 y = k2 y) → (∀ y ∈ l, k1 y = k2 y) →
      l.foldl (fun acc x => insertStable k1 x acc) acc =
        l.foldl (fun acc x => insertStable k2 x acc) acc := by
  induction l with
  | nil => intros; rfl
  | cons x xs ih =>
    intro acc hacc hl
    simp only [List.foldl_cons]
    rw [insertStable_congr k1 k2 x acc (fun y hy => by
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hl _ (by simp)
      · exact hacc y hy)]
    apply ih
    · intro y hy
      rcases List.mem_cons.1 ((insertStable_perm k2 x acc).mem_iff.1 hy) with rfl | hy
      · exact hl _ (by simp)
      · exact hacc y hy
    · intro y hy; exact hl y (by simp [hy])

theorem sortByKey_congr (k1 k2 : Nat → Nat) (l : List Nat) (h : ∀ y ∈ l, k1 y = k2 y) :
    sortByKey k1 l = sortByKey k2 l :=
  foldl_insertStable_congr k1 k2 l [] (by simp) h

/-! ## The sorted order is the `sortKey` order -/

/-- Strict `sortKey` order. -/
abbrev KeyLt (key : Nat → Nat) (x y : Nat) : Prop := sortKey (key x) x < sortKey (key y) y

theorem insertStable_sorted (key : Nat → Nat) (x : Nat) (hx : x < 64) (l : List Nat)
    (hl : ∀ y ∈ l, y < x) (hs : l.Pairwise (KeyLt key)) :
    (insertStable key x l).Pairwise (KeyLt key) := by
  induction l with
  | nil => simp [insertStable]
  | cons y ys ih =>
    rw [List.pairwise_cons] at hs
    have hy := hl y (by simp)
    unfold insertStable
    split
    · rename_i hk
      have hxy : KeyLt key x y := by unfold KeyLt sortKey; omega
      refine List.Pairwise.cons ?_ (List.Pairwise.cons hs.1 hs.2)
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hxy
      · exact Nat.lt_trans hxy (hs.1 z hz)
    · rename_i hk
      refine List.Pairwise.cons ?_ (ih (fun z hz => hl z (by simp [hz])) hs.2)
      intro z hz
      rcases List.mem_cons.1 ((insertStable_perm key x ys).mem_iff.1 hz) with rfl | hz
      · unfold KeyLt sortKey; omega
      · exact hs.1 z hz

theorem sortByKey_range_succ (key : Nat → Nat) (n : Nat) :
    sortByKey key (List.range (n + 1)) = insertStable key n (sortByKey key (List.range n)) := by
  simp [sortByKey, List.range_succ, List.foldl_append]

theorem sortByKey_range_sorted (key : Nat → Nat) (n : Nat) (hn : n ≤ 64) :
    (sortByKey key (List.range n)).Pairwise (KeyLt key) := by
  induction n with
  | zero => simp [sortByKey]
  | succ n ih =>
    rw [sortByKey_range_succ]
    exact insertStable_sorted key n (by omega) _
      (fun y hy => (mem_sortByKey_range key n y).1 hy) (ih (by omega))

/-- Two lists strictly increasing under `f` with the same members are equal. -/
theorem eq_of_pairwise_lt_of_mem_iff (f : Nat → Nat) :
    ∀ (l1 l2 : List Nat), l1.Pairwise (fun a b => f a < f b) →
      l2.Pairwise (fun a b => f a < f b) → (∀ x, x ∈ l1 ↔ x ∈ l2) → l1 = l2
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 (by simp)) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).1 (by simp)) (by simp)
  | a :: t1, b :: t2, h1, h2, h => by
    rw [List.pairwise_cons] at h1 h2
    have hab : a = b := by
      apply Classical.byContradiction
      intro hne
      have ha : a ∈ t2 := (List.mem_cons.1 ((h a).1 (by simp))).resolve_left hne
      have hb : b ∈ t1 :=
        (List.mem_cons.1 ((h b).2 (by simp))).resolve_left (fun e => hne e.symm)
      have := h1.1 b hb
      have := h2.1 a ha
      omega
    subst hab
    rw [eq_of_pairwise_lt_of_mem_iff f t1 t2 h1.2 h2.2 (fun x => by
      constructor
      · intro hx
        have hne : x ≠ a := fun e => by have := h1.1 x hx; subst e; omega
        exact (List.mem_cons.1 ((h x).1 (by simp [hx]))).resolve_left hne
      · intro hx
        have hne : x ≠ a := fun e => by have := h2.1 x hx; subst e; omega
        exact (List.mem_cons.1 ((h x).2 (by simp [hx]))).resolve_left hne)]

/-- Pigeonhole: a duplicate-free list inside `m` is no longer than `m`. -/
theorem length_le_of_nodup_subset :
    ∀ (l m : List Nat), l.Nodup → (∀ x ∈ l, x ∈ m) → l.length ≤ m.length
  | [], _, _, _ => by simp
  | a :: t, m, hnd, hs => by
    rw [List.nodup_cons] at hnd
    have ham : a ∈ m := hs a (by simp)
    have ht := length_le_of_nodup_subset t (m.erase a) hnd.2 (fun x hx => by
      have hxa : x ≠ a := fun e => hnd.1 (e ▸ hx)
      exact (List.mem_erase_of_ne hxa).2 (hs x (by simp [hx])))
    rw [List.length_erase_of_mem ham] at ht
    have := List.length_pos_of_mem ham
    simp only [List.length_cons]
    omega

/-- A duplicate-free list of length `n` with entries `< n` contains every `x < n`. -/
theorem mem_of_nodup_of_length (n : Nat) (l : List Nat) (hnd : l.Nodup)
    (hlt : ∀ x ∈ l, x < n) (hlen : l.length = n) (x : Nat) : x ∈ l ↔ x < n := by
  refine ⟨hlt x, fun hx => Classical.byContradiction fun hnx => ?_⟩
  have := length_le_of_nodup_subset l ((List.range n).erase x) hnd (fun y hy => by
    have hyx : y ≠ x := fun e => hnx (e ▸ hy)
    exact (List.mem_erase_of_ne hyx).2 (List.mem_range.2 (hlt y hy)))
  rw [List.length_erase_of_mem (List.mem_range.2 hx), List.length_range] at this
  omega

/-- **(3)** For `n ≤ 64` the stable sort of `[0, n)` by `key` is the unique permutation of
`[0, n)` along which `sortKey (key x) x` strictly increases. -/
theorem sortByKey_eq_of_sorted (key : Nat → Nat) (n : Nat) (hn : n ≤ 64) (l : List Nat)
    (hnd : l.Nodup) (hlt : ∀ x ∈ l, x < n) (hlen : l.length = n)
    (hs : List.Pairwise (fun x y => sortKey (key x) x < sortKey (key y) y) l) :
    sortByKey key (List.range n) = l :=
  eq_of_pairwise_lt_of_mem_iff (fun x => sortKey (key x) x) _ _
    (sortByKey_range_sorted key n hn) hs (fun x => by
      rw [mem_sortByKey_range, mem_of_nodup_of_length n l hnd hlt hlen])

/-! ## The `break` never fires -/

/-- **(1)** Inner loop of one sender: while the sender's `links_num` is its number of allowed
links to the receivers still to visit, and every such receiver still has `links_num ≥ 1`, the
`break` of `distReceivers` never fires. -/
theorem distReceivers_eq_gridRow (n : Nat) (allowed : Array Bool) (s : Nat) :
    ∀ (rs : List Nat) (se : Endpoint) (ri : Array Endpoint) (g : Array (Option Nat)),
      rs.Nodup → se.1 = (rs.filter fun r => allowed[s * n + r]!).length →
      (∀ r ∈ rs, allowed[s * n + r]! = true → 1 ≤ (ri[r]!).1) →
      distReceivers n allowed s rs se ri g = gridRow n allowed s rs se ri g
  | [], se, ri, g, _, _, _ => by simp [distReceivers, gridRow]
  | r :: rs, se, ri, g, hnd, hse, hri => by
    rw [List.nodup_cons] at hnd
    by_cases ha : allowed[s * n + r]! = true
    · have h1 : 1 ≤ (ri[r]!).1 := hri r (by simp) ha
      have h2 : se.1 = (rs.filter fun r => allowed[s * n + r]!).length + 1 := by
        simpa [List.filter_cons, ha] using hse
      simp only [distReceivers, gridRow, ha, Bool.not_true, Bool.false_eq_true, ite_false]
      have hc : ¬(se.1 = 0 ∨ (ri[r]!).1 = 0) := by omega
      simp only [hc, ite_false]
      apply distReceivers_eq_gridRow n allowed s rs _ _ _ hnd.2
      · simp only; omega
      · intro r' hr' ha'
        rw [getElem!_set!_ne _ _ (fun e => by subst e; exact hnd.1 hr')]
        exact hri r' (by simp [hr']) ha'
    · have ha' : allowed[s * n + r]! = false := by simpa using ha
      simp only [distReceivers, gridRow, ha', Bool.not_false, ite_true]
      apply distReceivers_eq_gridRow n allowed s rs _ _ _ hnd.2
      · simpa [List.filter_cons, ha'] using hse
      · intro r' hr' ha''; exact hri r' (by simp [hr']) ha''

/-- One grid row decrements `links_num` of every visited allowed receiver once. -/
theorem gridRow_ri_fst (n : Nat) (allowed : Array Bool) (s : Nat) :
    ∀ (rs : List Nat) (se : Endpoint) (ri : Array Endpoint) (g : Array (Option Nat)),
      rs.Nodup → ∀ r,
      ((gridRow n allowed s rs se ri g).2.1[r]!).1 =
        (ri[r]!).1 - (if r ∈ rs ∧ allowed[s * n + r]! = true then 1 else 0)
  | [], se, ri, g, _, r => by simp [gridRow]
  | r' :: rs, se, ri, g, hnd, r => by
    rw [List.nodup_cons] at hnd
    by_cases ha : allowed[s * n + r']! = true
    · simp only [gridRow, ha, Bool.not_true, Bool.false_eq_true, ite_false]
      rw [gridRow_ri_fst n allowed s rs _ _ _ hnd.2 r]
      by_cases hr : r = r'
      · subst hr
        rw [getElem!_set!_self]
        split
        · simp [ha, hnd.1]
        · rename_i hsz
          rw [getElem!_oob ri (Nat.le_of_not_lt hsz)]
          simp [ha, hnd.1]
          rfl
      · rw [getElem!_set!_ne _ _ (fun e => hr e.symm)]
        simp [hr]
    · have ha' : allowed[s * n + r']! = false := by simpa using ha
      simp only [gridRow, ha', Bool.not_false, ite_true]
      rw [gridRow_ri_fst n allowed s rs _ _ _ hnd.2 r]
      by_cases hr : r = r'
      · subst hr; simp [ha', hnd.1]
      · simp [hr]

/-- **(1)** Across senders: processing the senders of `L` (no repeats, all `< n`) in order, with
`ri[r]!.1` = number of allowed links `(s', r)` with `s'` still in `L`, and each sender's
initial endpoint counting its allowed links, `distribute`'s fold computes the grid's grants. -/
theorem distFold_eq_gridFold (n : Nat) (allowed : Array Bool) (rord : List Nat)
    (si0 : Array Endpoint) (hrnd : rord.Nodup) (hrmem : ∀ r, r ∈ rord ↔ r < n)
    (hsi0 : ∀ s < n, (si0[s]!).1 = (rord.filter fun r => allowed[s * n + r]!).length) :
    ∀ (L : List Nat) (si ri : Array Endpoint) (g : Array (Option Nat)),
      L.Nodup → (∀ s ∈ L, s < n) → (∀ s ∈ L, si[s]! = si0[s]!) →
      (∀ r < n, (ri[r]!).1 = (L.filter fun s => allowed[s * n + r]!).length) →
      (L.foldl (fun (x : Array Endpoint × Array Endpoint × Array (Option Nat)) s =>
          (x.1.set! s (distReceivers n allowed s rord x.1[s]! x.2.1 x.2.2).1,
           (distReceivers n allowed s rord x.1[s]! x.2.1 x.2.2).2.1,
           (distReceivers n allowed s rord x.1[s]! x.2.1 x.2.2).2.2)) (si, ri, g)).2.2 =
      (L.foldl (fun (acc : Array Endpoint × Array (Option Nat)) s =>
          ((gridRow n allowed s rord si0[s]! acc.1 acc.2).2.1,
           (gridRow n allowed s rord si0[s]! acc.1 acc.2).2.2)) (ri, g)).2
  | [], _, _, _, _, _, _, _ => rfl
  | s :: L, si, ri, g, hnd, hlt, hsi, hri => by
    rw [List.nodup_cons] at hnd
    simp only [List.foldl_cons]
    have hs : s < n := hlt s (by simp)
    have hd : distReceivers n allowed s rord si[s]! ri g =
        gridRow n allowed s rord si0[s]! ri g := by
      rw [hsi s (by simp)]
      apply distReceivers_eq_gridRow _ _ _ _ _ _ _ hrnd (hsi0 s hs)
      intro r hr ha
      rw [hri r ((hrmem r).1 hr)]
      simp [ha]
    rw [hd]
    apply distFold_eq_gridFold n allowed rord si0 hrnd hrmem hsi0 L
    · exact hnd.2
    · exact fun s' h => hlt s' (by simp [h])
    · intro s' hs'
      rw [getElem!_set!_ne _ _ (fun e => by subst e; exact hnd.1 hs')]
      exact hsi s' (by simp [hs'])
    · intro r hr
      rw [gridRow_ri_fst _ _ _ _ _ _ _ hrnd r, hri r hr]
      cases h : allowed[s * n + r]! <;> simp [h, (hrmem r).2 hr]

/-! ## `distribute` is the grid -/

theorem filter_length_perm (p : Nat → Bool) {l1 l2 : List Nat} (h : l1.Perm l2) :
    (l1.filter p).length = (l2.filter p).length :=
  (h.filter p).length_eq

/-- **(2)** `distribute` applies the grid's grants (senders in `sordOf`, receivers in
`rordOf`). -/
theorem distribute_eq_grid (n : Nat) (allowed : Array Bool) (st : St)
    (_hsb : st.senderBudget.size = n) (_hrb : st.receiverBudget.size = n)
    (_hal : allowed.size = n * n) :
    distribute n allowed st =
      applyGrants n st (gridGrants n allowed st.senderBudget st.receiverBudget
        (sordOf n allowed st.senderBudget) (rordOf n allowed st.receiverBudget)) := by
  simp only [distribute]
  show applyGrants n st _ = applyGrants n st _
  congr 1
  simp only [gridGrants]
  have hsi : ((List.range n).map fun s =>
      ((List.filter (fun j => allowed[s * n + j]!) (List.range n)).length,
        st.senderBudget[s]!)).toArray =
      ((List.range n).map fun s => (cntS n allowed s, st.senderBudget[s]!)).toArray := rfl
  have hri : ((List.range n).map fun r =>
      ((List.filter (fun j => allowed[j * n + r]!) (List.range n)).length,
        st.receiverBudget[r]!)).toArray =
      ((List.range n).map fun r => (cntR n allowed r, st.receiverBudget[r]!)).toArray := rfl
  rw [hsi, hri]
  have hsord : sortByKey (fun s => avgLink
      ((List.range n).map fun s => (cntS n allowed s, st.senderBudget[s]!)).toArray[s]!)
      (List.range n) = sordOf n allowed st.senderBudget :=
    sortByKey_congr _ _ _ (fun s hs => by
      rw [getElem!_toArray_map_range _ _ (List.mem_range.1 hs)])
  have hrord : sortByKey (fun r => avgLink
      ((List.range n).map fun r => (cntR n allowed r, st.receiverBudget[r]!)).toArray[r]!)
      (List.range n) = rordOf n allowed st.receiverBudget :=
    sortByKey_congr _ _ _ (fun r hr => by
      rw [getElem!_toArray_map_range _ _ (List.mem_range.1 hr)])
  rw [hsord, hrord]
  have hrperm := sortByKey_perm (fun r => avgLink (cntR n allowed r, st.receiverBudget[r]!))
    (List.range n)
  have hsperm := sortByKey_perm (fun s => avgLink (cntS n allowed s, st.senderBudget[s]!))
    (List.range n)
  apply distFold_eq_gridFold
  · exact sortByKey_range_nodup _ n
  · exact mem_sortByKey_range _ n
  · intro s hs
    rw [getElem!_toArray_map_range _ _ hs]
    exact filter_length_perm _ hrperm.symm
  · exact sortByKey_range_nodup _ n
  · exact fun s hs => (mem_sortByKey_range _ n s).1 hs
  · intro _ _; rfl
  · intro r hr
    rw [getElem!_toArray_map_range _ _ hr]
    exact filter_length_perm _ hsperm.symm

/-! ## `applyGrants` -/

/-- The granted value of a link after adding the grid grant `o` (`grantMore`'s checked add). -/
def addGrant (o : Option Nat) (old : Nat) : Nat :=
  match o with
  | some b => if old + b ≤ u64Max then old + b else u64Max
  | none => old

/-- One step of `applyGrants`. -/
theorem applyGrants_step (st : St) (g : Array (Option Nat)) (k : Nat)
    (hk : k < st.granted.size) :
    let st' := (match g[k]! with | some b => grantMore st k b | none => st)
    st'.senderBudget = st.senderBudget ∧ st'.receiverBudget = st.receiverBudget ∧
      st'.allowance = st.allowance ∧ st'.rng = st.rng ∧
      st'.granted.size = st.granted.size ∧
      ∀ l, st'.granted[l]! = if l = k then addGrant g[k]! st.granted[k]! else st.granted[l]! := by
  intro st'
  cases h : g[k]! with
  | none =>
    refine ⟨?_, ?_, ?_, ?_, ?_, fun l => ?_⟩ <;> simp only [st', h, addGrant]
    by_cases hl : l = k
    · subst hl; simp
    · simp [hl]
  | some b =>
    refine ⟨?_, ?_, ?_, ?_, ?_, fun l => ?_⟩ <;> simp only [st', h, addGrant, grantMore]
    · simp [Array.set!_eq_setIfInBounds]
    by_cases hl : l = k
    · subst hl; rw [getElem!_set!_self]; simp [hk]
    · rw [getElem!_set!_ne _ _ (fun e => hl e.symm)]; simp [hl]

theorem applyGrants_fold (st : St) (g : Array (Option Nat)) :
    ∀ k, k ≤ st.granted.size →
      let st' := (List.range k).foldl (fun st l =>
        match g[l]! with
        | some b => grantMore st l b
        | none => st) st
      st'.senderBudget = st.senderBudget ∧ st'.receiverBudget = st.receiverBudget ∧
        st'.allowance = st.allowance ∧ st'.rng = st.rng ∧
        st'.granted.size = st.granted.size ∧
        ∀ l, st'.granted[l]! = if l < k then addGrant g[l]! st.granted[l]! else st.granted[l]!
  | 0, _ => by simp
  | k + 1, hk => by
    intro st'
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := applyGrants_fold st g k (by omega)
    have hs : st' = (match g[k]! with
        | some b => grantMore ((List.range k).foldl (fun st l =>
            match g[l]! with
            | some b => grantMore st l b
            | none => st) st) k b
        | none => ((List.range k).foldl (fun st l =>
            match g[l]! with
            | some b => grantMore st l b
            | none => st) st)) := by
      simp only [st', List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := applyGrants_step ((List.range k).foldl (fun st l =>
        match g[l]! with
        | some b => grantMore st l b
        | none => st) st) g k (by omega)
    rw [hs]
    refine ⟨e1.trans h1, e2.trans h2, e3.trans h3, e4.trans h4, e5.trans h5, fun l => ?_⟩
    rw [e6 l]
    by_cases hl : l = k
    · subst hl; rw [h6 l]; simp
    · rw [h6 l]
      by_cases hlk : l < k
      · simp [hl, hlk, show l < k + 1 by omega]
      · simp [hl, hlk, show ¬ l < k + 1 by omega]

/-- **(4)** `applyGrants` adds each grid grant to its link (checked add, `u64::MAX` on
overflow) and leaves every other field unchanged. -/
theorem applyGrants_granted (n : Nat) (st : St) (g : Array (Option Nat)) (l : Nat)
    (hl : l < n * n) (hst : st.granted.size = n * n) (_hg : g.size = n * n) :
    (applyGrants n st g).granted[l]! =
      match g[l]! with
      | some b => (if st.granted[l]! + b ≤ u64Max then st.granted[l]! + b else u64Max)
      | none => st.granted[l]! := by
  have := (applyGrants_fold st g (n * n) (by omega)).2.2.2.2.2 l
  simp only [hl, ite_true] at this
  unfold applyGrants
  refine Eq.trans this ?_
  cases g[l]! <;> rfl

theorem applyGrants_fields (n : Nat) (st : St) (g : Array (Option Nat))
    (hst : st.granted.size = n * n) :
    (applyGrants n st g).senderBudget = st.senderBudget ∧
      (applyGrants n st g).receiverBudget = st.receiverBudget ∧
      (applyGrants n st g).allowance = st.allowance ∧
      (applyGrants n st g).rng = st.rng := by
  obtain ⟨h1, h2, h3, h4, _⟩ := applyGrants_fold st g (n * n) (by omega)
  exact ⟨h1, h2, h3, h4⟩

theorem applyGrants_allowance (n : Nat) (st : St) (g : Array (Option Nat))
    (hst : st.granted.size = n * n) : (applyGrants n st g).allowance = st.allowance :=
  (applyGrants_fields n st g hst).2.2.1

theorem applyGrants_size (n : Nat) (st : St) (g : Array (Option Nat))
    (hst : st.granted.size = n * n) : (applyGrants n st g).granted.size = n * n := by
  rw [← hst]
  exact (applyGrants_fold st g (n * n) (by omega)).2.2.2.2.1

/-! ## The grid, cell by cell -/

/-- Sender endpoints along row `i` (sender `sord[i]`), given the receiver endpoints `re j` of
the cells of that row: `SErow … i re j` is the endpoint before receiver position `j`. -/
def SErow (n : Nat) (allowed : Array Bool) (sb : Array Nat) (sord rord : List Nat) (i : Nat)
    (re : Nat → Endpoint) : Nat → Endpoint
  | 0 => (cntS n allowed sord[i]!, sb[sord[i]!]!)
  | j + 1 =>
    let se := SErow n allowed sb sord rord i re j
    let rr := re j
    if allowed[sord[i]! * n + rord[j]!]! then
      (se.1 - 1, se.2 - Nat.min (se.2 / se.1) (rr.2 / rr.1))
    else se

/-- `RE … i j`: the receiver endpoint of `rord[j]` before sender position `i`. -/
def RE (n : Nat) (allowed : Array Bool) (sb rb : Array Nat) (sord rord : List Nat) :
    Nat → Nat → Endpoint
  | 0, j => (cntR n allowed rord[j]!, rb[rord[j]!]!)
  | i + 1, j =>
    let re := RE n allowed sb rb sord rord i j
    let se := SErow n allowed sb sord rord i (RE n allowed sb rb sord rord i) j
    if allowed[sord[i]! * n + rord[j]!]! then
      (re.1 - 1, re.2 - Nat.min (se.2 / se.1) (re.2 / re.1))
    else re

/-- `SE … i j`: the sender endpoint of `sord[i]` before receiver position `j`. -/
def SE (n : Nat) (allowed : Array Bool) (sb rb : Array Nat) (sord rord : List Nat)
    (i j : Nat) : Endpoint :=
  SErow n allowed sb sord rord i (RE n allowed sb rb sord rord i) j

/-- The grant of cell `(i, j)`. -/
def cellG (n : Nat) (allowed : Array Bool) (sb rb : Array Nat) (sord rord : List Nat)
    (i j : Nat) : Option Nat :=
  if allowed[sord[i]! * n + rord[j]!]! then
    some (Nat.min ((SE n allowed sb rb sord rord i j).2 / (SE n allowed sb rb sord rord i j).1)
      ((RE n allowed sb rb sord rord i j).2 / (RE n allowed sb rb sord rord i j).1))
  else none

theorem SE_succ (n : Nat) (allowed : Array Bool) (sb rb : Array Nat) (sord rord : List Nat)
    (i j : Nat) :
    SE n allowed sb rb sord rord i (j + 1) =
      if allowed[sord[i]! * n + rord[j]!]! then
        ((SE n allowed sb rb sord rord i j).1 - 1, (SE n allowed sb rb sord rord i j).2 -
          Nat.min ((SE n allowed sb rb sord rord i j).2 / (SE n allowed sb rb sord rord i j).1)
            ((RE n allowed sb rb sord rord i j).2 / (RE n allowed sb rb sord rord i j).1))
      else SE n allowed sb rb sord rord i j := rfl

theorem RE_succ (n : Nat) (allowed : Array Bool) (sb rb : Array Nat) (sord rord : List Nat)
    (i j : Nat) :
    RE n allowed sb rb sord rord (i + 1) j =
      if allowed[sord[i]! * n + rord[j]!]! then
        ((RE n allowed sb rb sord rord i j).1 - 1, (RE n allowed sb rb sord rord i j).2 -
          Nat.min ((SE n allowed sb rb sord rord i j).2 / (SE n allowed sb rb sord rord i j).1)
            ((RE n allowed sb rb sord rord i j).2 / (RE n allowed sb rb sord rord i j).1))
      else RE n allowed sb rb sord rord i j := rfl

theorem link_lt {n s r : Nat} (hs : s < n) (hr : r < n) : s * n + r < n * n := by
  have : (s + 1) * n ≤ n * n := Nat.mul_le_mul_right n hs
  rw [Nat.succ_mul] at this
  omega

theorem link_inj {n s r s' r' : Nat} (hr : r < n) (hr' : r' < n) (h : s * n + r = s' * n + r') :
    s = s' ∧ r = r' := by
  have hn : 0 < n := by omega
  have hd : ∀ a b, b < n → (a * n + b) / n = a := fun a b hb => by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hb, Nat.zero_add]
  have hm : ∀ a b, b < n → (a * n + b) % n = b := fun a b hb => by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  exact ⟨by rw [← hd s r hr, h, hd s' r' hr'], by rw [← hm s r hr, h, hm s' r' hr']⟩

theorem getElem!_lt_of_mem (l : List Nat) (n i : Nat) (hlt : ∀ x ∈ l, x < n)
    (hi : i < l.length) : l[i]! < n := by
  rw [getElem!_pos l i hi]
  exact hlt _ (List.getElem_mem hi)

section Grid

variable (n : Nat) (allowed : Array Bool) (sb rb : Array Nat) (sord rord : List Nat)
  (hsnd : sord.Nodup) (hslen : sord.length = n) (hslt : ∀ x ∈ sord, x < n)
  (hrnd : rord.Nodup) (hrlen : rord.length = n) (hrlt : ∀ x ∈ rord, x < n)

include hsnd hslen hslt hrnd hrlen hrlt in
/-- Row `i` of the grid: from receiver position `j` on. -/
theorem gridRow_inv (i : Nat) (hi : i < n) :
    ∀ (m j : Nat) (se : Endpoint) (ri : Array Endpoint) (g : Array (Option Nat)),
      j + m = n → se = SE n allowed sb rb sord rord i j → ri.size = n → g.size = n * n →
      (∀ j' < n, ri[rord[j']!]! = if j' < j then RE n allowed sb rb sord rord (i + 1) j'
        else RE n allowed sb rb sord rord i j') →
      (∀ i' < n, ∀ j' < n, g[sord[i']! * n + rord[j']!]! =
        if i' < i ∨ (i' = i ∧ j' < j) then cellG n allowed sb rb sord rord i' j' else none) →
      (gridRow n allowed sord[i]! (rord.drop j) se ri g).2.1.size = n ∧
      (gridRow n allowed sord[i]! (rord.drop j) se ri g).2.2.size = n * n ∧
      (∀ j' < n, (gridRow n allowed sord[i]! (rord.drop j) se ri g).2.1[rord[j']!]! =
        RE n allowed sb rb sord rord (i + 1) j') ∧
      (∀ i' < n, ∀ j' < n,
        (gridRow n allowed sord[i]! (rord.drop j) se ri g).2.2[sord[i']! * n + rord[j']!]! =
        if i' < i + 1 then cellG n allowed sb rb sord rord i' j' else none)
  | 0, j, se, ri, g, hjm, _, hri, hg, hrv, hgv => by
    have hj : j = n := by omega
    subst hj
    rw [List.drop_eq_nil_of_le (by omega)]
    simp only [gridRow]
    refine ⟨hri, hg, fun j' hj' => by rw [hrv j' hj', ite_eq_left hj'], fun i' hi' j' hj' => ?_⟩
    rw [hgv i' hi' j' hj']
    by_cases h : i' < i + 1
    · simp [h, hj', show i' < i ∨ i' = i by omega]
    · simp [h, show ¬ i' < i by omega, show i' ≠ i by omega]
  | m + 1, j, se, ri, g, hjm, hse, hri, hg, hrv, hgv => by
    have hj : j < rord.length := by omega
    rw [List.drop_eq_getElem_cons hj, ← getElem!_pos rord j hj]
    have hs : sord[i]! < n := getElem!_lt_of_mem sord n i hslt (by omega)
    have hr : rord[j]! < n := getElem!_lt_of_mem rord n j hrlt hj
    have hre : ri[rord[j]!]! = RE n allowed sb rb sord rord i j := by
      rw [hrv j (by omega), ite_eq_right (Nat.lt_irrefl j)]
    have hrne : ∀ j' < n, j' ≠ j → rord[j']! ≠ rord[j]! := fun j' hj' hne e =>
      hne ((List.Nodup.getElem!_inj (by omega) hj hrnd).1 e)
    have hlne : ∀ i' < n, ∀ j' < n, ¬ (i' = i ∧ j' = j) →
        sord[i']! * n + rord[j']! ≠ sord[i]! * n + rord[j]! := fun i' hi' j' hj' hne e => by
      obtain ⟨e1, e2⟩ := link_inj (getElem!_lt_of_mem rord n j' hrlt (by omega)) hr e
      exact hne ⟨(List.Nodup.getElem!_inj (by omega) (by omega) hsnd).1 e1,
        (List.Nodup.getElem!_inj (by omega) hj hrnd).1 e2⟩
    by_cases ha : allowed[sord[i]! * n + rord[j]!]! = true
    · simp only [gridRow, ha, Bool.not_true, Bool.false_eq_true, ite_false]
      apply gridRow_inv i hi m (j + 1) _ _ _ (by omega)
      · rw [SE_succ, ite_eq_left ha, hse, hre]
      · rw [Array.size_set!, hri]
      · rw [Array.size_set!, hg]
      · intro j' hj'
        by_cases hjj : j' = j
        · subst hjj
          rw [getElem!_set!_self, ite_eq_left (by omega), ite_eq_left (by omega), RE_succ, ite_eq_left ha,
            hre, hse]
        · rw [getElem!_set!_ne _ _ (fun e => hrne j' hj' hjj e.symm), hrv j' hj']
          by_cases hlt : j' < j
          · rw [ite_eq_left hlt, ite_eq_left (by omega)]
          · rw [ite_eq_right hlt, ite_eq_right (by omega)]
      · intro i' hi' j' hj'
        by_cases hc : i' = i ∧ j' = j
        · obtain ⟨rfl, rfl⟩ := hc
          rw [getElem!_set!_self, ite_eq_left (by rw [hg]; exact link_lt hs hr),
            ite_eq_left (Or.inr ⟨rfl, by omega⟩), cellG, ite_eq_left ha, hse, hre]
        · rw [getElem!_set!_ne _ _ (fun e => hlne i' hi' j' hj' hc e.symm), hgv i' hi' j' hj']
          have : (i' < i ∨ (i' = i ∧ j' < j)) ↔ (i' < i ∨ (i' = i ∧ j' < j + 1)) := by omega
          by_cases hh : i' < i ∨ (i' = i ∧ j' < j)
          · rw [ite_eq_left hh, ite_eq_left (this.1 hh)]
          · rw [ite_eq_right hh, ite_eq_right (fun h => hh (this.2 h))]
    · have ha' : allowed[sord[i]! * n + rord[j]!]! = false := by simpa using ha
      simp only [gridRow, ha', Bool.not_false, ite_true]
      apply gridRow_inv i hi m (j + 1) _ _ _ (by omega)
      · rw [SE_succ, ite_eq_right ha, hse]
      · exact hri
      · exact hg
      · intro j' hj'
        rw [hrv j' hj']
        by_cases hjj : j' = j
        · subst hjj
          rw [ite_eq_right (Nat.lt_irrefl _), ite_eq_left (by omega), RE_succ, ite_eq_right ha]
        · by_cases hlt : j' < j
          · rw [ite_eq_left hlt, ite_eq_left (by omega)]
          · rw [ite_eq_right hlt, ite_eq_right (by omega)]
      · intro i' hi' j' hj'
        rw [hgv i' hi' j' hj']
        by_cases hc : i' = i ∧ j' = j
        · obtain ⟨rfl, rfl⟩ := hc
          rw [ite_eq_right (by omega), ite_eq_left (Or.inr ⟨rfl, by omega⟩), cellG, ite_eq_right ha]
        · have : (i' < i ∨ (i' = i ∧ j' < j)) ↔ (i' < i ∨ (i' = i ∧ j' < j + 1)) := by omega
          by_cases hh : i' < i ∨ (i' = i ∧ j' < j)
          · rw [ite_eq_left hh, ite_eq_left (this.1 hh)]
          · rw [ite_eq_right hh, ite_eq_right (fun h => hh (this.2 h))]

include hsnd hslen hslt hrnd hrlen hrlt in
/-- The rows of the grid: from sender position `i` on. -/
theorem gridFold_inv (si0 : Array Endpoint)
    (hsi0 : ∀ i < n, si0[sord[i]!]! = SE n allowed sb rb sord rord i 0) :
    ∀ (m i : Nat) (ri : Array Endpoint) (g : Array (Option Nat)),
      i + m = n → ri.size = n → g.size = n * n →
      (∀ j' < n, ri[rord[j']!]! = RE n allowed sb rb sord rord i j') →
      (∀ i' < n, ∀ j' < n, g[sord[i']! * n + rord[j']!]! =
        if i' < i then cellG n allowed sb rb sord rord i' j' else none) →
      ∀ i' < n, ∀ j' < n,
        ((sord.drop i).foldl (fun (acc : Array Endpoint × Array (Option Nat)) s =>
          ((gridRow n allowed s rord si0[s]! acc.1 acc.2).2.1,
           (gridRow n allowed s rord si0[s]! acc.1 acc.2).2.2)) (ri, g)).2[sord[i']! * n +
            rord[j']!]! = cellG n allowed sb rb sord rord i' j'
  | 0, i, ri, g, him, _, _, _, hgv => by
    have hi : i = n := by omega
    subst hi
    rw [List.drop_eq_nil_of_le (by omega)]
    intro i' hi' j' hj'
    rw [List.foldl_nil, hgv i' hi' j' hj', ite_eq_left hi']
  | m + 1, i, ri, g, him, hri, hg, hrv, hgv => by
    have hi : i < sord.length := by omega
    rw [List.drop_eq_getElem_cons hi, ← getElem!_pos sord i hi]
    simp only [List.foldl_cons]
    rw [hsi0 i (by omega)]
    have hrow := gridRow_inv n allowed sb rb sord rord hsnd hslen hslt hrnd hrlen hrlt i (by omega)
      n 0 (SE n allowed sb rb sord rord i 0) ri g (by omega) rfl hri hg
      (fun j' hj' => by rw [hrv j' hj', ite_eq_right (Nat.not_lt_zero _)])
      (fun i' hi' j' hj' => by
        rw [hgv i' hi' j' hj']
        by_cases h : i' < i
        · rw [ite_eq_left h, ite_eq_left (Or.inl h)]
        · rw [ite_eq_right h, ite_eq_right (by omega)])
    rw [List.drop_zero] at hrow
    obtain ⟨h1, h2, h3, h4⟩ := hrow
    exact gridFold_inv si0 hsi0 m (i + 1) _ _ (by omega) h1 h2 h3 h4

end Grid

/-- **(5)** The grid grants cell by cell: the grant of link `(sord[i], rord[j])` is
`min(SE.left / SE.links, RE.left / RE.links)` on an allowed cell and nothing otherwise, with
`SE`/`RE` the per-cell recurrences. `sord`, `rord` are permutations of `[0, n)` (as
`sordOf`/`rordOf` are, by `sortByKey_range_nodup`, `mem_sortByKey_range`,
`length_sortByKey_range`). -/
theorem gridGrants_get (n : Nat) (allowed : Array Bool) (sb rb : Array Nat)
    (sord rord : List Nat)
    (hsnd : sord.Nodup) (hslen : sord.length = n) (hslt : ∀ x ∈ sord, x < n)
    (hrnd : rord.Nodup) (hrlen : rord.length = n) (hrlt : ∀ x ∈ rord, x < n)
    (i j : Nat) (hi : i < n) (hj : j < n) :
    (gridGrants n allowed sb rb sord rord)[sord[i]! * n + rord[j]!]! =
      if allowed[sord[i]! * n + rord[j]!]! then
        some (min ((SE n allowed sb rb sord rord i j).2 / (SE n allowed sb rb sord rord i j).1)
          ((RE n allowed sb rb sord rord i j).2 / (RE n allowed sb rb sord rord i j).1))
      else none := by
  have hf := gridFold_inv n allowed sb rb sord rord hsnd hslen hslt hrnd hrlen hrlt
    (((List.range n).map fun s => (cntS n allowed s, sb[s]!)).toArray)
    (fun i hi => getElem!_toArray_map_range _ _
      (getElem!_lt_of_mem sord n i hslt (by omega)))
    n 0 (((List.range n).map fun r => (cntR n allowed r, rb[r]!)).toArray)
    (Array.replicate (n * n) none) (by omega) (by simp) (by simp)
    (fun j' hj' => getElem!_toArray_map_range _ _
      (getElem!_lt_of_mem rord n j' hrlt (by omega)))
    (fun i' _ j' _ => by
      rw [ite_eq_right (Nat.not_lt_zero _), getElem!_def, Array.getElem?_replicate]
      split <;> simp_all <;> rfl)
    i hi j hj
  rw [List.drop_zero] at hf
  exact hf

end ZkFormal.NearV3.Sched
