import ZkFormal.Prover.BcsMulti

/-!
# ZkFormal.Prover.BcsOpen — opening all oracles at the query positions

`ev_openAll`: on the prover's opening stream `openBytes`, the verifier's `openAll`
consumes exactly the stream and, at every query position `x`, `rowsAt` returns the
true openings (`o.map fun M => M.row (x >>> (n0 - M.log))`) of every oracle.
-/

set_option linter.unusedSectionVars false

namespace ZkFormal.Prover

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark

/-! ## `sortDedup` -/

theorem mem_dedupSorted {a : Nat} : ∀ {l : List Nat}, a ∈ sortDedup.dedupSorted l ↔ a ∈ l
  | [] => by simp [sortDedup.dedupSorted]
  | [b] => by simp [sortDedup.dedupSorted]
  | b :: c :: rest => by
    have ih := @mem_dedupSorted a (c :: rest)
    unfold sortDedup.dedupSorted
    split
    · rename_i h; subst h; rw [ih]; simp
    · simp only [List.mem_cons] at ih ⊢; rw [ih]

theorem dedupSorted_sorted : ∀ {l : List Nat}, l.Pairwise (· ≤ ·) →
    (sortDedup.dedupSorted l).Pairwise (· < ·)
  | [], _ => by simp [sortDedup.dedupSorted]
  | [b], _ => by simp [sortDedup.dedupSorted]
  | b :: c :: rest, h => by
    have h' := (List.pairwise_cons.mp h).2
    have ih := dedupSorted_sorted h'
    unfold sortDedup.dedupSorted
    split
    · exact ih
    · rename_i hne
      refine List.Pairwise.cons (fun d hd => ?_) ih
      have hd' := mem_dedupSorted.mp hd
      have hbc := (List.pairwise_cons.mp h).1 c (by simp)
      rcases List.mem_cons.mp hd' with rfl | hd''
      · omega
      · have := (List.pairwise_cons.mp h').1 d hd''; omega

theorem mem_sortDedup {a : Nat} {xs : List Nat} : a ∈ sortDedup xs ↔ a ∈ xs := by
  unfold sortDedup; rw [mem_dedupSorted, List.mem_mergeSort]

theorem sortDedup_sorted (xs : List Nat) : (sortDedup xs).Pairwise (· < ·) := by
  unfold sortDedup
  apply dedupSorted_sorted
  have h := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (fun a b c h1 h2 => by simp at *; omega) (fun a b => by simp; omega) xs
  exact h.imp fun h => by simpa using h

theorem sortDedup_ne_nil {xs : List Nat} (h : xs ≠ []) : sortDedup xs ≠ [] := by
  intro he
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil xs h
  have := mem_sortDedup.mpr ha
  rw [he] at this; cases this

/-! ## Lookup -/

theorem lookup_of_mem {β : Type} {k : Nat × Nat} {v : β} :
    ∀ {l : List ((Nat × Nat) × β)}, (k, v) ∈ l → ∃ v', l.lookup k = some v' ∧ (k, v') ∈ l
  | [], h => by cases h
  | (k', v'') :: l, h => by
    simp only [List.lookup]
    by_cases hk : k = k'
    · subst hk; simp
    · have hb : (k == k') = false := by simpa using hk
      simp only [hb]
      rcases List.mem_cons.mp h with h | h
      · simp at h; exact absurd h.1 hk
      · obtain ⟨w, h1, h2⟩ := lookup_of_mem h
        exact ⟨w, h1, List.mem_cons_of_mem _ h2⟩

section
variable {F K : Type} [Field F] [Field K] [StarkField F K] [StarkFieldLaws F K] [DecidableEq F]

theorem count_logs (m : Nat) : ∀ pre : List (Mat F),
    (pre.map (·.log)).count m = (pre.filter fun M => M.log == m).length
  | [] => rfl
  | M :: pre => by
    simp only [List.map_cons, List.count_cons, List.filter_cons, count_logs m pre]
    split <;> simp_all

theorem rowsAt_go (n0 : Nat) (op : Opened F) (x : Nat) (o : Oracle F)
    (hlook : ∀ M ∈ o, op.lookup (M.log, x >>> (n0 - M.log)) =
      some (levelRows o M.log (x >>> (n0 - M.log)))) :
    ∀ post pre : List (Mat F), o = pre ++ post →
      rowsAt.go n0 op x (shapesOf post) ((pre.map (·.log)).reverse) =
        post.map fun M => M.row (x >>> (n0 - M.log))
  | [], _, _ => rfl
  | M :: post, pre, ho => by
    have hM : M ∈ o := by rw [ho]; simp
    have ih := rowsAt_go n0 op x o hlook post (pre ++ [M]) (by rw [ho]; simp)
    simp only [List.map_append, List.map_cons, List.map_nil, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append] at ih
    simp only [shapesOf, List.map_cons] at ih ⊢
    rw [rowsAt.go]
    simp only [hlook M hM, ih]
    congr 1
    rw [List.count_reverse, count_logs, levelRows, ho, List.filter_append, List.map_append,
      List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
    simp

/-- The rows read at `x` from a correctly opened oracle are the true rows. -/
theorem rowsAt_true (n0 : Nat) (op : Opened F) (x : Nat) (o : Oracle F)
    (hlook : ∀ M ∈ o, op.lookup (M.log, x >>> (n0 - M.log)) =
      some (levelRows o M.log (x >>> (n0 - M.log)))) :
    rowsAt n0 (shapesOf o) op x = o.map fun M => M.row (x >>> (n0 - M.log)) :=
  rowsAt_go n0 op x o hlook o [] rfl

theorem log_le_treeLog {o : Oracle F} {M : Mat F} (hM : M ∈ o) : M.log ≤ treeLog (shapesOf o) := by
  unfold treeLog shapesOf
  induction o with
  | nil => cases hM
  | cons N o ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp hM with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem levelWidths_ne {o : Oracle F} {M : Mat F} (hM : M ∈ o) :
    levelWidths (shapesOf o) M.log ≠ [] := by
  rw [levelWidths_shapesOf]
  simp only [ne_eq, List.map_eq_nil_iff, List.filter_eq_nil_iff, beq_iff_eq, not_forall,
    Classical.not_not]
  exact ⟨M, hM, rfl⟩

variable (H : Bytes → Bytes)

/-- An honest tree: the prover's levels of a well-formed oracle. -/
def TreeOk (n0 : Nat) (t : Oracle F × List (List Bytes)) : Prop :=
  t.2 = ev H (buildTree (K := K) t.1) ∧ RowsOk t.1 ∧ treeLog (shapesOf t.1) ≤ n0

theorem ev_openAll (hH : ∀ m, (fit32 (H m)).length = 32) (n0 : Nat) (xs : List Nat) (hxs : xs ≠ [])
    (hlt : ∀ x ∈ xs, x < 2 ^ n0) :
    ∀ ts : List (Oracle F × List (List Bytes)), (∀ t ∈ ts, TreeOk (K := K) H n0 t) → ∀ rest : Bytes,
    ∃ ops, ev H (openAll (F := F) n0 xs (ts.map fun t => (shapesOf t.1, rootOf t.2))
        (openBytes (K := K) n0 xs ts ++ rest)) = some (ops, rest) ∧
      ∀ x ∈ xs, ((ts.map fun t => shapesOf t.1).zip ops).map (fun (m, op) => rowsAt n0 m op x) =
        ts.map fun t => t.1.map fun M => M.row (x >>> (n0 - M.log))
  | [], _, rest => ⟨[], by simp [openAll, openBytes, ev_pure], fun _ _ => rfl⟩
  | (o, lv) :: ts, hts, rest => by
    obtain ⟨hlv, hr, hn⟩ := hts (o, lv) (by simp)
    simp only at hlv hr hn
    subst hlv
    obtain ⟨ops, hev, hrows⟩ := ev_openAll hH n0 xs hxs hlt ts (fun t ht => hts t (by simp [ht])) rest
    have hS := sortDedup_sorted (xs.map fun x => x >>> (n0 - treeLog (shapesOf o)))
    have hSne : sortDedup (xs.map fun x => x >>> (n0 - treeLog (shapesOf o))) ≠ [] :=
      sortDedup_ne_nil (by simpa using hxs)
    have hSlt : ∀ s ∈ sortDedup (xs.map fun x => x >>> (n0 - treeLog (shapesOf o))),
        s < 2 ^ treeLog (shapesOf o) := by
      intro s hs
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (mem_sortDedup.mp hs)
      rw [Nat.shiftRight_eq_div_pow]
      apply Nat.div_lt_of_lt_mul
      have e : n0 - treeLog (shapesOf o) + treeLog (shapesOf o) = n0 := by omega
      rw [← Nat.pow_add, e]
      exact hlt x hx
    obtain ⟨op, hmp, hgood, hcov⟩ := ev_multiproof (K := K) H o hH hr _ hS hSne hSlt
      (openBytes (K := K) n0 xs ts ++ rest)
    refine ⟨op :: ops, ?_, ?_⟩
    · simp only [List.map_cons, openAll, openBytes, List.append_assoc, ev_bind, hmp, hev, ev_pure]
    · intro x hx
      simp only [List.map_cons, List.zip_cons_cons, hrows x hx]
      congr 1
      apply rowsAt_true
      intro M hM
      have hm := log_le_treeLog hM
      have hs : x >>> (n0 - treeLog (shapesOf o)) ∈
          sortDedup (xs.map fun x => x >>> (n0 - treeLog (shapesOf o))) :=
        mem_sortDedup.mpr (List.mem_map.mpr ⟨x, hx, rfl⟩)
      have hc := hcov M.log hm (levelWidths_ne hM) _ hs
      have e : x >>> (n0 - treeLog (shapesOf o)) >>> (treeLog (shapesOf o) - M.log) =
          x >>> (n0 - M.log) := by
        rw [← Nat.shiftRight_add]; congr 1; omega
      rw [e] at hc
      obtain ⟨v, hv, hmem⟩ := lookup_of_mem hc
      rw [hv]; exact congrArg some (hgood _ hmem)

end

end ZkFormal.Prover
