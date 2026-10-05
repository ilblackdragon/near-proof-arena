import ZkFormal.Bcs.StarkDecode

/-!
# ZkFormal.Bcs.StarkOpen — query answers, `sortDedup`, `openAll`
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace ZkFormal.Bcs.Adapter

open ArenaCore ArenaCore.Security ZkFormal Lean.Grind

theorem queryAnswers_spec (tbl : Table) (wf : TableWF tbl) (d : Bytes) : ∀ (n : Nat) (ys : List Bytes),
    evalT tbl (Stark.queryAnswers d n) = some ys →
      ys.length = n ∧ ∀ j (hj : j < ys.length), tbl.lookup (chunkQ d j) = some ys[j]
  | 0, ys, h => by
    simp [Stark.queryAnswers, evalT] at h; subst h; exact ⟨rfl, fun j hj => by simp at hj⟩
  | n + 1, ys, h => by
    simp only [Stark.queryAnswers, evalT_bind] at h
    cases h1 : evalT tbl (Stark.queryAnswers d n) with
    | none => rw [h1] at h; cases h
    | some ys0 =>
      rw [h1] at h
      simp only [Option.bind_some] at h
      cases h2 : evalT tbl (Stark.H (Stark.tagQuery :: (d ++ Bytes.leN 4 n))) with
      | none => rw [h2] at h; cases h
      | some y =>
        rw [h2] at h
        simp only [Option.bind_some, evalT, Option.some.injEq] at h
        subst h
        obtain ⟨hl, hq⟩ := queryAnswers_spec tbl wf d n ys0 h1
        refine ⟨by simp [hl], fun j hj => ?_⟩
        simp only [List.length_append, List.length_singleton] at hj
        by_cases hjl : j < ys0.length
        · rw [List.getElem_append_left hjl]; exact hq j hjl
        · have : j = ys0.length := by omega
          subst this
          rw [List.getElem_append_right (Nat.le_refl _)]
          simp only [Nat.sub_self, List.getElem_singleton]
          rw [evalT_starkH wf] at h2
          rw [← hl] at h2
          exact h2

theorem dedupSorted_mem : ∀ (l : List Nat) (x : Nat), x ∈ l → x ∈ Stark.sortDedup.dedupSorted l
  | [], x, h => by simp at h
  | [a], x, h => by simpa [Stark.sortDedup.dedupSorted] using h
  | a :: b :: rest, x, h => by
    simp only [Stark.sortDedup.dedupSorted]
    by_cases hab : a = b
    · rw [if_pos hab]
      apply dedupSorted_mem
      rcases List.mem_cons.mp h with rfl | h
      · rw [hab]; exact List.mem_cons_self
      · exact h
    · rw [if_neg hab]
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (dedupSorted_mem _ x h)
termination_by l => l.length

theorem sortDedup_mem {xs : List Nat} {x : Nat} (h : x ∈ xs) : x ∈ Stark.sortDedup xs :=
  dedupSorted_mem _ _ (List.mem_mergeSort.mpr h)

section
variable {F K : Type} [Field F] [Field K] [Stark.StarkField F K] [DecidableEq F]

/-- `openAll` accepted every oracle's multiproof. -/
theorem openAll_spec (tbl : Table) (n0 : Nat) (xs : List Nat) :
    ∀ (L : List (List (Nat × Nat) × Bytes)) (r : Bytes) (ops : List (Stark.Opened F)) (r' : Bytes),
      evalT tbl (Stark.openAll (F := F) n0 xs L r) = some (some (ops, r')) →
      Fa2 (fun (o : List (Nat × Nat) × Bytes) (op : Stark.Opened F) => ∃ r1 r2,
        evalT tbl (Stark.multiproof (F := F) o.1 o.2
          (Stark.sortDedup (xs.map fun x => x >>> (n0 - Stark.treeLog o.1))) r1) = some (some (op, r2))) L ops
  | [], r, ops, r', h => by
    simp [Stark.openAll, evalT] at h; obtain ⟨rfl, rfl⟩ := h; exact .nil
  | (mats, root) :: os, r, ops, r', h => by
    simp only [Stark.openAll, evalT_bind] at h
    cases h1 : evalT tbl (Stark.multiproof (F := F) mats root
        (Stark.sortDedup (xs.map fun x => x >>> (n0 - Stark.treeLog mats))) r) with
    | none => rw [h1] at h; cases h
    | some res =>
      rw [h1] at h
      simp only [Option.bind_some] at h
      cases res with
      | none => simp [evalT] at h
      | some opr =>
        obtain ⟨op, r1⟩ := opr
        simp only [evalT_bind] at h
        cases h2 : evalT tbl (Stark.openAll (F := F) n0 xs os r1) with
        | none => rw [h2] at h; cases h
        | some res2 =>
          rw [h2] at h
          simp only [Option.bind_some] at h
          cases res2 with
          | none => simp [evalT] at h
          | some opr2 =>
            obtain ⟨ops2, r3⟩ := opr2
            simp only [evalT, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .cons ⟨r, r1, h1⟩ (openAll_spec tbl n0 xs os r1 ops2 r3 h2)

end

end ZkFormal.Bcs.Adapter
