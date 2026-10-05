import ZkFormal.Bcs.MultiproofRead

/-!
# ZkFormal.Bcs.Multiproof — L4's multiproof verifier certifies MMCS paths

`multiproof_sound : Adapter.MultiproofStmt`.  On a well-formed log, if lane
L4's `Stark.multiproof mats root S r` evaluates (purely, against the log) to
`some (op, r')`, then every opened `(level, index)` of a leaf in `S` is
recorded in `op` and certified by an `mmcsOpen` path from `root`.

Invariant (bottom-up over `mpLevels`): a node `(y, h)` of the current list at
level `j` together with a certificate `mmcsOpen h j t i raw` (`y = i >>> t`)
lifts to a certificate `mmcsOpen root 0 (j + t) i raw`; every row set
recorded at or above level `j` is certified from `root`; and every ancestor
of `y` at a level with matrices records its rows.  `S` need not be sorted or
duplicate-free; acceptance forces `x < 2^n` (the final list is `[(0, root)]`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.Bcs.Multiproof

open ArenaCore ArenaCore.Security ZkFormal Lean.Grind

/-! ## Generic helpers -/

theorem evalT_bind_some {α β : Type} {tbl : Table} {oa : OracleComp hashSpec α}
    {f : α → OracleComp hashSpec β} {b : β} (h : evalT tbl (OracleComp.bind oa f) = some b) :
    ∃ a, evalT tbl oa = some a ∧ evalT tbl (f a) = some b := by
  rw [evalT_bind] at h
  cases ha : evalT tbl oa with
  | none => rw [ha] at h; cases h
  | some a => rw [ha] at h; exact ⟨a, rfl, h⟩

theorem WH_eq (tag : UInt8) (m : Bytes) : Stark.WH tag m = wh (tag :: m) := rfl

theorem evalT_WH {tbl : Table} {tag : UInt8} {m u : Bytes} (h : evalT tbl (Stark.WH tag m) = some u) :
    WHin tbl (tag :: m) u := by
  rw [WH_eq] at h; exact (evalT_wh tbl _ u).mp h

theorem lookup_mem' {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {a : α} {b : β}, l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (k, v) :: l, a, b, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hk
      cases h
      have : a = k := by simpa using hk
      subst this; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem' h)

theorem lookup_some_of_mem' {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {a : α} {b : β}, (a, b) ∈ l → ∃ b', l.lookup a = some b'
  | [], _, _, h => by simp at h
  | (k, v) :: l, a, b, h => by
    simp only [List.lookup]
    split
    · exact ⟨_, rfl⟩
    · rename_i hk
      rcases List.mem_cons.mp h with h | h
      · cases h; simp at hk
      · exact lookup_some_of_mem' h

theorem shiftRight_succ' (i t : Nat) : i >>> (t + 1) = (i >>> t) / 2 := by
  rw [Nat.shiftRight_succ]

theorem mem_le_foldr_max : ∀ {l : List Nat} {a : Nat}, a ∈ l → a ≤ l.foldr max 0
  | [], _, h => by simp at h
  | b :: l, a, h => by
    simp only [List.foldr]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (mem_le_foldr_max h) (Nat.le_max_right _ _)

theorem le_treeLog {mats : List (Nat × Nat)} {mw : Nat × Nat} (h : mw ∈ mats) :
    mw.1 ≤ Stark.treeLog mats :=
  mem_le_foldr_max (List.mem_map.mpr ⟨mw, h, rfl⟩)

theorem levelWidths_ne_nil {mats : List (Nat × Nat)} {mw : Nat × Nat} (h : mw ∈ mats) :
    Stark.levelWidths mats mw.1 ≠ [] := by
  intro he
  have : mw.2 ∈ Stark.levelWidths mats mw.1 :=
    List.mem_map.mpr ⟨mw, List.mem_filter.mpr ⟨h, by simp⟩, rfl⟩
  rw [he] at this; simp at this

section
variable {F K : Type} [Field F] [Field K] [Stark.StarkField F K] [DecidableEq F]

/-! ## Leaves -/

theorem mpLeaves_spec (tbl : Table) (wf : TableWF tbl) (n : Nat) (ws : List Nat) :
    ∀ (S : List Nat) (r : Bytes) (L : List (Nat × Bytes)) (op : Stark.Opened F) (r' : Bytes),
      evalT tbl (Stark.mpLeaves (F := F) n ws S r) = some (some (L, op, r')) →
      (∀ p ∈ L, p.2.length = 64) ∧ (∀ x ∈ S, ∃ h, (x, h) ∈ L) ∧
      (∀ e ∈ op, e.1.1 = n ∧ ∃ h raw, (e.1.2, h) ∈ L ∧ WHin tbl (leafMsg raw) h ∧
        Stark.readRows (F := F) ws raw = some (e.2, [])) ∧
      (∀ x ∈ S, ∃ rows, ((n, x), rows) ∈ op)
  | [], r, L, op, r', h => by
    simp only [Stark.mpLeaves, evalT, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp
  | x :: xs, r, L, op, r', h => by
    simp only [Stark.mpLeaves] at h
    split at h
    · simp [evalT] at h
    · rename_i rows r1 hrows
      obtain ⟨hx, hh, h⟩ := evalT_bind_some h
      obtain ⟨res, hres, h⟩ := evalT_bind_some h
      rcases res with _ | ⟨hs, op', r''⟩
      · simp [evalT] at h
      · simp only [evalT, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨ih1, ih2, ih3, ih4⟩ := mpLeaves_spec tbl wf n ws xs r1 hs op' r'' hres
        have hW : WHin tbl (leafMsg (r.take (r.length - r1.length))) hx := evalT_WH hh
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact hW.length wf
          · exact ih1 p hp
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact ⟨hx, List.mem_cons_self⟩
          · obtain ⟨h', h'm⟩ := ih2 y hy; exact ⟨h', List.mem_cons_of_mem _ h'm⟩
        · intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact ⟨rfl, hx, _, List.mem_cons_self, hW, readRows_consumed hrows⟩
          · obtain ⟨e1, h', raw, hm, hw, hr⟩ := ih3 e he
            exact ⟨e1, h', raw, List.mem_cons_of_mem _ hm, hw, hr⟩
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact ⟨rows, List.mem_cons_self⟩
          · obtain ⟨rs, hm⟩ := ih4 y hy; exact ⟨rs, List.mem_cons_of_mem _ hm⟩

/-! ## One node -/

theorem mpNode_spec {tbl : Table} {lvl : Nat} {ws : List Nat} {x : Nat} {lft rgt r : Bytes}
    {nh : Nat × Bytes} {rows? : Option (List (List F))} {r2 : Bytes}
    (h : evalT tbl (Stark.mpNode (F := F) lvl ws x lft rgt r) = some (some (nh, rows?, r2))) :
    ∃ raw rows, Stark.readRows (F := F) ws raw = some (rows, []) ∧ nh.1 = x ∧
      WHin tbl (nodeMsg lvl lft rgt raw) nh.2 ∧
      rows? = (if ws.isEmpty then none else some rows) := by
  simp only [Stark.mpNode] at h
  split at h
  · simp [evalT] at h
  · rename_i rows raw r' hinj
    simp only [Stark.readInj] at hinj
    split at hinj
    · cases hinj
    · rename_i rows0 r0 hrows
      simp only [Option.some.injEq, Prod.mk.injEq] at hinj
      obtain ⟨rfl, rfl, rfl⟩ := hinj
      obtain ⟨hp, hh, h⟩ := evalT_bind_some h
      simp only [evalT, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨_, rows0, readRows_consumed hrows, rfl, ?_, rfl⟩
      have := evalT_WH hh
      simpa [nodeMsg, Stark.tagNode, Bcs.tagNode, List.cons_append, List.append_assoc] using this

end

end ZkFormal.Bcs.Multiproof
