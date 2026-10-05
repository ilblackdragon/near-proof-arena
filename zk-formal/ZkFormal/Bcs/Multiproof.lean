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

/-- On a well-formed log (32-byte answers) L4's normalising `Stark.H`
(`fit32`) is invisible: `Stark.WH` evaluates as L2's `wh`. -/
theorem evalT_WH_eq {tbl : Table} (wf : TableWF tbl) (tag : UInt8) (m : Bytes) :
    evalT tbl (Stark.WH tag m) = evalT tbl (wh (tag :: m)) := by
  unfold Stark.WH Stark.H wh
  simp only [OracleComp.bind, evalT]
  have e0 : whq (tag :: m) 0 = tag :: 1 :: m := rfl
  have e1 : whq (tag :: m) 1 = tag :: 2 :: m := rfl
  rw [e0, e1]
  cases ha : tbl.lookup (tag :: 1 :: m) with
  | none => rfl
  | some a =>
    simp only
    cases hb : tbl.lookup (tag :: 2 :: m) with
    | none => rfl
    | some b =>
      simp only [evalT, Stark.fit32_of_length (wf.lookup_length ha),
        Stark.fit32_of_length (wf.lookup_length hb)]

theorem evalT_WH {tbl : Table} (wf : TableWF tbl) {tag : UInt8} {m u : Bytes}
    (h : evalT tbl (Stark.WH tag m) = some u) : WHin tbl (tag :: m) u := by
  rw [evalT_WH_eq wf] at h; exact (evalT_wh tbl _ u).mp h

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

theorem shiftRight_one' (y : Nat) : y >>> 1 = y / 2 := by
  rw [Nat.shiftRight_eq_div_pow]

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
        have hW : WHin tbl (leafMsg (r.take (r.length - r1.length))) hx := evalT_WH wf hh
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

theorem mpNode_spec {tbl : Table} (wf : TableWF tbl) {lvl : Nat} {ws : List Nat} {x : Nat} {lft rgt r : Bytes}
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
      have := evalT_WH wf hh
      simpa [nodeMsg, Stark.tagNode, Bcs.tagNode, List.cons_append, List.append_assoc] using this


/-! ## One level up -/

/-- A node hashed at height `lvl` from 64-byte children and injected bytes `raw`. -/
def NodeAt (tbl : Table) (lvl : Nat) (hp l rr raw : Bytes) : Prop :=
  l.length = 64 ∧ rr.length = 64 ∧ WHin tbl (nodeMsg lvl l rr raw) hp

/-- Postcondition of one `mpUp` level from nodes `L` to parents `L'`, recording `op`. -/
def UpOK (tbl : Table) (k lvl : Nat) (ws : List Nat) (L L' : List (Nat × Bytes))
    (op : Stark.Opened F) : Prop :=
  (∀ p ∈ L', p.2.length = 64) ∧
  (∀ e ∈ op, e.1.1 = k ∧ ∃ hp l rr raw, (e.1.2, hp) ∈ L' ∧ NodeAt tbl lvl hp l rr raw ∧
     Stark.readRows (F := F) ws raw = some (e.2, [])) ∧
  (∀ x h, (x, h) ∈ L → ∃ hp l rr raw, (x / 2, hp) ∈ L' ∧ NodeAt tbl lvl hp l rr raw ∧
     (if x % 2 = 0 then l = h else rr = h) ∧ (ws ≠ [] → ∃ rows, ((k, x / 2), rows) ∈ op))

/-- The `finish` step of `mpUp`: the children `C` of parent `x / 2` (with
digests `lft`, `rgt`), then the rest `Lr`. -/
theorem finish_spec (tbl : Table) (wf : TableWF tbl) (k lvl : Nat) (ws : List Nat) (x : Nat)
    (lft rgt r1 : Bytes)
    (recur : Bytes → OracleComp hashSpec (Option (List (Nat × Bytes) × Stark.Opened F × Bytes)))
    (C Lr : List (Nat × Bytes)) (hlft : lft.length = 64) (hrgt : rgt.length = 64)
    (hC : ∀ c ∈ C, c.1 / 2 = x / 2 ∧ (if c.1 % 2 = 0 then lft = c.2 else rgt = c.2))
    (hrec : ∀ r2 L' op r3, evalT tbl (recur r2) = some (some (L', op, r3)) →
      UpOK (F := F) tbl k lvl ws Lr L' op)
    {L' : List (Nat × Bytes)} {op : Stark.Opened F} {r' : Bytes}
    (h : evalT tbl (OracleComp.bind (Stark.mpNode (F := F) lvl ws (x / 2) lft rgt r1) fun
        | none => .pure none
        | some (nh, rows?, r2) =>
          OracleComp.bind (recur r2) fun
            | none => .pure none
            | some (hs, op, r3) =>
              .pure (some (nh :: hs, (match rows? with
                | some rows => ((k, x / 2), rows) :: op
                | none => op), r3))) = some (some (L', op, r'))) :
    UpOK (F := F) tbl k lvl ws (C ++ Lr) L' op := by
  obtain ⟨res, hres, h⟩ := evalT_bind_some h
  rcases res with _ | ⟨⟨y, hp⟩, rows?, r2⟩
  · simp [evalT] at h
  obtain ⟨raw, rows, hrr, hy, hW, hrows⟩ := mpNode_spec wf hres
  simp only at hy; subst hy; subst hrows
  obtain ⟨res2, hres2, h⟩ := evalT_bind_some h
  rcases res2 with _ | ⟨hs, op0, r3⟩
  · simp [evalT] at h
  obtain ⟨u1, u2, u3⟩ := hrec r2 hs op0 r3 hres2
  have hnode : NodeAt tbl lvl hp lft rgt raw := ⟨hlft, hrgt, hW⟩
  have hfin : L' = (x / 2, hp) :: hs ∧
      op = (if ws.isEmpty then op0 else ((k, x / 2), rows) :: op0) := by
    cases hws : ws.isEmpty <;> simp only [hws, evalT, Option.some.injEq, Prod.mk.injEq] at h <;>
      exact ⟨h.1.symm, by simp [← h.2.1]⟩
  obtain ⟨rfl, rfl⟩ := hfin
  have hhead : ws ≠ [] → ((k, x / 2), rows) ∈ (if ws.isEmpty then op0 else ((k, x / 2), rows) :: op0) := by
    intro hne
    have : ws.isEmpty = false := by cases ws <;> simp_all
    rw [this]; exact List.mem_cons_self
  have htail : ∀ e ∈ op0, e ∈ (if ws.isEmpty then op0 else ((k, x / 2), rows) :: op0) := by
    intro e he
    split
    · exact he
    · exact List.mem_cons_of_mem _ he
  refine ⟨?_, ?_, ?_⟩
  · intro p hp'
    rcases List.mem_cons.mp hp' with rfl | hp'
    · exact hW.length wf
    · exact u1 p hp'
  · intro e he
    split at he
    · obtain ⟨e1, hp2, l, rr, raw2, hm, hn, hr⟩ := u2 e he
      exact ⟨e1, hp2, l, rr, raw2, List.mem_cons_of_mem _ hm, hn, hr⟩
    · rcases List.mem_cons.mp he with rfl | he
      · exact ⟨rfl, hp, lft, rgt, raw, List.mem_cons_self, hnode, hrr⟩
      · obtain ⟨e1, hp2, l, rr, raw2, hm, hn, hr⟩ := u2 e he
        exact ⟨e1, hp2, l, rr, raw2, List.mem_cons_of_mem _ hm, hn, hr⟩
  · intro c hc hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨hc1, hc2⟩ := hC _ hm
      simp only at hc1 hc2
      refine ⟨hp, lft, rgt, raw, by rw [hc1]; exact List.mem_cons_self, hnode, hc2, fun hne => ?_⟩
      exact ⟨rows, by rw [hc1]; exact hhead hne⟩
    · obtain ⟨hp2, l, rr, raw2, hm2, hn, hch, hrw⟩ := u3 c hc hm
      exact ⟨hp2, l, rr, raw2, List.mem_cons_of_mem _ hm2, hn, hch,
        fun hne => (hrw hne).elim fun rs hrs => ⟨rs, htail _ hrs⟩⟩

theorem mpUp_spec (tbl : Table) (wf : TableWF tbl) (k lvl : Nat) (ws : List Nat) :
    ∀ (N : Nat) (L : List (Nat × Bytes)) (r : Bytes), L.length ≤ N → (∀ p ∈ L, p.2.length = 64) →
      ∀ L' op r', evalT tbl (Stark.mpUp (F := F) k lvl ws L r) = some (some (L', op, r')) →
        UpOK (F := F) tbl k lvl ws L L' op := by
  intro N
  induction N with
  | zero =>
    intro L r hN _ L' op r' h
    match L with
    | [] =>
      simp only [Stark.mpUp, evalT, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨by simp, by simp, by simp⟩
  | succ N ih =>
    intro L r hN h64 L' op r' h
    match L with
    | [] =>
      simp only [Stark.mpUp, evalT, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨by simp, by simp, by simp⟩
    | (x, hx) :: tl =>
      have hx64 : hx.length = 64 := h64 _ List.mem_cons_self
      match tl with
      | (x', hx') :: rest =>
        have hx'64 : hx'.length = 64 := h64 _ (List.mem_cons_of_mem _ List.mem_cons_self)
        have hrest64 : ∀ p ∈ rest, p.2.length = 64 := fun p hp =>
          h64 p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))
        have htl64 : ∀ p ∈ (x', hx') :: rest, p.2.length = 64 := fun p hp =>
          h64 p (List.mem_cons_of_mem _ hp)
        have hr : rest.length ≤ N := by simp at hN; omega
        have hr' : ((x', hx') :: rest).length ≤ N := by simp at hN; omega
        simp only [Stark.mpUp] at h
        split at h
        · rename_i hc
          exact finish_spec (F := F) tbl wf k lvl ws x hx hx' r _ [(x, hx), (x', hx')] rest hx64 hx'64
            (by
              intro c hc'
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
              rcases hc' with rfl | rfl
              · simp [hc.1]
              · simp only [hc.2]; refine ⟨by omega, ?_⟩
                rw [ite_eq_right (by omega)]; trivial)
            (fun r2 L' op r3 h => ih rest r2 hr hrest64 L' op r3 h) h
        · split at h
          · simp [evalT] at h
          · rename_i s r1 hs
            have hs64 : s.length = 64 := by
              unfold Stark.take? at hs; split at hs
              · simp only [Option.some.injEq, Prod.mk.injEq] at hs; rw [← hs.1]; simp; omega
              · cases hs
            split at h
            · rename_i hc
              exact finish_spec (F := F) tbl wf k lvl ws x hx s r1 _ [(x, hx)] ((x', hx') :: rest)
                hx64 hs64 (by intro c hc'; simp at hc'; subst hc'; simp [hc])
                (fun r2 L' op r3 h => ih _ r2 hr' htl64 L' op r3 h) h
            · rename_i hc
              exact finish_spec (F := F) tbl wf k lvl ws x s hx r1 _ [(x, hx)] ((x', hx') :: rest)
                hs64 hx64 (by intro c hc'; simp at hc'; subst hc'; simp [hc])
                (fun r2 L' op r3 h => ih _ r2 hr' htl64 L' op r3 h) h
      | [] =>
        simp only [Stark.mpUp] at h
        split at h
        · simp [evalT] at h
        · rename_i s r1 hs
          have hs64 : s.length = 64 := by
            unfold Stark.take? at hs; split at hs
            · simp only [Option.some.injEq, Prod.mk.injEq] at hs; rw [← hs.1]; simp; omega
            · cases hs
          split at h
          · rename_i hc
            exact finish_spec (F := F) tbl wf k lvl ws x hx s r1 _ [(x, hx)] []
              hx64 hs64 (by intro c hc'; simp at hc'; subst hc'; simp [hc])
              (fun r2 L' op r3 h => ih [] r2 (by simp) (by simp) L' op r3 h) h
          · rename_i hc
            exact finish_spec (F := F) tbl wf k lvl ws x s hx r1 _ [(x, hx)] []
              hs64 hx64 (by intro c hc'; simp at hc'; subst hc'; simp [hc])
              (fun r2 L' op r3 h => ih [] r2 (by simp) (by simp) L' op r3 h) h


/-! ## All levels -/

theorem mpLevels_spec (tbl : Table) (wf : TableWF tbl) (mats : List (Nat × Nat)) (n : Nat) :
    ∀ (j : Nat) (L : List (Nat × Bytes)) (r root : Bytes) (op : Stark.Opened F) (r' : Bytes),
      j ≤ n → (∀ p ∈ L, p.2.length = 64) →
      evalT tbl (Stark.mpLevels (F := F) mats n j L r) = some (some (root, op, r')) →
      (∀ e ∈ op, ∃ raw, mmcsOpen tbl n root 0 e.1.1 e.1.2 raw ∧
        Stark.readRows (F := F) (Stark.levelWidths mats e.1.1) raw = some (e.2, [])) ∧
      (∀ y h t i raw, (y, h) ∈ L → mmcsOpen tbl n h j t i raw → y = i >>> t →
        mmcsOpen tbl n root 0 (j + t) i raw) ∧
      (∀ y h, (y, h) ∈ L → ∀ m < j, Stark.levelWidths mats m ≠ [] →
        ∃ rows, ((m, y >>> (j - m)), rows) ∈ op) := by
  intro j
  induction j with
  | zero =>
    intro L r root op r' _ _ h
    simp only [Stark.mpLevels] at h
    split at h
    · rename_i root0
      simp only [evalT, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨by simp, ?_, fun _ _ _ m hm => absurd hm (Nat.not_lt_zero m)⟩
      intro y h t i raw hm hc _
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      rw [← hm.2, Nat.zero_add]; exact hc
    · simp [evalT] at h
  | succ j ih =>
    intro L r root op r' hj h64 h
    simp only [Stark.mpLevels] at h
    obtain ⟨res, hres, h⟩ := evalT_bind_some h
    rcases res with _ | ⟨L1, op1, r1⟩
    · simp [evalT] at h
    obtain ⟨u1, u2, u3⟩ := mpUp_spec (F := F) tbl wf j (n - j) (Stark.levelWidths mats j) L.length L r
      (Nat.le_refl _) h64 L1 op1 r1 hres
    obtain ⟨res2, hres2, h⟩ := evalT_bind_some h
    rcases res2 with _ | ⟨root0, op2, r2⟩
    · simp [evalT] at h
    simp only [evalT, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨A, B, C⟩ := ih L1 r1 _ op2 _ (by omega) u1 hres2
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      rcases List.mem_append.mp he with he | he
      · obtain ⟨e1, hp, l, rr, raw, hm, ⟨hl, hrr, hW⟩, hr⟩ := u2 e he
        refine ⟨raw, ?_, by rw [e1]; exact hr⟩
        have hc : mmcsOpen tbl n hp j 0 e.1.2 raw := by
          simp only [mmcsOpen]
          rw [ite_eq_right (by omega)]
          exact ⟨l, rr, hl, hrr, hW⟩
        have := B e.1.2 hp 0 e.1.2 raw hm hc (Nat.shiftRight_zero).symm
        rw [e1]; simpa using this
      · exact A e he
    · intro y h t i raw hm hc hy
      obtain ⟨hp, l, rr, raw', hm', ⟨hl, hrr, hW⟩, hch, _⟩ := u3 y h hm
      have hdiv : i / 2 ^ t = y := by rw [hy, Nat.shiftRight_eq_div_pow]
      have hc' : mmcsOpen tbl n hp j (t + 1) i raw := by
        simp only [mmcsOpen]
        refine ⟨l, rr, raw', hl, hrr, hW, ?_⟩
        rw [hdiv]
        by_cases hy2 : y % 2 = 0
        · rw [ite_eq_left hy2] at hch ⊢; subst hch; exact hc
        · rw [ite_eq_right hy2] at hch ⊢; subst hch; exact hc
      have := B (y / 2) hp (t + 1) i raw hm' hc' (by rw [shiftRight_succ', ← hy])
      rw [show j + 1 + t = j + (t + 1) by omega]; exact this
    · intro y h hm m hmj hne
      obtain ⟨hp, l, rr, raw', hm', _, _, hrow⟩ := u3 y h hm
      by_cases hmj' : m = j
      · subst hmj'
        obtain ⟨rows, hrows⟩ := hrow hne
        refine ⟨rows, List.mem_append_left _ ?_⟩
        rw [show m + 1 - m = 0 + 1 by omega, shiftRight_succ', Nat.shiftRight_zero]
        exact hrows
      · obtain ⟨rows, hrows⟩ := C (y / 2) hp hm' m (by omega) hne
        refine ⟨rows, List.mem_append_right _ ?_⟩
        rw [show j + 1 - m = 1 + (j - m) by omega, Nat.shiftRight_add, shiftRight_one']
        exact hrows

end

/-! ## The multiproof -/

/-- **L4's multiproof certifies MMCS paths** (`Adapter.MultiproofStmt`). -/
theorem multiproof_sound : Adapter.MultiproofStmt := by
  intro F K _ _ _ _ tbl mats root S r op r' wf h x hx mw hmw
  simp only [Stark.multiproof] at h
  obtain ⟨res, hres, h⟩ := evalT_bind_some h
  rcases res with _ | ⟨L, opL, r1⟩
  · simp [evalT] at h
  obtain ⟨res2, hres2, h⟩ := evalT_bind_some h
  rcases res2 with _ | ⟨root', op', r2⟩
  · simp [evalT] at h
  simp only [evalT] at h
  split at h
  · rename_i heq
    have hroot : root' = root := by simpa using heq
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    subst hroot
    have hn : List.foldr max 0 (List.map (fun x => x.fst) mats) = Stark.treeLog mats := rfl
    rw [hn] at hres hres2
    obtain ⟨l1, l2, l3, l4⟩ := mpLeaves_spec (F := F) tbl wf _ _ S r L opL r1 hres
    obtain ⟨A, B, C⟩ := mpLevels_spec (F := F) tbl wf mats _ _ L r1 root' op' _
      (Nat.le_refl _) l1 hres2
    -- every recorded row set is certified from the root
    have cert : ∀ e ∈ opL ++ op', ∃ raw, mmcsOpen tbl (Stark.treeLog mats) root' 0 e.1.1 e.1.2 raw ∧
        Stark.readRows (F := F) (Stark.levelWidths mats e.1.1) raw = some (e.2, []) := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · obtain ⟨e1, h, raw, hm, hW, hr⟩ := l3 e he
        refine ⟨raw, ?_, by rw [e1]; exact hr⟩
        have hc : mmcsOpen tbl (Stark.treeLog mats) h (Stark.treeLog mats) 0 e.1.2 raw := by
          simp only [mmcsOpen, ite_true]; exact hW
        have := B e.1.2 h 0 e.1.2 raw hm hc (Nat.shiftRight_zero).symm
        rw [e1]; simpa using this
      · exact A e he
    -- the opened position is recorded
    have hkey : ∃ rows, ((mw.1, x >>> (Stark.treeLog mats - mw.1)), rows) ∈ opL ++ op' := by
      have hle := le_treeLog hmw
      by_cases hm : mw.1 = Stark.treeLog mats
      · obtain ⟨rows, hrows⟩ := l4 x hx
        refine ⟨rows, List.mem_append_left _ ?_⟩
        rw [hm, Nat.sub_self, Nat.shiftRight_zero]; exact hrows
      · obtain ⟨hx', hmx⟩ := l2 x hx
        obtain ⟨rows, hrows⟩ := C x hx' hmx mw.1 (by omega) (levelWidths_ne_nil hmw)
        exact ⟨rows, List.mem_append_right _ hrows⟩
    obtain ⟨rows0, hrows0⟩ := hkey
    obtain ⟨rows, hlk⟩ := lookup_some_of_mem' hrows0
    obtain ⟨raw, hc, hr⟩ := cert _ (lookup_mem' hlk)
    exact ⟨rows, raw, hlk, hc, hr⟩
  · cases h

end ZkFormal.Bcs.Multiproof
