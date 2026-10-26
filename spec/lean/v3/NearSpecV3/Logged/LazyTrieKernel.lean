import NearSpecV3.Logged.LazyTrie

/-!
# The kernel-reducible lazy-trie operations compute the well-founded ones

`LazyTrie.lean` defines each lazy operation twice:

* the original, by well-founded recursion on `(mf, sizeOf)` (`findL`, `findRefL`, `allKeysL`,
  `prefixKeysL`, `upsertL`, `delL`). Every `*_spec` theorem is about these.
* a fuelled structural form (`findN`, …, `delN`), which the kernel can evaluate.

This file proves that they agree whenever the fuel is at least the trie's `mf`:
`findN n t key = findL t key` for `t.mf ≤ n`, and likewise for each operation. The proofs go by the
originals' functional induction (`*.mutual_induct`), one case per defining equation.

The call sites are `trieFindL`, `trieFindRefL`, `triePrefixL` (fuel `revealFuel` on `.lz root
revealFuel`, whose `mf` is `revealFuel`) and `applyChangeL` (fuel `t.mf`). So they compute exactly
what they computed with the originals; `ev_trieFindL` and the other spec theorems carry over through
the `*_lz` corollaries at the end.
-/

namespace NearSpecV3.Logged

open NearSpec NearSpecV3 NearSpecV3.D2

/-! ## The level-`n` recursion handles -/

def findRec : Nat → LT → List Nat → TM (Option (Option Bytes))
  | 0 => fun _ _ => pure none
  | n + 1 => findN n

theorem findN_eq_at (n : Nat) : findN n = findAt (findRec n) := by cases n <;> rfl

def findRefRec : Nat → LT → List Nat → TM (Option (Option Nat))
  | 0 => fun _ _ => pure none
  | n + 1 => findRefN n

theorem findRefN_eq_at (n : Nat) : findRefN n = findRefAt (findRefRec n) := by cases n <;> rfl

def allKeysRec : Nat → LT → List Nat → TM (Option (List (List Nat)))
  | 0 => fun _ _ => pure none
  | n + 1 => allKeysN n

theorem allKeysN_eq_at (n : Nat) : allKeysN n = allKeysAt (allKeysRec n) := by cases n <;> rfl

def prefixKeysRec : Nat → LT → List Nat → List Nat → TM (Option (List (List Nat)))
  | 0 => fun _ _ _ => pure none
  | n + 1 => prefixKeysN n

theorem prefixKeysN_eq_at (n : Nat) :
    prefixKeysN n = prefixKeysAt (allKeysN n) (prefixKeysRec n) := by cases n <;> rfl

def upsertRec : Nat → LT → List Nat → Bytes → TM (Option (Nat × LT))
  | 0 => fun _ _ _ => pure none
  | n + 1 => upsertN n

theorem upsertN_eq_at (n : Nat) : upsertN n = upsertAt (upsertRec n) := by cases n <;> rfl

def delRec : Nat → LT → List Nat → TM (Option (Nat × Bool × Option LT))
  | 0 => fun _ _ => pure none
  | n + 1 => delN n

theorem delN_eq_at (n : Nat) : delN n = delAt (delRec n) := by cases n <;> rfl

/-! ## Measure facts -/

theorem mf_lz (h : Bytes) (f : Nat) : (LT.lz h f).mf = f := rfl
theorem mf_ext (k : List Nat) (c : LT) (m : Nat) : (LT.ext k c m).mf = c.mf := rfl
theorem mf_branch (v : Option Slot) (cs : LK) (m : Nat) : (LT.branch v cs m).mf = cs.mf := rfl
theorem mf_none (r : LK) : (LK.none r).mf = r.mf := rfl
theorem mf_some (c : LT) (r : LK) : (LK.some c r).mf = max c.mf r.mf := rfl

/-- The fuel below an expansion suffices for the expanded node. -/
theorem toLT_mf_le {f n : Nat} (r : RNode) (h : f + 1 ≤ n + 1) : (toLT f r).mf ≤ n :=
  Nat.le_trans (toLT_mf f r) (Nat.le_of_succ_le_succ h)

/-- A bind whose continuations agree pointwise. -/
theorem bind_congr' {α β : Type} (x : TM α) {f g : α → TM β} (h : ∀ a, f a = g a) :
    (x >>= f) = (x >>= g) := by
  rw [show f = g from funext h]

/-- The fuel bound passes from a node to a child (`omega` over the `mf` equations). -/
macro "mf_le" : tactic => `(tactic| (simp only [LT.mf, LK.mf] at *; omega))

/-! ## `find` -/

theorem findAt_eq :
    (∀ (t : LT) (key : List Nat) (n : Nat), t.mf ≤ n → findAt (findRec n) t key = findL t key) ∧
    (∀ (cs : LK) (i : Nat) (key : List Nat) (n : Nat), cs.mf ≤ n →
      findAtK (findRec n) cs i key = findLK cs i key) := by
  apply findL.mutual_induct
    (motive1 := fun t key => ∀ n, t.mf ≤ n → findAt (findRec n) t key = findL t key)
    (motive2 := fun cs i key => ∀ n, cs.mf ≤ n → findAtK (findRec n) cs i key = findLK cs i key)
  · intro h key n _; rw [findAt, findL]
  · intro h f key ih n hn
    cases n with
    | zero => simp [LT.mf] at hn
    | succ m =>
      rw [findAt, findL]
      apply bind_congr'
      intro x
      cases x with
      | none => rfl
      | some r =>
        show findRec (m + 1) (toLT f r) key = _
        rw [findRec, findN_eq_at]; exact ih r m (toLT_mf_le r hn)
  · intro v mem key n _; rw [findAt, findL]
  · intro k v mem key hk n _; rw [findAt, findL]
  · intro k c mem key hk ih n hn
    rw [findAt, findL]; simp only [hk, ite_true]; exact ih n hn
  · intro k c mem key hk n _; rw [findAt, findL]; simp only [hk, Bool.false_eq_true, ↓reduceIte]
  · intro cs mem n _; rw [findAt, findL]
  · intro cs mem s n _; rw [findAt, findL]
  · intro v cs mem i rest ih n hn; rw [findAt, findL]; exact ih n hn
  · intro i key n _; rw [findAtK, findLK]
  · intro r key n _; rw [findAtK, findLK]
  · intro c r key ih n hn; rw [findAtK, findLK]; exact ih n (by mf_le)
  · intro r i key ih n hn; rw [findAtK, findLK]; exact ih n hn
  · intro c r i key ih n hn; rw [findAtK, findLK]; exact ih n (by mf_le)

theorem findN_eq (n : Nat) (t : LT) (key : List Nat) (h : t.mf ≤ n) : findN n t key = findL t key := by
  rw [findN_eq_at]; exact findAt_eq.1 t key n h

/-! ## `findRef` -/

theorem findRefAt_eq :
    (∀ (t : LT) (key : List Nat) (n : Nat), t.mf ≤ n → findRefAt (findRefRec n) t key = findRefL t key) ∧
    (∀ (cs : LK) (i : Nat) (key : List Nat) (n : Nat), cs.mf ≤ n →
      findRefAtK (findRefRec n) cs i key = findRefLK cs i key) := by
  apply findRefL.mutual_induct
    (motive1 := fun t key => ∀ n, t.mf ≤ n → findRefAt (findRefRec n) t key = findRefL t key)
    (motive2 := fun cs i key => ∀ n, cs.mf ≤ n → findRefAtK (findRefRec n) cs i key = findRefLK cs i key)
  · intro h key n _; rw [findRefAt, findRefL]
  · intro h f key ih n hn
    cases n with
    | zero => simp [LT.mf] at hn
    | succ m =>
      rw [findRefAt, findRefL]
      apply bind_congr'
      intro x
      cases x with
      | none => rfl
      | some r =>
        show findRefRec (m + 1) (toLT f r) key = _
        rw [findRefRec, findRefN_eq_at]; exact ih r m (toLT_mf_le r hn)
  · intro k v mem key n _; rw [findRefAt, findRefL]
  · intro k c mem key hk ih n hn
    rw [findRefAt, findRefL]; simp only [hk, ite_true]; exact ih n hn
  · intro k c mem key hk n _; rw [findRefAt, findRefL]; simp only [hk, Bool.false_eq_true, ↓reduceIte]
  · intro v cs mem n _; rw [findRefAt, findRefL]
  · intro v cs mem i rest ih n hn; rw [findRefAt, findRefL]; exact ih n hn
  · intro i key n _; rw [findRefAtK, findRefLK]
  · intro r key n _; rw [findRefAtK, findRefLK]
  · intro c r key ih n hn; rw [findRefAtK, findRefLK]; exact ih n (by mf_le)
  · intro r i key ih n hn; rw [findRefAtK, findRefLK]; exact ih n hn
  · intro c r i key ih n hn; rw [findRefAtK, findRefLK]; exact ih n (by mf_le)

theorem findRefN_eq (n : Nat) (t : LT) (key : List Nat) (h : t.mf ≤ n) :
    findRefN n t key = findRefL t key := by
  rw [findRefN_eq_at]; exact findRefAt_eq.1 t key n h

/-! ## `allKeys` -/

theorem allKeysAt_eq :
    (∀ (t : LT) (acc : List Nat) (n : Nat), t.mf ≤ n → allKeysAt (allKeysRec n) t acc = allKeysL t acc) ∧
    (∀ (cs : LK) (i : Nat) (acc : List Nat) (n : Nat), cs.mf ≤ n →
      allKeysAtK (allKeysRec n) cs i acc = allKeysLK cs i acc) := by
  apply allKeysL.mutual_induct
    (motive1 := fun t acc => ∀ n, t.mf ≤ n → allKeysAt (allKeysRec n) t acc = allKeysL t acc)
    (motive2 := fun cs i acc => ∀ n, cs.mf ≤ n → allKeysAtK (allKeysRec n) cs i acc = allKeysLK cs i acc)
  · intro h acc n _; rw [allKeysAt, allKeysL]
  · intro h f acc ih n hn
    cases n with
    | zero => simp [LT.mf] at hn
    | succ m =>
      rw [allKeysAt, allKeysL]
      apply bind_congr'
      intro x
      cases x with
      | none => rfl
      | some r =>
        show allKeysRec (m + 1) (toLT f r) acc = _
        rw [allKeysRec, allKeysN_eq_at]; exact ih r m (toLT_mf_le r hn)
  · intro k v mem acc n _; rw [allKeysAt, allKeysL]
  · intro k c mem acc ih n hn; rw [allKeysAt, allKeysL]; exact ih n hn
  · intro cs mem acc ih n hn; rw [allKeysAt, allKeysL, ih n hn]
  · intro cs mem acc s ih n hn; rw [allKeysAt, allKeysL, ih n hn]
  · intro i acc n _; rw [allKeysAtK, allKeysLK]
  · intro r i acc ih n hn; rw [allKeysAtK, allKeysLK]; exact ih n hn
  · intro c r i acc ih1 ih2 n hn
    rw [allKeysAtK, allKeysLK, ih1 n (by mf_le), ih2 n (by mf_le)]

theorem allKeysN_eq (n : Nat) (t : LT) (acc : List Nat) (h : t.mf ≤ n) :
    allKeysN n t acc = allKeysL t acc := by
  rw [allKeysN_eq_at]; exact allKeysAt_eq.1 t acc n h

/-! ## `prefixKeys` -/

theorem prefixKeysAt_eq :
    (∀ (t : LT) (pre acc : List Nat) (n : Nat), t.mf ≤ n →
      prefixKeysAt (allKeysN n) (prefixKeysRec n) t pre acc = prefixKeysL t pre acc) ∧
    (∀ (cs : LK) (i : Nat) (pre acc : List Nat) (n : Nat), cs.mf ≤ n →
      prefixKeysAtK (allKeysN n) (prefixKeysRec n) cs i pre acc = prefixKeysLK cs i pre acc) := by
  apply prefixKeysL.mutual_induct
    (motive1 := fun t pre acc => ∀ n, t.mf ≤ n →
      prefixKeysAt (allKeysN n) (prefixKeysRec n) t pre acc = prefixKeysL t pre acc)
    (motive2 := fun cs i pre acc => ∀ n, cs.mf ≤ n →
      prefixKeysAtK (allKeysN n) (prefixKeysRec n) cs i pre acc = prefixKeysLK cs i pre acc)
  · intro h pre acc n _; rw [prefixKeysAt, prefixKeysL]
  · intro h f pre acc ih n hn
    cases n with
    | zero => simp [LT.mf] at hn
    | succ m =>
      rw [prefixKeysAt, prefixKeysL]
      apply bind_congr'
      intro x
      cases x with
      | none => rfl
      | some r =>
        show prefixKeysRec (m + 1) (toLT f r) pre acc = _
        rw [prefixKeysRec, prefixKeysN_eq_at]; exact ih r m (toLT_mf_le r hn)
  · intro k v m pre acc hk n hn
    rw [prefixKeysAt, prefixKeysL]; simp only [hk, ite_true]; exact allKeysN_eq n _ acc hn
  · intro k v m pre acc hk n _
    rw [prefixKeysAt, prefixKeysL]; simp only [hk, Bool.false_eq_true, ↓reduceIte]
  · intro k c m pre acc hk ih n hn
    rw [prefixKeysAt, prefixKeysL]; simp only [hk, ite_true]; exact ih n hn
  · intro k c m pre acc hk1 hk2 n hn
    rw [prefixKeysAt, prefixKeysL]; simp only [hk1, hk2, Bool.false_eq_true, ↓reduceIte]
    exact allKeysN_eq n _ acc hn
  · intro k c m pre acc hk1 hk2 n _
    rw [prefixKeysAt, prefixKeysL]; simp only [hk1, hk2, Bool.false_eq_true, ↓reduceIte]
  · intro v cs m acc n hn; rw [prefixKeysAt, prefixKeysL]; exact allKeysN_eq n _ acc hn
  · intro v cs mem i rest acc ih n hn; rw [prefixKeysAt, prefixKeysL]; exact ih n hn
  · intro i pre acc n _; rw [prefixKeysAtK, prefixKeysLK]
  · intro r pre acc n _; rw [prefixKeysAtK, prefixKeysLK]
  · intro c r rest acc ih n hn; rw [prefixKeysAtK, prefixKeysLK]; exact ih n (by mf_le)
  · intro r i rest acc ih n hn; rw [prefixKeysAtK, prefixKeysLK]; exact ih n hn
  · intro c r i rest acc ih n hn; rw [prefixKeysAtK, prefixKeysLK]; exact ih n (by mf_le)

theorem prefixKeysN_eq (n : Nat) (t : LT) (pre acc : List Nat) (h : t.mf ≤ n) :
    prefixKeysN n t pre acc = prefixKeysL t pre acc := by
  rw [prefixKeysN_eq_at]; exact prefixKeysAt_eq.1 t pre acc n h

/-! ## `upsert` -/

theorem upsertAt_eq :
    (∀ (t : LT) (key : List Nat) (v : Bytes) (n : Nat), t.mf ≤ n →
      upsertAt (upsertRec n) t key v = upsertL t key v) ∧
    (∀ (cs : LK) (i : Nat) (key : List Nat) (v : Bytes) (n : Nat), cs.mf ≤ n →
      upsertAtK (upsertRec n) cs i key v = upsertLK cs i key v) := by
  apply upsertL.mutual_induct
    (motive1 := fun t key v => ∀ n, t.mf ≤ n → upsertAt (upsertRec n) t key v = upsertL t key v)
    (motive2 := fun cs i key v => ∀ n, cs.mf ≤ n →
      upsertAtK (upsertRec n) cs i key v = upsertLK cs i key v)
  · intro h key v n _; rw [upsertAt, upsertL]
  · intro h f key v ih n hn
    cases n with
    | zero => simp [LT.mf] at hn
    | succ m =>
      rw [upsertAt, upsertL]
      apply bind_congr'
      intro x
      cases x with
      | none => rfl
      | some r =>
        show upsertRec (m + 1) (toLT f r) key v = _
        rw [upsertRec, upsertN_eq_at]; exact ih r m (toLT_mf_le r hn)
  · intro k s m key v n _; rw [upsertAt, upsertL]
  · intro k c m key v hk ih n hn
    rw [upsertAt, upsertL]; simp only [hk, ite_true]; rw [ih n hn]
  · intro k c m key v hk n _
    rw [upsertAt, upsertL]; simp only [hk, Bool.false_eq_true, ↓reduceIte]
  · intro bv cs m v n _; rw [upsertAt.eq_def, upsertL.eq_def]
  · intro bv cs m i rest v ih n hn; rw [upsertAt, upsertL, ih n hn]
  · intro i key v n _; rw [upsertAtK, upsertLK]
  · intro r key v n _; rw [upsertAtK, upsertLK]
  · intro c r key v ih n hn; rw [upsertAtK, upsertLK, ih n (by mf_le)]
  · intro r i key v ih n hn; rw [upsertAtK, upsertLK, ih n hn]
  · intro c r i key v ih n hn; rw [upsertAtK, upsertLK, ih n (by mf_le)]

theorem upsertN_eq (n : Nat) (t : LT) (key : List Nat) (v : Bytes) (h : t.mf ≤ n) :
    upsertN n t key v = upsertL t key v := by
  rw [upsertN_eq_at]; exact upsertAt_eq.1 t key v n h

/-! ## `del` -/

theorem delAt_eq :
    (∀ (t : LT) (key : List Nat) (n : Nat), t.mf ≤ n → delAt (delRec n) t key = delL t key) ∧
    (∀ (cs : LK) (i : Nat) (key : List Nat) (n : Nat), cs.mf ≤ n →
      delAtAtK (delRec n) cs i key = delAtLK cs i key) := by
  apply delL.mutual_induct
    (motive1 := fun t key => ∀ n, t.mf ≤ n → delAt (delRec n) t key = delL t key)
    (motive2 := fun cs i key => ∀ n, cs.mf ≤ n → delAtAtK (delRec n) cs i key = delAtLK cs i key)
  · intro h key n _; rw [delAt, delL]
  · intro h f key ih n hn
    cases n with
    | zero => simp [LT.mf] at hn
    | succ m =>
      rw [delAt, delL]
      apply bind_congr'
      intro x
      cases x with
      | none => rfl
      | some r =>
        show delRec (m + 1) (toLT f r) key = _
        rw [delRec, delN_eq_at]; exact ih r m (toLT_mf_le r hn)
  · intro k v mem key n _; rw [delAt, delL]
  · intro k c mem key hk ih n hn
    rw [delAt, delL]; simp only [hk, ite_true]; rw [ih n hn]
  · intro k c mem key hk n _
    rw [delAt, delL]; simp only [hk, Bool.false_eq_true, ↓reduceIte]
  · intro cs mem n _; rw [delAt, delL]
  · intro cs mem s n _; rw [delAt, delL]
  · intro v cs mem i rest ih n hn; rw [delAt, delL, ih n hn]
  · intro i key n _; rw [delAtAtK, delAtLK]
  · intro r key n _; rw [delAtAtK, delAtLK]
  · intro c r key ih n hn; rw [delAtAtK, delAtLK, ih n (by mf_le)]
  · intro r i key ih n hn; rw [delAtAtK, delAtLK, ih n hn]
  · intro c r i key ih n hn; rw [delAtAtK, delAtLK, ih n (by mf_le)]

theorem delN_eq (n : Nat) (t : LT) (key : List Nat) (h : t.mf ≤ n) : delN n t key = delL t key := by
  rw [delN_eq_at]; exact delAt_eq.1 t key n h

/-! ## The call sites compute what they computed with the originals -/

theorem findN_lz (root : Bytes) (key : List Nat) :
    findN revealFuel (.lz root revealFuel) key = findL (.lz root revealFuel) key :=
  findN_eq _ _ _ (Nat.le_refl _)

theorem findRefN_lz (root : Bytes) (key : List Nat) :
    findRefN revealFuel (.lz root revealFuel) key = findRefL (.lz root revealFuel) key :=
  findRefN_eq _ _ _ (Nat.le_refl _)

theorem prefixKeysN_lz (root : Bytes) (pre acc : List Nat) :
    prefixKeysN revealFuel (.lz root revealFuel) pre acc = prefixKeysL (.lz root revealFuel) pre acc :=
  prefixKeysN_eq _ _ _ _ (Nat.le_refl _)

theorem upsertN_mf (t : LT) (key : List Nat) (v : Bytes) : upsertN t.mf t key v = upsertL t key v :=
  upsertN_eq _ _ _ _ (Nat.le_refl _)

theorem delN_mf (t : LT) (key : List Nat) : delN t.mf t key = delL t key :=
  delN_eq _ _ _ (Nat.le_refl _)

/-- `applyChangeL` (which now calls `upsertN`/`delN`) is the original well-founded formulation. -/
theorem applyChangeL_eq (t : Option LT) (k : Bytes) (v : Option Bytes) :
    applyChangeL t k v =
      (match v, t with
        | some x, none => pure (some (some (newLeafL (nibbles k) x)))
        | some x, some t => do
          match ← upsertL t (nibbles k) x with
          | some (_, t') => pure (some (some t'))
          | none => pure none
        | none, none => pure (some none)
        | none, some t => do
          match ← delL t (nibbles k) with
          | some (_, _, r) => pure (some r)
          | none => pure none : TM (Option (Option LT))) := by
  unfold applyChangeL
  cases v <;> cases t <;> simp only [upsertN_mf, delN_mf] <;> rfl

end NearSpecV3.Logged
