import StateM5a.Bus

/-!
# StateM5a.Traffic — the bus-level step: walks, the root chain and the version store from balance

Record-level traffic of the M5a trie tables (decoded messages; `StateM5a.Bus` turns the AIR's
`Holds` into permutations of message lists, and `Bus.perm_decode` carries them to decoded
messages).  Three generic facts, each from a permutation (bus balance) and the table structure:

* **Walks** (`DOWN` / `UP`).  A walk root (`WSB`: walk `w`, at most one per `w`) sends
  `DOWN(w, d₀, ref, pay)` and receives `UP(w, d₀, res)`.  An active trie row receives one
  `DOWN(w, d, ref, pay)`, sends one `UP(w, d, res)`, and, when it descends, sends one
  `DOWN(w, d', …)` with `d' > d` and receives `UP(w, d', res')`.  `UP` does not repeat the node's
  ref, so the parent must know that the row answering at `(w, d')` is the row it addressed:
  `walk_unique` proves that at most one active row receives a `DOWN` at each `(w, d)` (a counting
  argument on the open `DOWN` edges crossing depth `d`: one at depth `0`, never more after).
  `walk_sem`: then *any* row-local property `Sem` that each row's step carries from its child to
  itself holds at every root — the walk induction, by depth.
* **Root chain** (`TCH`).  The writing `WSB` rows `j < N` receive `TCH(j, a j)` and send
  `TCH(j + 1, b j)`; the public tape sends `TCH(0, prev)` and receives `TCH(n, post)`.
  `tch_chain`: `N = n`, `a 0 = prev`, `a (j + 1) = b j`, `post = b (n − 1)` (or `prev`).
* **Version store** (`VER`).  A publisher sends every part of its record under its ref (with
  multiplicity); a reader receives every part of its record under the ref it reads.  If all
  publishers under one ref agree (a version id has one producing row; a digest's publishers hashed
  their records — collision resistance), `ver_recv`: every reader's record *is* a published record
  (parts cannot be mixed).
-/

namespace StateM5a.Traffic

/-! ## Counting helpers -/

theorem countP_le_one {α : Type} {p : α → Bool} :
    ∀ {l : List α}, l.countP p ≤ 1 → ∀ {a b : α}, a ∈ l → b ∈ l → p a = true → p b = true → a = b
  | [], _, _, _, ha, _, _, _ => absurd ha List.not_mem_nil
  | x :: xs, h, a, b, ha, hb, pa, pb => by
    rw [List.countP_cons] at h
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · rfl
      · have : 0 < xs.countP p := List.countP_pos_iff.2 ⟨b, hb', pb⟩
        simp only [pa, ↓reduceIte] at h; omega
    · rcases List.mem_cons.1 hb with rfl | hb'
      · have : 0 < xs.countP p := List.countP_pos_iff.2 ⟨a, ha', pa⟩
        simp only [pb, ↓reduceIte] at h; omega
      · exact countP_le_one (by split at h <;> omega) ha' hb' pa pb

/-- Pointwise `[p] + [q] = [p'] + [q']` sums up. -/
theorem countP_add_congr {α : Type} {p q p' q' : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, (p x).toNat + (q x).toNat = (p' x).toNat + (q' x).toNat) →
      l.countP p + l.countP q = l.countP p' + l.countP q'
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.countP_cons]
    have h1 := h x (List.mem_cons_self ..)
    have h2 := countP_add_congr (l := xs) (fun y hy => h y (List.mem_cons_of_mem _ hy))
    cases hp : p x <;> cases hq : q x <;> cases hp' : p' x <;> cases hq' : q' x <;>
      simp_all <;> omega

/-! ## Walks: `DOWN` / `UP` -/

/-- A decoded `DOWN` message: walk, depth, the node's ref, the walk payload (key, mode, value). -/
structure Down (Ref Pay : Type) where
  w : Nat
  d : Nat
  ref : Ref
  pay : Pay

/-- A decoded `UP` message: walk, depth, the node's result. -/
structure Up (Res : Type) where
  w : Nat
  d : Nat
  res : Res

/-- An active walk row (`BR` / `SN` with `gold = 1`). -/
structure WRow (Ref Pay Res : Type) where
  /-- the `DOWN` it receives -/
  din : Down Ref Pay
  /-- the `DOWN` it sends (it descends) -/
  dout : Option (Down Ref Pay)
  /-- the child's result it receives on `UP` (when it descends) -/
  uin : Res
  /-- the result it sends on `UP`, at `(din.w, din.d)` -/
  uout : Res

/-- A walk root (`WSB`): sends `dn`, receives `UP(dn.w, dn.d, res)`. -/
structure Root (Ref Pay Res : Type) where
  dn : Down Ref Pay
  res : Res

section Walk
variable {Ref Pay Res : Type}

def downSends (roots : List (Root Ref Pay Res)) (rows : List (WRow Ref Pay Res)) :
    List (Down Ref Pay) :=
  roots.map (·.dn) ++ rows.filterMap (·.dout)

def downRecvs (rows : List (WRow Ref Pay Res)) : List (Down Ref Pay) := rows.map (·.din)

def upSends (rows : List (WRow Ref Pay Res)) : List (Up Res) :=
  rows.map fun r => ⟨r.din.w, r.din.d, r.uout⟩

def upRecvs (roots : List (Root Ref Pay Res)) (rows : List (WRow Ref Pay Res)) : List (Up Res) :=
  roots.map (fun q => ⟨q.dn.w, q.dn.d, q.res⟩) ++ rows.filterMap fun r => r.dout.map fun c => ⟨c.w, c.d, r.uin⟩

/-- The table structure the walk argument needs: a row descends within its walk to a strictly
greater depth; a walk has at most one root. -/
structure WalkShape (roots : List (Root Ref Pay Res)) (rows : List (WRow Ref Pay Res)) : Prop where
  deeper : ∀ r ∈ rows, ∀ c, r.dout = some c → c.w = r.din.w ∧ r.din.d < c.d
  rootUniq : ∀ w, roots.countP (fun q => decide (q.dn.w = w)) ≤ 1

/-- Open `DOWN` edges of walk `w` crossing depth `d` (a root sits above depth `0`; a row at depth
`e` descending to `e'` crosses `e + 1 … e'`). -/
def cross (roots : List (Root Ref Pay Res)) (rows : List (WRow Ref Pay Res)) (w d : Nat) : Nat :=
  roots.countP (fun q => decide (q.dn.w = w ∧ d ≤ q.dn.d)) +
  rows.countP (fun r => match r.dout with
    | some c => decide (c.w = w ∧ r.din.d + 1 ≤ d ∧ d ≤ c.d) | none => false)

def sendAt (roots : List (Root Ref Pay Res)) (rows : List (WRow Ref Pay Res)) (w d : Nat) : Nat :=
  roots.countP (fun q => decide (q.dn.w = w ∧ q.dn.d = d)) +
  rows.countP (fun r => match r.dout with | some c => decide (c.w = w ∧ c.d = d) | none => false)

def descAt (rows : List (WRow Ref Pay Res)) (w d : Nat) : Nat :=
  rows.countP (fun r => match r.dout with | some c => decide (c.w = w ∧ r.din.d = d) | none => false)

def recvAt (rows : List (WRow Ref Pay Res)) (w d : Nat) : Nat :=
  rows.countP (fun r => decide (r.din.w = w ∧ r.din.d = d))

theorem sendAt_eq (roots : List (Root Ref Pay Res)) (rows : List (WRow Ref Pay Res)) (w d : Nat) :
    (downSends roots rows).countP (fun m => decide (m.w = w ∧ m.d = d)) = sendAt roots rows w d := by
  simp only [downSends, List.countP_append, List.countP_map, List.countP_filterMap, sendAt]
  congr 1
  apply List.countP_congr
  intro r _
  cases r.dout <;> simp

theorem recvAt_eq (rows : List (WRow Ref Pay Res)) (w d : Nat) :
    (downRecvs rows).countP (fun m => decide (m.w = w ∧ m.d = d)) = recvAt rows w d := by
  simp only [downRecvs, List.countP_map, recvAt]; rfl

theorem descAt_le (roots : List (Root Ref Pay Res)) (rows : List (WRow Ref Pay Res))
    (hs : WalkShape roots rows) (w d : Nat) : descAt rows w d ≤ recvAt rows w d := by
  apply List.countP_mono_left
  intro r hr h
  cases hc : r.dout with
  | none => simp [hc] at h
  | some c =>
    simp only [hc, decide_eq_true_eq] at h
    have := (hs.deeper r hr c hc).1
    simp only [decide_eq_true_eq]; exact ⟨this ▸ h.1, h.2⟩

theorem cross_step (roots : List (Root Ref Pay Res)) (rows : List (WRow Ref Pay Res))
    (hs : WalkShape roots rows) (w d : Nat) :
    cross roots rows w (d + 1) + sendAt roots rows w d = cross roots rows w d + descAt rows w d := by
  have h1 : roots.countP (fun q => decide (q.dn.w = w ∧ d + 1 ≤ q.dn.d)) +
      roots.countP (fun q => decide (q.dn.w = w ∧ q.dn.d = d)) =
      roots.countP (fun q => decide (q.dn.w = w ∧ d ≤ q.dn.d)) + roots.countP (fun _ => false) := by
    apply countP_add_congr
    intro q _
    by_cases hw : q.dn.w = w
    · by_cases h1 : d + 1 ≤ q.dn.d <;> by_cases h2 : q.dn.d = d <;> by_cases h3 : d ≤ q.dn.d <;>
        simp [hw, h1, h2, h3] <;> omega
    · simp [hw]
  have h2 : rows.countP (fun r => match r.dout with
        | some c => decide (c.w = w ∧ r.din.d + 1 ≤ d + 1 ∧ d + 1 ≤ c.d) | none => false) +
      rows.countP (fun r => match r.dout with | some c => decide (c.w = w ∧ c.d = d) | none => false) =
      rows.countP (fun r => match r.dout with
        | some c => decide (c.w = w ∧ r.din.d + 1 ≤ d ∧ d ≤ c.d) | none => false) +
      rows.countP (fun r => match r.dout with | some c => decide (c.w = w ∧ r.din.d = d) | none => false) := by
    apply countP_add_congr
    intro r hr
    cases hc : r.dout with
    | none => simp
    | some c =>
      have hd := (hs.deeper r hr c hc).2
      by_cases hw : c.w = w
      · by_cases h1 : r.din.d + 1 ≤ d <;> by_cases h2 : d ≤ c.d <;> by_cases h3 : r.din.d = d <;>
          by_cases h4 : d + 1 ≤ c.d <;> by_cases h5 : c.d = d <;> by_cases h6 : r.din.d ≤ d <;>
          simp [hw, h1, h2, h3, h4, h5, h6] <;> omega
      · simp [hw]
  have hz : roots.countP (fun _ => false) = 0 := List.countP_eq_zero.2 (by simp)
  rw [hz] at h1
  simp only [cross, sendAt, descAt] at h1 h2 ⊢
  omega

theorem cross_le_one (roots : List (Root Ref Pay Res)) (rows : List (WRow Ref Pay Res))
    (hs : WalkShape roots rows) (hbal : (downSends roots rows).Perm (downRecvs rows)) (w : Nat) :
    ∀ d, cross roots rows w d ≤ 1
  | 0 => by
    have hz : rows.countP (fun r => match r.dout with
        | some c => decide (c.w = w ∧ r.din.d + 1 ≤ 0 ∧ 0 ≤ c.d) | none => false) = 0 := by
      rw [List.countP_eq_zero]; intro r _; cases r.dout <;> simp
    have hr : roots.countP (fun q => decide (q.dn.w = w ∧ 0 ≤ q.dn.d)) =
        roots.countP (fun q => decide (q.dn.w = w)) := List.countP_congr (by simp)
    have h0 : cross roots rows w 0 = roots.countP (fun q => decide (q.dn.w = w)) := by
      simp only [cross, hz, hr, Nat.add_zero]
    rw [h0]; exact hs.rootUniq w
  | d + 1 => by
    have ih := cross_le_one roots rows hs hbal w d
    have hstep := cross_step roots rows hs w d
    have hsr : sendAt roots rows w d = recvAt rows w d := by
      rw [← sendAt_eq, ← recvAt_eq]; exact hbal.countP_eq _
    have := descAt_le roots rows hs w d
    omega

/-- **One row per walk position.**  At most one active row receives a `DOWN` at `(w, d)`. -/
theorem walk_unique (roots : List (Root Ref Pay Res)) (rows : List (WRow Ref Pay Res))
    (hs : WalkShape roots rows) (hbal : (downSends roots rows).Perm (downRecvs rows)) (w d : Nat) :
    recvAt rows w d ≤ 1 := by
  have hsr : sendAt roots rows w d = recvAt rows w d := by
    rw [← sendAt_eq, ← recvAt_eq]; exact hbal.countP_eq _
  have hle : sendAt roots rows w d ≤ cross roots rows w d := by
    simp only [sendAt, cross]
    apply Nat.add_le_add
    · apply List.countP_mono_left; intro q _ h; simp only [decide_eq_true_eq] at h ⊢; omega
    · apply List.countP_mono_left
      intro r hr h
      cases hc : r.dout with
      | none => simp [hc] at h
      | some c =>
        have hd := (hs.deeper r hr c hc).2
        simp only [hc, decide_eq_true_eq] at h ⊢; omega
  have := cross_le_one roots rows hs hbal w d
  omega

theorem walk_unique' {roots : List (Root Ref Pay Res)} {rows : List (WRow Ref Pay Res)}
    (hs : WalkShape roots rows) (hbal : (downSends roots rows).Perm (downRecvs rows))
    {r r' : WRow Ref Pay Res} (hr : r ∈ rows) (hr' : r' ∈ rows) (hw : r.din.w = r'.din.w)
    (hd : r.din.d = r'.din.d) : r = r' :=
  countP_le_one (walk_unique roots rows hs hbal r'.din.w r'.din.d) hr hr'
    (by simp [hw, hd]) (by simp)

/-- The row answering at `(c.w, c.d)` is the row addressed by `DOWN c`. -/
theorem child_of {roots : List (Root Ref Pay Res)} {rows : List (WRow Ref Pay Res)}
    (hs : WalkShape roots rows) (hD : (downSends roots rows).Perm (downRecvs rows))
    (hU : (upSends rows).Perm (upRecvs roots rows)) {c : Down Ref Pay} {x : Res}
    (hc : c ∈ downSends roots rows) (hx : (⟨c.w, c.d, x⟩ : Up Res) ∈ upRecvs roots rows) :
    ∃ r' ∈ rows, r'.din = c ∧ r'.uout = x := by
  obtain ⟨r', hr', e'⟩ := List.mem_map.1 (hU.mem_iff.2 hx)
  obtain ⟨r'', hr'', e''⟩ := List.mem_map.1 (hD.mem_iff.1 hc)
  simp only [Up.mk.injEq] at e'
  have := walk_unique' hs hD hr' hr'' (by rw [e'.1, e'']) (by rw [e'.2.1, e''])
  subst this
  exact ⟨r', hr', e'', e'.2.2⟩

/-- Rows' depths are bounded. -/
def depthBound (rows : List (WRow Ref Pay Res)) : Nat := rows.foldr (fun r acc => max r.din.d acc) 0

theorem le_depthBound : ∀ {rows : List (WRow Ref Pay Res)} {r}, r ∈ rows → r.din.d ≤ depthBound rows
  | [], _, h => absurd h List.not_mem_nil
  | x :: xs, r, h => by
    simp only [depthBound, List.foldr_cons] at *
    rcases List.mem_cons.1 h with rfl | h'
    · omega
    · have := le_depthBound h'; simp only [depthBound] at this; omega

/-- The local step of a row: from its child's property (if it descends) to its own. -/
def LocalOK (Sem : Nat → Nat → Ref → Pay → Res → Prop) (r : WRow Ref Pay Res) : Prop :=
  match r.dout with
  | none => Sem r.din.w r.din.d r.din.ref r.din.pay r.uout
  | some c => Sem c.w c.d c.ref c.pay r.uin → Sem r.din.w r.din.d r.din.ref r.din.pay r.uout

/-- **The walk induction.**  If every active row's step carries `Sem` from its child to itself,
every row and every root satisfies `Sem` with the result it sends / receives. -/
theorem walk_rows (Sem : Nat → Nat → Ref → Pay → Res → Prop) {roots : List (Root Ref Pay Res)}
    {rows : List (WRow Ref Pay Res)} (hs : WalkShape roots rows)
    (hD : (downSends roots rows).Perm (downRecvs rows)) (hU : (upSends rows).Perm (upRecvs roots rows))
    (hloc : ∀ r ∈ rows, LocalOK Sem r) :
    ∀ n, ∀ r ∈ rows, depthBound rows - r.din.d ≤ n → Sem r.din.w r.din.d r.din.ref r.din.pay r.uout := by
  intro n
  induction n with
  | zero =>
    intro r hr hn
    have hl := hloc r hr
    unfold LocalOK at hl
    cases hc : r.dout with
    | none => rw [hc] at hl; exact hl
    | some c =>
      exfalso
      have hd := (hs.deeper r hr c hc).2
      obtain ⟨r', hr', e, -⟩ := child_of hs hD hU (c := c) (x := r.uin)
        (List.mem_append_right _ (List.mem_filterMap.2 ⟨r, hr, hc⟩))
        (List.mem_append_right _ (List.mem_filterMap.2 ⟨r, hr, by simp [hc]⟩))
      have := le_depthBound hr'
      rw [e] at this; omega
  | succ n ih =>
    intro r hr hn
    have hl := hloc r hr
    unfold LocalOK at hl
    cases hc : r.dout with
    | none => rw [hc] at hl; exact hl
    | some c =>
      rw [hc] at hl
      have hd := (hs.deeper r hr c hc).2
      obtain ⟨r', hr', e, ex⟩ := child_of hs hD hU (c := c) (x := r.uin)
        (List.mem_append_right _ (List.mem_filterMap.2 ⟨r, hr, hc⟩))
        (List.mem_append_right _ (List.mem_filterMap.2 ⟨r, hr, by simp [hc]⟩))
      have hb := le_depthBound hr'
      have := ih r' hr' (by rw [e]; omega)
      rw [e, ex] at this
      exact hl this

/-- **Walk soundness at the roots.** -/
theorem walk_sem (Sem : Nat → Nat → Ref → Pay → Res → Prop) {roots : List (Root Ref Pay Res)}
    {rows : List (WRow Ref Pay Res)} (hs : WalkShape roots rows)
    (hD : (downSends roots rows).Perm (downRecvs rows)) (hU : (upSends rows).Perm (upRecvs roots rows))
    (hloc : ∀ r ∈ rows, LocalOK Sem r) :
    ∀ q ∈ roots, Sem q.dn.w q.dn.d q.dn.ref q.dn.pay q.res := by
  intro q hq
  obtain ⟨r', hr', e, ex⟩ := child_of hs hD hU (c := q.dn) (x := q.res)
    (List.mem_append_left _ (List.mem_map.2 ⟨q, hq, rfl⟩))
    (List.mem_append_left _ (List.mem_map.2 ⟨q, hq, rfl⟩))
  have := walk_rows Sem hs hD hU hloc _ r' hr' (Nat.le_refl _)
  rw [e, ex] at this
  exact this

end Walk

/-! ## The root chain `TCH` -/

section Chain
variable {Ref : Type}

/-- `TCH` sends: the public `(0, prev)` and each writing row's `(j + 1, b j)`. -/
def tchSends (prev : Ref) (N : Nat) (b : Nat → Ref) : List (Nat × Ref) :=
  (0, prev) :: (List.range N).map fun j => (j + 1, b j)

/-- `TCH` receives: the public `(n, post)` and each writing row's `(j, a j)`. -/
def tchRecvs (post : Ref) (n N : Nat) (a : Nat → Ref) : List (Nat × Ref) :=
  (n, post) :: (List.range N).map fun j => (j, a j)

/-- The ref after `j` changes. -/
def chainAt (prev : Ref) (b : Nat → Ref) : Nat → Ref
  | 0 => prev
  | j + 1 => b j

/-- **The root chain.**  Balance of `TCH` makes the writing rows one chain from the public
`prev` to the public `post`: the row count is the public `n`, row `j` starts from the ref row
`j − 1` left (`prev` for `j = 0`), and `post` is the last row's ref. -/
theorem tch_chain {prev post : Ref} {n N : Nat} {a b : Nat → Ref}
    (h : (tchSends prev N b).Perm (tchRecvs post n N a)) :
    N = n ∧ (∀ j, j < N → a j = chainAt prev b j) ∧ post = chainAt prev b n := by
  have hrecv : ∀ j, j < N → (j, a j) ∈ tchSends prev N b := fun j hj =>
    h.mem_iff.2 (List.mem_cons_of_mem _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩))
  have hpost : (n, post) ∈ tchSends prev N b := h.mem_iff.2 (List.mem_cons_self ..)
  have hN : N = n := by
    cases N with
    | zero =>
      simp [tchSends] at hpost; exact hpost.1.symm
    | succ N =>
      have hs : (N + 1, b N) ∈ tchRecvs post n (N + 1) a :=
        h.mem_iff.1 (List.mem_cons_of_mem _ (List.mem_map.2 ⟨N, List.mem_range.2 (by omega), rfl⟩))
      simp only [tchRecvs, List.mem_cons, List.mem_map, List.mem_range, Prod.mk.injEq] at hs
      rcases hs with ⟨e, -⟩ | ⟨j, hj, e, -⟩
      · exact e
      · omega
  refine ⟨hN, ?_, ?_⟩
  · intro j hj
    have := hrecv j hj
    simp only [tchSends, List.mem_cons, List.mem_map, List.mem_range, Prod.mk.injEq] at this
    rcases this with ⟨rfl, e⟩ | ⟨i, -, e1, e2⟩
    · exact e
    · subst e1; exact e2.symm
  · simp only [tchSends, List.mem_cons, List.mem_map, List.mem_range, Prod.mk.injEq] at hpost
    rcases hpost with ⟨rfl, e⟩ | ⟨i, -, e1, e2⟩
    · exact e
    · subst e1; exact e2.symm

end Chain

/-! ## The version store `VER` -/

section Store
variable {Ref R P : Type}

/-- The `VER` messages of one record under one ref: part `i` for `i < k`. -/
def verMsgs (k : Nat) (part : R → Nat → P) (x : Ref × R) : List (Ref × Nat × P) :=
  (List.range k).map fun i => (x.1, i, part x.2 i)

/-- **A reader's record is a published record.**  Every part a reader receives under `ref` is
sent by some publisher under `ref`; if all publishers under one ref publish one record (`agree`)
and the parts determine the record (`hext`), the reader's record is that record. -/
theorem ver_recv (k : Nat) (hk : 0 < k) (part : R → Nat → P)
    (hext : ∀ x y, (∀ i, i < k → part x i = part y i) → x = y)
    {pubs recvs : List (Ref × R)} (hbal : (pubs.flatMap (verMsgs k part)).Perm (recvs.flatMap (verMsgs k part)))
    (agree : ∀ ref x y, (ref, x) ∈ pubs → (ref, y) ∈ pubs → x = y) :
    ∀ ref x, (ref, x) ∈ recvs → (ref, x) ∈ pubs := by
  intro ref x hx
  have hpart : ∀ i, i < k → ∃ y, (ref, y) ∈ pubs ∧ part y i = part x i := by
    intro i hi
    have hm : (ref, i, part x i) ∈ recvs.flatMap (verMsgs k part) :=
      List.mem_flatMap.2 ⟨(ref, x), hx, List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩⟩
    obtain ⟨⟨ref', y⟩, hy, hm'⟩ := List.mem_flatMap.1 (hbal.mem_iff.2 hm)
    obtain ⟨i', -, e⟩ := List.mem_map.1 hm'
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, e⟩ := e
    exact ⟨y, hy, e⟩
  obtain ⟨y, hy, -⟩ := hpart 0 hk
  have : x = y := hext x y fun i hi => by
    obtain ⟨z, hz, e⟩ := hpart i hi
    rw [← e, agree ref z y hz hy]
  subst this; exact hy

end Store

end StateM5a.Traffic
