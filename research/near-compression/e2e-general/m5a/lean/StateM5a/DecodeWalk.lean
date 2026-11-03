import StateM5a.DecodeBus
import StateM5a.Traffic
import StateM5a.FieldWalk2
import StateM5a.FieldWsb

/-!
# StateM5a.DecodeWalk — `DOWN` / `UP` balance of the AIR as `Traffic`'s walk permutations

`Traffic.walk_sem` / `bus_batched_changes` take two permutations of *record-level* lists:
`downSends roots rows ~ downRecvs rows` and `upSends rows ~ upRecvs roots rows`.  This file
derives them from `Holds` of the AIR the prover runs (the Lean `m5aAir D` followed by the tables
the prover adds — the native SHA-512 chip and the public tape — which do not use `DOWN`/`UP`):

* **Generic walk table** (`WalkIx`): one `DOWN` receive and one `UP` send with bit `g` (the
  active walk row), one `DOWN` send and one `UP` receive with bit `gdn` (it descends), the `UP`
  messages repeating the walk id and depth of the `DOWN` message they answer (`take 2` equal), and
  `gdn = 1 ⇒ g = 1` on every row.  Its decoded rows `rowsOf` (one `WRow` per active row) have
  exactly the table's bus lists as their `downRecvs` / `filterMap dout` / `upSends` / child-`UP`
  lists (`rowsOf_*`).
* **Generic root table** (`RootIx`): `WSB`'s two root kinds (INTAKE bit `g0`, FINAL bit `gw`), each
  one `DOWN` send and one `UP` receive (`rootsOf_*`).
* **Decoding** is any function: walk id and depth are the first two message elements read as
  naturals, the rest goes through `Dec.dp` (`DOWN`: ref, payload) and `Dec.dr` (`UP`: result).
  `List.Perm.map` carries the field permutation to the decoded one (no injectivity needed).
* **`walk_traffic`**: the two permutations for `rows = rowsOf BR ++ rowsOf SN`,
  `roots = rootsOf WSB`, from `Holds`.  The `BR`/`SN`/`WSB` interactions on `DOWN`/`UP` are
  pinned by `filter` lemmas against the exported tables (so a change of the AIR breaks the build),
  `gdn ⇒ g` is `FieldWalk.br_gdn_gold` / `FieldWalk2.sn_gdn_walk`.
-/

namespace StateM5a.DecodeWalk

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic

/-! ## Decoders -/

/-- Field decoders of the walk messages. -/
structure Dec (Ref Pay Res : Type) where
  dp : List Fp → Ref × Pay
  dr : List Fp → Res

variable {Ref Pay Res : Type}

def Dec.down (D : Dec Ref Pay Res) (m : List Fp) : Down Ref Pay :=
  ⟨(m.getD 0 0).toNat, (m.getD 1 0).toNat, (D.dp (m.drop 2)).1, (D.dp (m.drop 2)).2⟩

def Dec.up (D : Dec Ref Pay Res) (m : List Fp) : Up Res :=
  ⟨(m.getD 0 0).toNat, (m.getD 1 0).toNat, D.dr (m.drop 2)⟩

/-- Message values on a row. -/
def vals (tr : Trace Fp) (t r : Nat) (pub : List Fp) (l : List Expr) : List Fp :=
  l.map fun e => e.eval tr t r pub

/-- The rows of table `t` whose bit `e` is set, with message `msg` (the shape of
`DecodeBus.tableBusList_one`). -/
def sel (tr : Trace Fp) (t : Nat) (pub : List Fp) (e : Expr) (msg : List Expr) : List (List Fp) :=
  (List.range (tr.height t)).filterMap fun r =>
    if e.eval tr t r pub = 1 then some (vals tr t r pub msg) else none

theorem vals_head {tr : Trace Fp} {t r : Nat} {pub : List Fp} {l l' : List Expr} (h : l.take 2 = l'.take 2)
    (i : Nat) (hi : i < 2) : (vals tr t r pub l).getD i 0 = (vals tr t r pub l').getD i 0 := by
  have : (l.map fun e => e.eval tr t r pub).take 2 = (l'.map fun e => e.eval tr t r pub).take 2 := by
    rw [← List.map_take, ← List.map_take, h]
  simp only [vals, List.getD_eq_getElem?_getD]
  rw [← List.getElem?_take_of_lt (j := 2) hi, this, List.getElem?_take_of_lt hi]

/-! ## A walk table -/

/-- A walk table's four interactions on `DOWN` / `UP`. -/
structure WalkIx where
  g : Expr
  gdn : Expr
  di : List Expr
  dd : List Expr
  ui : List Expr
  uo : List Expr

/-- The decoded active rows of a walk table. -/
def rowsOf (Dc : Dec Ref Pay Res) (W : WalkIx) (tr : Trace Fp) (t : Nat) (pub : List Fp) :
    List (WRow Ref Pay Res) :=
  (List.range (tr.height t)).filterMap fun r =>
    if W.g.eval tr t r pub = 1 then
      some { din := Dc.down (vals tr t r pub W.di),
             dout := if W.gdn.eval tr t r pub = 1 then some (Dc.down (vals tr t r pub W.dd)) else none,
             uin := Dc.dr ((vals tr t r pub W.ui).drop 2),
             uout := Dc.dr ((vals tr t r pub W.uo).drop 2) }
    else none

section Walk
variable (Dc : Dec Ref Pay Res) (W : WalkIx) (tr : Trace Fp) (t : Nat) (pub : List Fp)

/-- The generic statement over any list of row indices. -/
def rowsL (rs : List Nat) : List (WRow Ref Pay Res) :=
  rs.filterMap fun r =>
    if W.g.eval tr t r pub = 1 then
      some { din := Dc.down (vals tr t r pub W.di),
             dout := if W.gdn.eval tr t r pub = 1 then some (Dc.down (vals tr t r pub W.dd)) else none,
             uin := Dc.dr ((vals tr t r pub W.ui).drop 2),
             uout := Dc.dr ((vals tr t r pub W.uo).drop 2) }
    else none

def selL (e : Expr) (msg : List Expr) (rs : List Nat) : List (List Fp) :=
  rs.filterMap fun r => if e.eval tr t r pub = 1 then some (vals tr t r pub msg) else none

theorem rowsL_din (rs : List Nat) :
    (rowsL Dc W tr t pub rs).map (·.din) = (selL tr t pub W.g W.di rs).map Dc.down := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [rowsL, selL, List.filterMap_cons] at ih ⊢
    by_cases h1 : W.g.eval tr t r pub = 1 <;> simp [h1, ih]

theorem rowsL_dout (rs : List Nat) (hg : ∀ r ∈ rs, W.gdn.eval tr t r pub = 1 → W.g.eval tr t r pub = 1) :
    (rowsL Dc W tr t pub rs).filterMap (·.dout) = (selL tr t pub W.gdn W.dd rs).map Dc.down := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have ih' := ih (fun r' hr' => hg r' (List.mem_cons_of_mem _ hr'))
    simp only [rowsL, selL, List.filterMap_cons] at ih' ⊢
    by_cases h1 : W.g.eval tr t r pub = 1
    · by_cases h2 : W.gdn.eval tr t r pub = 1 <;> simp [h1, h2, ih']
    · have h2 : ¬ W.gdn.eval tr t r pub = 1 := fun h => h1 (hg r (List.mem_cons_self ..) h)
      simp [h1, h2, ih']

theorem rowsL_uout (rs : List Nat) (hU : W.uo.take 2 = W.di.take 2) :
    (rowsL Dc W tr t pub rs).map (fun r => (⟨r.din.w, r.din.d, r.uout⟩ : Up Res)) =
      (selL tr t pub W.g W.uo rs).map Dc.up := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [rowsL, selL, List.filterMap_cons] at ih ⊢
    by_cases h1 : W.g.eval tr t r pub = 1
    · simp only [h1, ↓reduceIte, List.map_cons]
      rw [ih]
      congr 1
      simp only [Dec.up, Dec.down]
      rw [vals_head hU 0 (by decide), vals_head hU 1 (by decide)]
    · simp only [h1, ↓reduceIte, List.filterMap_cons_none]; exact ih

theorem rowsL_uin (rs : List Nat) (hg : ∀ r ∈ rs, W.gdn.eval tr t r pub = 1 → W.g.eval tr t r pub = 1)
    (hI : W.ui.take 2 = W.dd.take 2) :
    (rowsL Dc W tr t pub rs).filterMap (fun r => r.dout.map fun c => (⟨c.w, c.d, r.uin⟩ : Up Res)) =
      (selL tr t pub W.gdn W.ui rs).map Dc.up := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have ih' := ih (fun r' hr' => hg r' (List.mem_cons_of_mem _ hr'))
    simp only [rowsL, selL, List.filterMap_cons] at ih' ⊢
    by_cases h1 : W.g.eval tr t r pub = 1
    · by_cases h2 : W.gdn.eval tr t r pub = 1
      · simp only [h1, h2, ↓reduceIte, List.filterMap_cons, Option.map_some, List.map_cons]
        rw [ih']
        congr 1
        simp only [Dec.up, Dec.down]
        rw [vals_head hI 0 (by decide), vals_head hI 1 (by decide)]
      · simp [h1, h2, ih']
    · have h2 : ¬ W.gdn.eval tr t r pub = 1 := fun h => h1 (hg r (List.mem_cons_self ..) h)
      simp [h1, h2, ih']

end Walk

/-! ## A root table (two root kinds) -/

/-- A root table: per kind `k ∈ {1, 2}` a bit, a `DOWN` send and an `UP` receive. -/
structure RootIx where
  g₁ : Expr
  d₁ : List Expr
  u₁ : List Expr
  g₂ : Expr
  d₂ : List Expr
  u₂ : List Expr

def rootRow (Dc : Dec Ref Pay Res) (R : RootIx) (tr : Trace Fp) (t : Nat) (pub : List Fp) (r : Nat) :
    List (Root Ref Pay Res) :=
  (if R.g₁.eval tr t r pub = 1 then
    [{ dn := Dc.down (vals tr t r pub R.d₁), res := Dc.dr ((vals tr t r pub R.u₁).drop 2) }] else []) ++
  (if R.g₂.eval tr t r pub = 1 then
    [{ dn := Dc.down (vals tr t r pub R.d₂), res := Dc.dr ((vals tr t r pub R.u₂).drop 2) }] else [])

def rootsOf (Dc : Dec Ref Pay Res) (R : RootIx) (tr : Trace Fp) (t : Nat) (pub : List Fp) :
    List (Root Ref Pay Res) :=
  (List.range (tr.height t)).flatMap (rootRow Dc R tr t pub)

/-- The field lists of the two kinds, per row (the shape of `DecodeBus.rowBusList_two`). -/
def sel2 (tr : Trace Fp) (t : Nat) (pub : List Fp) (g₁ : Expr) (m₁ : List Expr) (g₂ : Expr) (m₂ : List Expr) :
    List (List Fp) :=
  (List.range (tr.height t)).flatMap fun r =>
    (if g₁.eval tr t r pub = 1 then [vals tr t r pub m₁] else []) ++
    (if g₂.eval tr t r pub = 1 then [vals tr t r pub m₂] else [])

theorem rootsOf_dn (Dc : Dec Ref Pay Res) (R : RootIx) (tr : Trace Fp) (t : Nat) (pub : List Fp) :
    (rootsOf Dc R tr t pub).map (·.dn) = (sel2 tr t pub R.g₁ R.d₁ R.g₂ R.d₂).map Dc.down := by
  simp only [rootsOf, sel2]
  induction List.range (tr.height t) with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.flatMap_cons, List.map_append, ih, rootRow]
    congr 1
    split <;> split <;> rfl

theorem rootsOf_up (Dc : Dec Ref Pay Res) (R : RootIx) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (h₁ : R.u₁.take 2 = R.d₁.take 2) (h₂ : R.u₂.take 2 = R.d₂.take 2) :
    (rootsOf Dc R tr t pub).map (fun q => (⟨q.dn.w, q.dn.d, q.res⟩ : Up Res)) =
      (sel2 tr t pub R.g₁ R.u₁ R.g₂ R.u₂).map Dc.up := by
  simp only [rootsOf, sel2]
  induction List.range (tr.height t) with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.flatMap_cons, List.map_append, ih, rootRow]
    congr 1
    have e1 := vals_head (tr := tr) (t := t) (r := r) (pub := pub) h₁
    have e2 := vals_head (tr := tr) (t := t) (r := r) (pub := pub) h₂
    split <;> split <;> simp only [List.map_cons, List.map_nil, List.nil_append, List.cons_append,
      Dec.up, Dec.down, e1 0 (by decide), e1 1 (by decide), e2 0 (by decide), e2 1 (by decide)]

end StateM5a.DecodeWalk
