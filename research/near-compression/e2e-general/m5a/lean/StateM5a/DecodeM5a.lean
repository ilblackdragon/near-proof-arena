import StateM5a.DecodeWalk

/-!
# StateM5a.DecodeM5a — the M5a walk traffic from `Holds`

Instantiates `DecodeWalk` for the exported AIR: `BR` (table 2) and `SN` (table 3) are walk tables,
`WSB` (table 5) the root table.  Their `DOWN`/`UP` interactions are read off the tables
(`pick`: the unique interaction on `(bus, side)`; the `*_filter` lemmas pin that it is unique and
its multiplicity bit), so the decoded rows are the AIR's rows.

**`walk_traffic`**: for the AIR the prover runs — `m5aAir D` followed by any tables `extra` that
do not use `DOWN`/`UP` (the SHA-512 chip, the public tape) — `Holds` gives, for *any* decoder
`Dc`, the two permutations `bus_batched_changes` / `Traffic.walk_sem` take:

  `downSends roots rows ~ downRecvs rows`,  `upSends rows ~ upRecvs roots rows`

with `rows = rowsOf Dc brW … 2 ++ rowsOf Dc snW … 3` (one `WRow` per active `BR`/`SN` row) and
`roots = rootsOf Dc wsbR … 5` (one `Root` per INTAKE / FINAL `WSB` row).
-/

namespace StateM5a.DecodeM5a

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk

/-! ## Reading the interactions off the tables -/

/-- The first interaction of `is` on `(b, s)`. -/
def pick (is : List Interaction) (b : Nat) (s : Bool) : Interaction :=
  (is.filter fun i => decide (i.bus = b ∧ i.send = s)).headD default

@[simp] theorem filter_ff {α : Type} (l : List α) : l.filter (fun _ => false) = [] := by
  induction l <;> simp_all

@[simp] theorem flatMap_nil' {α β : Type} (l : List α) : l.flatMap (fun _ => ([] : List β)) = [] := by
  induction l <;> simp_all

def noBus (is : List Interaction) (b : Nat) : Bool := is.all fun i => i.bus != b

theorem not_on_of_noBus {is : List Interaction} {b : Nat} (h : noBus is b = true) (s : Bool) :
    ∀ i ∈ is, ¬ (i.bus = b ∧ i.send = s) := by
  intro i hi ⟨e, _⟩
  have := List.all_eq_true.1 h i hi
  simp [e] at this

/-- The walk tables and the root table. -/
def brW : WalkIx where
  g := Br.gold
  gdn := Br.c "gdn"
  di := (pick Br.interactions B_DOWN false).msg
  dd := (pick Br.interactions B_DOWN true).msg
  ui := (pick Br.interactions B_UP false).msg
  uo := (pick Br.interactions B_UP true).msg

def snW : WalkIx where
  g := Sn.c "mF" + Sn.c "mU" + Sn.c "mD"
  gdn := Sn.c "gdn"
  di := (pick Sn.interactions B_DOWN false).msg
  dd := (pick Sn.interactions B_DOWN true).msg
  ui := (pick Sn.interactions B_UP false).msg
  uo := (pick Sn.interactions B_UP true).msg

/-- `WSB`: INTAKE roots (`g0 = (1 − ph)·real`) and FINAL roots (`gw = ph·wr`). -/
def wsbR : RootIx where
  g₁ := (1 - Wsb.c "ph") * Wsb.c "real"
  d₁ := (pick Wsb.interactions B_DOWN true).msg
  u₁ := (pick Wsb.interactions B_UP false).msg
  g₂ := Wsb.c "ph" * Wsb.c "wr"
  d₂ := (pick (Wsb.interactions.filter fun i => decide (i.bus = B_DOWN ∧ i.send = true)).tail B_DOWN true).msg
  u₂ := (pick (Wsb.interactions.filter fun i => decide (i.bus = B_UP ∧ i.send = false)).tail B_UP false).msg

set_option maxRecDepth 100000

macro "filt" : tactic => `(tactic| simp [pick, Br.interactions, Sn.interactions, Wsb.interactions, Br.serBytes,
  Sn.serBytes, Br.rec, Sn.rec, snd, rcv, sndBits, comp, B_DOWN, B_UP, B_SHA_BYTES, B_SHA_DIGEST, B_VER,
  B_RNG, B_NIB, B_KLEN, B_SIBQ, B_SIBA, B_MATQ, B_MATR, B_SPQ, B_SPR, B_EPQ, B_SXQ, B_SXR, B_KC, B_KCR, B_KDIG,
  B_ORD, B_TREE, B_TCH, B_IF384, List.filter_append, List.filter_map, Function.comp_def, List.filter_flatMap])

theorem br_dr : Br.interactions.filter (fun i => decide (i.bus = B_DOWN ∧ i.send = false)) =
    [{ bus := B_DOWN, mult := [brW.g], msg := brW.di, send := false }] := by simp [brW]; filt
theorem br_ds : Br.interactions.filter (fun i => decide (i.bus = B_DOWN ∧ i.send = true)) =
    [{ bus := B_DOWN, mult := [brW.gdn], msg := brW.dd, send := true }] := by simp [brW]; filt
theorem br_ur : Br.interactions.filter (fun i => decide (i.bus = B_UP ∧ i.send = false)) =
    [{ bus := B_UP, mult := [brW.gdn], msg := brW.ui, send := false }] := by simp [brW]; filt
theorem br_us : Br.interactions.filter (fun i => decide (i.bus = B_UP ∧ i.send = true)) =
    [{ bus := B_UP, mult := [brW.g], msg := brW.uo, send := true }] := by simp [brW]; filt
theorem sn_dr : Sn.interactions.filter (fun i => decide (i.bus = B_DOWN ∧ i.send = false)) =
    [{ bus := B_DOWN, mult := [snW.g], msg := snW.di, send := false }] := by simp [snW]; filt
theorem sn_ds : Sn.interactions.filter (fun i => decide (i.bus = B_DOWN ∧ i.send = true)) =
    [{ bus := B_DOWN, mult := [snW.gdn], msg := snW.dd, send := true }] := by simp [snW]; filt
theorem sn_ur : Sn.interactions.filter (fun i => decide (i.bus = B_UP ∧ i.send = false)) =
    [{ bus := B_UP, mult := [snW.gdn], msg := snW.ui, send := false }] := by simp [snW]; filt
theorem sn_us : Sn.interactions.filter (fun i => decide (i.bus = B_UP ∧ i.send = true)) =
    [{ bus := B_UP, mult := [snW.g], msg := snW.uo, send := true }] := by simp [snW]; filt

theorem wsb_ds : Wsb.interactions.filter (fun i => decide (i.bus = B_DOWN ∧ i.send = true)) =
    [{ bus := B_DOWN, mult := [wsbR.g₁], msg := wsbR.d₁, send := true },
     { bus := B_DOWN, mult := [wsbR.g₂], msg := wsbR.d₂, send := true }] := by simp [wsbR]; filt
theorem wsb_ur : Wsb.interactions.filter (fun i => decide (i.bus = B_UP ∧ i.send = false)) =
    [{ bus := B_UP, mult := [wsbR.g₁], msg := wsbR.u₁, send := false },
     { bus := B_UP, mult := [wsbR.g₂], msg := wsbR.u₂, send := false }] := by simp [wsbR]; filt
theorem wsb_dr : Wsb.interactions.filter (fun i => decide (i.bus = B_DOWN ∧ i.send = false)) = [] := by filt
theorem wsb_us : Wsb.interactions.filter (fun i => decide (i.bus = B_UP ∧ i.send = true)) = [] := by filt

/-! ## The `UP` messages repeat the walk position of the `DOWN` they answer -/

theorem br_hU : brW.uo.take 2 = brW.di.take 2 := by simp [brW]; filt
theorem br_hI : brW.ui.take 2 = brW.dd.take 2 := by simp [brW]; filt
theorem sn_hU : snW.uo.take 2 = snW.di.take 2 := by simp [snW]; filt
theorem sn_hI : snW.ui.take 2 = snW.dd.take 2 := by simp [snW]; filt
theorem wsb_h₁ : wsbR.u₁.take 2 = wsbR.d₁.take 2 := by simp [wsbR]; filt
theorem wsb_h₂ : wsbR.u₂.take 2 = wsbR.d₂.take 2 := by simp [wsbR]; filt

/-! ## The other tables do not use `DOWN` / `UP` -/

theorem nb_sha (b : Nat) (hb : b = B_DOWN ∨ b = B_UP) : noBus shaTable.interactions b = true := by
  rcases hb with rfl | rfl <;> decide
theorem nb_key (b : Nat) (hb : b = B_DOWN ∨ b = B_UP) : noBus Key.table.interactions b = true := by
  rcases hb with rfl | rfl <;> decide
theorem nb_kcmp (b : Nat) (hb : b = B_DOWN ∨ b = B_UP) : noBus Kcmp.table.interactions b = true := by
  rcases hb with rfl | rfl <;> decide
theorem nb_wsn (b : Nat) (hb : b = B_DOWN ∨ b = B_UP) : noBus Wsn.interactions b = true := by
  rcases hb with rfl | rfl <;> decide
theorem nb_wsa (b : Nat) (hb : b = B_DOWN ∨ b = B_UP) : noBus Wsa.table.interactions b = true := by
  rcases hb with rfl | rfl <;> decide
theorem nb_snc (b : Nat) (hb : b = B_DOWN ∨ b = B_UP) : noBus Snc.table.interactions b = true := by
  rcases hb with rfl | rfl <;> decide
theorem nb_rng (b : Nat) (hb : b = B_DOWN ∨ b = B_UP) : noBus Rng.table.interactions b = true := by
  rcases hb with rfl | rfl <;> decide
theorem nb_wsl (b : Nat) (hb : b = B_DOWN ∨ b = B_UP) : noBus Wsl.table.interactions b = true := by
  rcases hb with rfl | rfl <;> decide
theorem nb_wsp (b : Nat) (hb : b = B_DOWN ∨ b = B_UP) : noBus Wsp.interactions b = true := by
  rcases hb with rfl | rfl <;> decide

/-! ## The bus lists of the AIR -/

section
variable {tr : Trace Fp} {pub : List Fp}

theorem tbl_nil {is : List Interaction} {t b : Nat} {s : Bool} (h : noBus is b = true) :
    tableBusList is tr t pub b s = [] := tableBusList_nil is tr t pub b s (not_on_of_noBus h s)

theorem tbl_nil' {is : List Interaction} {t b : Nat} {s : Bool}
    (h : is.filter (fun i => decide (i.bus = b ∧ i.send = s)) = []) : tableBusList is tr t pub b s = [] :=
  tableBusList_nil is tr t pub b s (fun i hi hb => by
    have := List.filter_eq_nil_iff.1 h i hi
    simp_all)

theorem tbl_two (is : List Interaction) (m₁ m₂ : Expr) (msg₁ msg₂ : List Expr) (t b : Nat) (s : Bool)
    (h : is.filter (fun i => decide (i.bus = b ∧ i.send = s)) =
      [{ bus := b, mult := [m₁], msg := msg₁, send := s }, { bus := b, mult := [m₂], msg := msg₂, send := s }]) :
    tableBusList is tr t pub b s = sel2 tr t pub m₁ msg₁ m₂ msg₂ := by
  simp only [tableBusList, sel2]
  congr 1
  funext r
  rw [rowBusList_two is m₁ m₂ msg₁ msg₂ tr t r pub b s h]
  rfl

/-- The bus list of the Lean AIR on `DOWN` / `UP`: only `BR`, `SN`, `WSB` contribute. -/
theorem busList_m5a (D b : Nat) (s : Bool) (hb : b = B_DOWN ∨ b = B_UP) :
    busList (m5aAir D) tr pub b s =
      tableBusList Br.interactions tr 2 pub b s ++ tableBusList Sn.interactions tr 3 pub b s ++
        tableBusList Wsb.interactions tr 5 pub b s := by
  simp only [busList, m5aAir, busList.go]
  rw [tbl_nil (nb_sha b hb), tbl_nil (nb_key b hb), tbl_nil (nb_kcmp b hb),
    tbl_nil (is := (Wsn.table D).interactions) (nb_wsn b hb), tbl_nil (nb_wsa b hb), tbl_nil (nb_snc b hb), tbl_nil (nb_rng b hb),
    tbl_nil (nb_wsl b hb), tbl_nil (is := (Wsp.table D).interactions) (nb_wsp b hb)]
  simp only [Br.table, Sn.table, Wsb.table, List.nil_append, List.append_nil, List.append_assoc, Nat.zero_add,
    Nat.reduceAdd]

end

/-! ## `gdn ⇒ g` -/

section
variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

theorem eval_one_ev {e : Expr} (h : e.eval tr t r pub = 1) : ev tr t r pub e = 1 := by
  unfold ev; rw [h]; rfl

theorem ev_one_eval {e : Expr} (h : ev tr t r pub e = 1) : e.eval tr t r pub = 1 := Fp.ext h

theorem br_gdn_g (hc : ∀ e ∈ Br.table.constraints, e.eval tr t r pub = 0) :
    brW.gdn.eval tr t r pub = 1 → brW.g.eval tr t r pub = 1 := fun h =>
  ev_one_eval (FieldWalk.br_gdn_gold hc (eval_one_ev h))

theorem sn_gdn_g (hc : ∀ e ∈ Sn.table.constraints, e.eval tr t r pub = 0) :
    snW.gdn.eval tr t r pub = 1 → snW.g.eval tr t r pub = 1 := fun h =>
  ev_one_eval (FieldWalk2.sn_gdn_walk hc (eval_one_ev h)).1

end

/-! ## The walk traffic -/

/-- The AIR the prover runs: the Lean AIR followed by `extra` tables. -/
def fullAir (D : Nat) (extra : List Table) (nb np : Nat) : Air :=
  { tables := (m5aAir D).tables ++ extra, numBuses := nb, numPub := np }

/-- The decoded walk rows (`BR`, then `SN`) and walk roots (`WSB`). -/
def walkRows {Ref Pay Res : Type} (Dc : Dec Ref Pay Res) (tr : Trace Fp) (pub : List Fp) :
    List (WRow Ref Pay Res) :=
  rowsOf Dc brW tr 2 pub ++ rowsOf Dc snW tr 3 pub

def walkRoots {Ref Pay Res : Type} (Dc : Dec Ref Pay Res) (tr : Trace Fp) (pub : List Fp) :
    List (Root Ref Pay Res) :=
  rootsOf Dc wsbR tr 5 pub

theorem tbl_br {tr : Trace Fp} {pub : List Fp} (D : Nat) (extra : List Table) (nb np : Nat)
    (hH : Holds (fullAir D extra nb np) pub tr) :
    ∀ r ∈ List.range (tr.height 2), ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0 := fun r hr =>
  hH.constr 2 (by simp [fullAir, m5aAir]) r (List.mem_range.1 hr)

theorem tbl_sn {tr : Trace Fp} {pub : List Fp} (D : Nat) (extra : List Table) (nb np : Nat)
    (hH : Holds (fullAir D extra nb np) pub tr) :
    ∀ r ∈ List.range (tr.height 3), ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0 := fun r hr =>
  hH.constr 3 (by simp [fullAir, m5aAir]) r (List.mem_range.1 hr)

/-- **The walk traffic from `Holds`.**  For any decoder, the decoded `BR`/`SN` rows and `WSB`
roots satisfy `DOWN` and `UP` balance in the record form `Traffic` takes. -/
theorem walk_traffic {Ref Pay Res : Type} (Dc : Dec Ref Pay Res) {tr : Trace Fp} {pub : List Fp}
    (D : Nat) (extra : List Table) (nb np : Nat) (hH : Holds (fullAir D extra nb np) pub tr)
    (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP) :
    (downSends (walkRoots Dc tr pub) (walkRows Dc tr pub)).Perm (downRecvs (walkRows Dc tr pub)) ∧
      (upSends (walkRows Dc tr pub)).Perm (upRecvs (walkRoots Dc tr pub) (walkRows Dc tr pub)) := by
  have hbr := tbl_br D extra nb np hH
  have hsn := tbl_sn D extra nb np hH
  have hgb : ∀ r ∈ List.range (tr.height 2), brW.gdn.eval tr 2 r pub = 1 → brW.g.eval tr 2 r pub = 1 :=
    fun r hr => br_gdn_g (hbr r hr)
  have hgs : ∀ r ∈ List.range (tr.height 3), snW.gdn.eval tr 3 r pub = 1 → snW.g.eval tr 3 r pub = 1 :=
    fun r hr => sn_gdn_g (hsn r hr)
  have ext : ∀ (b : Nat) (s : Bool), (b = B_DOWN ∨ b = B_UP) →
      busList (fullAir D extra nb np) tr pub b s = busList (m5aAir D) tr pub b s := by
    intro b s hb
    exact busList_extend (m5aAir D) extra nb np tr pub b s (fun T hT i hi ⟨e, _⟩ => by
      rcases hb with rfl | rfl
      · exact (hx T hT i hi).1 e
      · exact (hx T hT i hi).2 e)
  have hD := (holds_perm hH B_DOWN).map Dc.down
  have hU := (holds_perm hH B_UP).map Dc.up
  rw [ext _ _ (.inl rfl), ext _ _ (.inl rfl), busList_m5a D _ _ (.inl rfl), busList_m5a D _ _ (.inl rfl)] at hD
  rw [ext _ _ (.inr rfl), ext _ _ (.inr rfl), busList_m5a D _ _ (.inr rfl), busList_m5a D _ _ (.inr rfl)] at hU
  rw [tableBusList_one _ _ _ tr 2 pub _ _ br_ds, tableBusList_one _ _ _ tr 3 pub _ _ sn_ds,
    tbl_two _ _ _ _ _ 5 _ _ wsb_ds, tableBusList_one _ _ _ tr 2 pub _ _ br_dr,
    tableBusList_one _ _ _ tr 3 pub _ _ sn_dr, tbl_nil' wsb_dr] at hD
  rw [tableBusList_one _ _ _ tr 2 pub _ _ br_us, tableBusList_one _ _ _ tr 3 pub _ _ sn_us,
    tbl_nil' wsb_us, tableBusList_one _ _ _ tr 2 pub _ _ br_ur,
    tableBusList_one _ _ _ tr 3 pub _ _ sn_ur, tbl_two _ _ _ _ _ 5 _ _ wsb_ur] at hU
  simp only [List.map_append, List.append_nil] at hD hU
  constructor
  · -- `DOWN`
    have e1 : downSends (walkRoots Dc tr pub) (walkRows Dc tr pub) =
        (sel2 tr 5 pub wsbR.g₁ wsbR.d₁ wsbR.g₂ wsbR.d₂).map Dc.down ++
          ((selL tr 2 pub brW.gdn brW.dd (List.range (tr.height 2))).map Dc.down ++
            (selL tr 3 pub snW.gdn snW.dd (List.range (tr.height 3))).map Dc.down) := by
      simp only [downSends, walkRoots, walkRows, List.filterMap_append, rootsOf_dn]
      rw [show rowsOf Dc brW tr 2 pub = rowsL Dc brW tr 2 pub (List.range (tr.height 2)) from rfl,
        show rowsOf Dc snW tr 3 pub = rowsL Dc snW tr 3 pub (List.range (tr.height 3)) from rfl,
        rowsL_dout _ _ _ _ _ _ hgb, rowsL_dout _ _ _ _ _ _ hgs]
    have e2 : downRecvs (walkRows Dc tr pub) =
        (selL tr 2 pub brW.g brW.di (List.range (tr.height 2))).map Dc.down ++
          (selL tr 3 pub snW.g snW.di (List.range (tr.height 3))).map Dc.down := by
      simp only [downRecvs, walkRows, List.map_append]
      rw [show rowsOf Dc brW tr 2 pub = rowsL Dc brW tr 2 pub (List.range (tr.height 2)) from rfl,
        show rowsOf Dc snW tr 3 pub = rowsL Dc snW tr 3 pub (List.range (tr.height 3)) from rfl,
        rowsL_din, rowsL_din]
    rw [e1, e2]
    exact List.perm_append_comm.trans hD
  · -- `UP`
    have e1 : upSends (walkRows Dc tr pub) =
        (selL tr 2 pub brW.g brW.uo (List.range (tr.height 2))).map Dc.up ++
          (selL tr 3 pub snW.g snW.uo (List.range (tr.height 3))).map Dc.up := by
      simp only [upSends, walkRows, List.map_append]
      rw [show rowsOf Dc brW tr 2 pub = rowsL Dc brW tr 2 pub (List.range (tr.height 2)) from rfl,
        show rowsOf Dc snW tr 3 pub = rowsL Dc snW tr 3 pub (List.range (tr.height 3)) from rfl,
        rowsL_uout _ _ _ _ _ _ br_hU, rowsL_uout _ _ _ _ _ _ sn_hU]
    have e2 : upRecvs (walkRoots Dc tr pub) (walkRows Dc tr pub) =
        (sel2 tr 5 pub wsbR.g₁ wsbR.u₁ wsbR.g₂ wsbR.u₂).map Dc.up ++
          ((selL tr 2 pub brW.gdn brW.ui (List.range (tr.height 2))).map Dc.up ++
            (selL tr 3 pub snW.gdn snW.ui (List.range (tr.height 3))).map Dc.up) := by
      simp only [upRecvs, walkRoots, walkRows, List.filterMap_append]
      rw [rootsOf_up _ _ _ _ _ wsb_h₁ wsb_h₂,
        show rowsOf Dc brW tr 2 pub = rowsL Dc brW tr 2 pub (List.range (tr.height 2)) from rfl,
        show rowsOf Dc snW tr 3 pub = rowsL Dc snW tr 3 pub (List.range (tr.height 3)) from rfl,
        rowsL_uin _ _ _ _ _ _ hgb br_hI, rowsL_uin _ _ _ _ _ _ hgs sn_hI]
    rw [e1, e2]
    exact hU.trans List.perm_append_comm

end StateM5a.DecodeM5a
