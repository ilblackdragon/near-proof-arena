import StateM5a.DepthBound

/-!
# StateM5a.Tape — the public tape as a Lean table, the `TCH` chain and the writing roots from `Holds`

**The tape.**  The prover adds a table `TAPE` (`prover/src/main.rs`, `harness("TAPE", …)`, cached
and committed by the verifier from the statement) whose rows are the public messages of
`tape.json` (`tracegen.py`): the write log `WRITE(seg, t, kd16, present, len, vh16)` (sent on bus
13) and the trie-root chain's ends `TCH(0, 0, prev_state_root)` (sent) and
`TCH(n, 0, post_state_root)` (received) on bus 14, each with multiplicity one.  `tapeTable tape`
models it as a fixed-content Lean table: one interaction per entry, message the entry's constants,
multiplicity `isFirst` (so exactly once); `m5aTape writes prev post n` is the M5a tape.

**`tch_perm`** (`hT` of `bus_batched_changes`, from `Holds` of `fullAir D (tapeTable tape :: rest)`
with `rest` not using `TCH`): with `wrRows` the writing `WSB` rows (`ph·wr = 1`) in row order,
`N` their number and `a k` / `b k` the decoded refs (`refDec`: flag + 16 limbs) row `k` receives /
sends on `TCH`, `tchSends (dig prev) N b ~ tchRecvs (dig post) n N a`.  The `WSB` `j` column is the
writing row's index (`wsb_j`: `isFirst·j = 0`, `j' = j + ph·wr`), so the `WSB` `TCH` messages are
exactly `(k, a k)`, `(k + 1, b k)`.

**`root_of_row`** (`hroot`): writing row `k` is a decoded `FINAL` root (`WSB`'s `g₂ = ph·wr`) at
depth `0` with input ref `a k`, output ref `b k`, a ref result kind (the constraint
`ph·wr·(rk − H)(rk − HB)(rk − HE)(rk − SAME) = 0`), and payload `(kid, 2 − cp, cl, cv)`; for the
standard decoding (`StdDec`).  `cs` is then **any list of changes matching the writing rows**
(`FinalChanges`): `cs[k]` has key `keyBytes tr kid_k` (the `KEY` table's bytes) and value
`some x` with `cp = 1`, `cl = |x|`, `cv = sha256 x`, or `none` with `cp = 0`.

**`air_final`**: `applyChanges (some T) cs = some (some T')` with `rootHash = post` from `Holds`,
`Sha256CR`, the per-row `LocalOK` (`hloc`, the other agent's), `SncDeeper` and `FinalChanges`.

What `FinalChanges` leaves open (not derived here): that `cs` is the spec's
`sortKV committed` — i.e. that the writing rows' `(kd, cp, cl, cv)` are the tape's last writes per
key in strictly increasing key order.  In the AIR that is the working-set argument (`WSL`/`WSP`
segment updates from `WM` chains, `RCH` from the INTAKE root whose phase-0 leaves are
`KCMP`/`ORD`-ordered; README item 4) plus `KDIG` (`kd = sha256 (keyBytes kid)`, from the `SHA`
table's contract once the `SHA_BYTES` message ids of `SNC` rows are tied to `SN` rows by the
`KC` chain).
-/

namespace StateM5a.Tape

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.FieldRows StateM5a.FieldRows2 StateM5a.KeyDecode
open StateM5a.DecodeShape StateM5a.DepthBound StateM5a.Store StateM5a.BusWalk NearSpec

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## The public tape as a table -/

/-- A fixed-content table: entry `(bus, send, msg)` is one interaction with constant message
`msg`, fired once (row 0). -/
def tapeTable (tape : List (Nat × Bool × List Nat)) : Table :=
  { width := 0, constraints := [], maxLog := 22,
    interactions := tape.map fun e =>
      { bus := e.1, mult := [.isFirst], msg := e.2.2.map Expr.const, send := e.2.1 } }

/-- 32 bytes as 16 big-endian limbs of 16 bits (`pack2`). -/
def pairs : Bytes → List Nat
  | a :: b :: r => (256 * a.toNat + b.toNat) :: pairs r
  | _ => []

/-- 16-bit limbs back to bytes. -/
def limbBytes : List Nat → Bytes
  | [] => []
  | l :: ls => UInt8.ofNat (l / 256) :: UInt8.ofNat (l % 256) :: limbBytes ls

/-- The M5a tape (`tracegen.py`): the writes, then `TCH(0, 0, prev)` sent and `TCH(n, 0, post)`
received. -/
def m5aTape (writes : List (List Nat)) (prev post : Bytes) (n : Nat) : List (Nat × Bool × List Nat) :=
  writes.map (fun w => (B_WRITE, true, w)) ++
    [(B_TCH, true, [0, 0] ++ pairs prev), (B_TCH, false, [n, 0] ++ pairs post)]

theorem limbBytes_pairs : ∀ x : Bytes, x.length % 2 = 0 → limbBytes (pairs x) = x
  | [], _ => rfl
  | [_], h => by simp at h
  | a :: b :: r, h => by
    simp only [pairs, limbBytes]
    rw [limbBytes_pairs r (by simp at h; omega)]
    have ha := UInt8.toNat_lt a
    have hb := UInt8.toNat_lt b
    have e1 : (256 * a.toNat + b.toNat) / 256 = a.toNat := by omega
    have e2 : (256 * a.toNat + b.toNat) % 256 = b.toNat := by omega
    rw [e1, e2, UInt8.ofNat_toNat, UInt8.ofNat_toNat]

theorem pairs_lt : ∀ x : Bytes, ∀ l ∈ pairs x, l < 2 ^ 16
  | [], _, h => by simp [pairs] at h
  | [_], _, h => by simp [pairs] at h
  | a :: b :: r, l, h => by
    simp only [pairs, List.mem_cons] at h
    rcases h with rfl | h
    · have := UInt8.toNat_lt a; have := UInt8.toNat_lt b; omega
    · exact pairs_lt r l h

theorem pairs_length : ∀ x : Bytes, (pairs x).length = x.length / 2
  | [] => rfl
  | [_] => by simp [pairs]
  | a :: b :: r => by simp only [pairs, List.length_cons, pairs_length r]; omega

/-! ## Refs on `TCH` and in the walk messages -/

/-- A ref: flag `0` and 16 limbs is a digest; flag `1` a version id (its first limb). -/
def refDec (m : List Fp) : Ref :=
  if (m.getD 0 0).toNat = 0 then .dig (limbBytes (((m.drop 1).take 16).map Fp.toNat))
  else .vid (m.getD 1 0).toNat

/-- `TCH` messages `(j, ref)`. -/
def tdec (m : List Fp) : Nat × Ref := ((m.getD 0 0).toNat, refDec (m.drop 1))

theorem refDec_append (x : Fp) (ys rest : List Fp) (hy : ys.length = 16) :
    refDec ((x :: ys) ++ rest) = refDec (x :: ys) := by
  obtain ⟨y, ys', rfl⟩ : ∃ y ys', ys = y :: ys' := by
    cases ys with
    | nil => simp at hy
    | cons y ys' => exact ⟨y, ys', rfl⟩
  simp only [refDec, List.cons_append, List.getD_cons_zero, List.drop_succ_cons, List.drop_zero,
    List.getD_cons_succ]
  rw [show y :: (ys' ++ rest) = (y :: ys') ++ rest from rfl, List.take_left' hy,
    List.take_of_length_le (by omega)]

/-- **The standard decoding** of the walk messages' refs, payloads and result kinds (what
`StateM5a.Tape` needs of a decoder; the other `Res` fields are free).  `DOWN` after the walk id and
depth: `(refFlag, ref16, kid, mode, vlen, vh16)`; `UP`: `(rk, refFlag, ref16, …)`. -/
structure StdDec (Dc : Dec Ref Pay Res) : Prop where
  ref : ∀ m, (Dc.dp m).1 = refDec m
  kid : ∀ m, (Dc.dp m).2.kid = (m.getD 17 0).toNat
  mode : ∀ m, (Dc.dp m).2.mode = (m.getD 18 0).toNat
  vlen : ∀ m, (Dc.dp m).2.vlen = (m.getD 19 0).toNat
  vh : ∀ m, (Dc.dp m).2.vh = limbBytes (((m.drop 20).take 16).map Fp.toNat)
  rk : ∀ m, (Dc.dr m).rk = (m.getD 0 0).toNat
  rref : ∀ m, (Dc.dr m).ref = refDec (m.drop 1)

/-- Little-endian 16-bit limbs as a number. -/
def limbNum (ls : List Fp) : Nat := ls.foldr (fun x acc => x.toNat + 65536 * acc) 0

/-- A decoder satisfying `StdDec` (so the premise is not vacuous); its other `Res` fields follow
the `UP` layout `(rk, flag, h16, nm4, om4, kid2, st2, alen, avh16, fpres)`. -/
def stdDec : Dec Ref Pay Res where
  dp m := (refDec m, ⟨(m.getD 17 0).toNat, (m.getD 18 0).toNat, (m.getD 19 0).toNat,
    limbBytes (((m.drop 20).take 16).map Fp.toNat)⟩)
  dr m := ⟨(m.getD 0 0).toNat, refDec (m.drop 1), limbNum ((m.drop 18).take 4),
    limbNum ((m.drop 22).take 4), (m.getD 26 0).toNat, (m.getD 27 0).toNat, (m.getD 28 0).toNat,
    limbBytes (((m.drop 29).take 16).map Fp.toNat), (m.getD 45 0).toNat⟩

theorem stdDec_std : StdDec stdDec :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-! ## Generic list facts -/

theorem filterMap_ite {α β : Type} (p : α → Prop) [DecidablePred p] (f : α → β) (l : List α) :
    l.filterMap (fun x => if p x then some (f x) else none) = (l.filter fun x => decide (p x)).map f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : p x
    · simp [h, ih]
    · simp [h, ih]

/-- Rows of `filter p (range h)` listed with their rank. -/
theorem filter_rank {β : Type} (p : Nat → Bool) (f : Nat → β) (g : Nat → Nat) (c : Nat) :
    ∀ h, (∀ r, r < h → p r = true → g r = ((List.range r).filter p).length + c) →
      ((List.range h).filter p).map (fun r => (g r, f r)) =
        (List.range ((List.range h).filter p).length).map
          (fun k => (k + c, f (((List.range h).filter p).getD k 0)))
  | 0, _ => rfl
  | h + 1, hg => by
    have ih := filter_rank p f g c h (fun r hr hp => hg r (by omega) hp)
    rw [List.range_succ, List.filter_append]
    by_cases hp : p h = true
    · have e : [h].filter p = [h] := by simp [hp]
      rw [e, List.map_append, ih, List.length_append, List.length_singleton, List.range_succ,
        List.map_append]
      congr 1
      · apply List.map_congr_left
        intro k hk
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (List.mem_range.1 hk)]
      · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true, Prod.mk.injEq]
        refine ⟨hg h (by omega) hp, ?_⟩
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl
    · have e : [h].filter p = [] := by simp [hp]
      rw [e, List.append_nil, ih]

/-! ## The bus lists of `TCH` -/

section
variable {tr : Trace Fp} {pub : List Fp}

theorem isFirst_one {t r : Nat} : (Expr.isFirst).eval tr t r pub = 1 ↔ r = 0 := by
  constructor
  · intro h
    have := eval_one_ev h
    rw [FieldWsb.ev_isFirst] at this
    split at this
    · assumption
    · exact absurd this (by decide)
  · intro h
    apply ev_one_eval
    rw [FieldWsb.ev_isFirst, if_pos h]

/-- The constant messages of the tape entries on `(b, s)`. -/
def tapeMsgs (tr : Trace Fp) (t : Nat) (pub : List Fp) (tape : List (Nat × Bool × List Nat))
    (b : Nat) (s : Bool) : List (List Fp) :=
  (tape.filter fun e => decide (e.1 = b ∧ e.2.1 = s)).map fun e =>
    e.2.2.map fun c => (Expr.const c).eval tr t 0 pub

theorem tape_row (tape : List (Nat × Bool × List Nat)) (t r : Nat) (b : Nat) (s : Bool) :
    rowBusList (tapeTable tape).interactions tr t r pub b s = if r = 0 then tapeMsgs tr t pub tape b s else [] := by
  simp only [tapeTable, tapeMsgs]
  induction tape with
  | nil => simp [rowBusList]
  | cons e es ih =>
    simp only [rowBusList, List.map_cons, List.flatMap_cons] at ih ⊢
    rw [ih]
    by_cases hr : r = 0
    · subst hr
      by_cases he : e.1 = b ∧ e.2.1 = s
      · simp only [he, and_self, ↓reduceIte, multNat_one, isFirst_one, List.filter_cons, decide_true,
          List.map_cons, List.replicate_one, Interaction.msgVal, List.map_map, Function.comp_def]
        rfl
      · simp [he]
    · simp only [hr, ↓reduceIte, List.append_nil]
      split
      · rw [multNat_one]
        simp only [isFirst_one, hr, ↓reduceIte, List.replicate_zero]
      · rfl

theorem flatMap_range_zero {β : Type} (f : Nat → List β) (hf : ∀ r, r ≠ 0 → f r = []) :
    ∀ h, 0 < h → (List.range h).flatMap f = f 0
  | 0, h => absurd h (by decide)
  | 1, _ => by simp
  | h + 2, _ => by
    rw [List.range_succ, List.flatMap_append, flatMap_range_zero f hf (h + 1) (by omega)]
    simp [hf (h + 1) (by omega)]

theorem tape_table (tape : List (Nat × Bool × List Nat)) (t : Nat) (b : Nat) (s : Bool) :
    tableBusList (tapeTable tape).interactions tr t pub b s = tapeMsgs tr t pub tape b s := by
  unfold tableBusList
  rw [flatMap_range_zero _ (fun r hr => by rw [tape_row, if_neg hr]) (tr.height t) (Nat.two_pow_pos _), tape_row,
    if_pos rfl]

theorem nb_tch_br : noBus Br.interactions B_TCH = true := by decide
theorem nb_tch_sn : noBus Sn.interactions B_TCH = true := by decide

/-- On `TCH`, only `WSB` contributes among the Lean AIR's tables. -/
theorem busList_m5a_tch (D : Nat) (s : Bool) :
    busList (m5aAir D) tr pub B_TCH s = tableBusList Wsb.interactions tr 5 pub B_TCH s := by
  simp only [busList, m5aAir, busList.go]
  rw [tbl_nil (by decide : noBus shaTable.interactions B_TCH = true),
    tbl_nil (by decide : noBus Key.table.interactions B_TCH = true),
    tbl_nil (is := Br.table.interactions) nb_tch_br, tbl_nil (is := Sn.table.interactions) nb_tch_sn,
    tbl_nil (by decide : noBus Kcmp.table.interactions B_TCH = true),
    tbl_nil (is := (Wsn.table D).interactions) (by decide : noBus Wsn.interactions B_TCH = true),
    tbl_nil (by decide : noBus Wsa.table.interactions B_TCH = true),
    tbl_nil (by decide : noBus Snc.table.interactions B_TCH = true),
    tbl_nil (by decide : noBus Rng.table.interactions B_TCH = true),
    tbl_nil (by decide : noBus Wsl.table.interactions B_TCH = true),
    tbl_nil (is := (Wsp.table D).interactions) (by decide : noBus Wsp.interactions B_TCH = true)]
  simp only [Wsb.table, List.nil_append, List.append_nil, busList.go]

/-- **`TCH` of the AIR the prover runs**: the `WSB` messages, then the tape's. -/
theorem busList_tch (D : Nat) (tape : List (Nat × Bool × List Nat)) (rest : List Table) (nb np : Nat)
    (hr : ∀ T ∈ rest, ∀ i ∈ T.interactions, i.bus ≠ B_TCH) (s : Bool) :
    busList (fullAir D (tapeTable tape :: rest) nb np) tr pub B_TCH s =
      tableBusList Wsb.interactions tr 5 pub B_TCH s ++ tapeMsgs tr 12 pub tape B_TCH s := by
  simp only [busList, fullAir]
  rw [busList_go_append]
  simp only [busList.go]
  rw [busList_go_nil tr pub B_TCH s rest _ (fun T hT i hi ⟨e, _⟩ => hr T hT i hi e), List.append_nil]
  rw [show (0 + (m5aAir D).tables.length) = 12 from rfl, tape_table]
  rw [← busList_m5a_tch D s]
  rfl

end

/-! ## The writing `WSB` rows -/

/-- The `FINAL` root bit `gw = ph·wr`. -/
abbrev gw : Expr := Wsb.c "ph" * Wsb.c "wr"

/-- The writing `WSB` rows, in row order. -/
def wrRows (tr : Trace Fp) (pub : List Fp) : List Nat :=
  (List.range (tr.height 5)).filter fun r => decide (gw.eval tr 5 r pub = 1)

theorem wsb_tr_ds : Wsb.interactions.filter (fun i => decide (i.bus = B_TCH ∧ i.send = true)) =
    [{ bus := B_TCH, mult := [gw], msg := [Wsb.c "j" + 1, Wsb.c "rof"] ++ Wsb.vec "rout" 16, send := true }] := by
  decide
theorem wsb_tr_dr : Wsb.interactions.filter (fun i => decide (i.bus = B_TCH ∧ i.send = false)) =
    [{ bus := B_TCH, mult := [gw], msg := [Wsb.c "j", Wsb.c "rif"] ++ Wsb.vec "rin" 16, send := false }] := by
  decide

theorem wsbR_g₂ : wsbR.g₂ = gw := rfl
theorem wsbR_d₂ : wsbR.d₂ = [K W_FINAL + Wsb.c "i", 0, Wsb.c "rif"] ++ Wsb.vec "rin" 16 ++
    [Wsb.c "kid", 2 - Wsb.c "cp", Wsb.c "cl"] ++ Wsb.vec "cv" 16 := by decide
theorem wsbR_u₂ : wsbR.u₂ = [K W_FINAL + Wsb.c "i", 0, Wsb.c "rk", Wsb.c "rof"] ++ Wsb.vec "rout" 16 ++
    Wsb.vec "rnm" 4 ++ Wsb.vec "rom" 4 ++ [0, 0, 0] ++ List.replicate 16 0 ++ [0] := by decide

section
variable {tr : Trace Fp} {pub : List Fp}

theorem m_first_j (D : Nat) : Expr.isFirst * Wsb.c "j" ∈ Wsb.constraints D := by
  unfold Wsb.constraints; simp
theorem m_tr_j (D : Nat) : Expr.isTransition * (Wsb.nx "j" - Wsb.c "j" - Wsb.c "ph" * Wsb.c "wr") ∈
    Wsb.constraints D := by unfold Wsb.constraints; simp
theorem m_bool_wr (D : Nat) : bool (Wsb.c "wr") ∈ Wsb.constraints D := by unfold Wsb.constraints; simp
theorem m_bool_ph (D : Nat) : bool (Wsb.c "ph") ∈ Wsb.constraints D := by unfold Wsb.constraints; simp
theorem m_rk (D : Nat) : Wsb.c "ph" * Wsb.c "wr" * (Wsb.c "rk" - K RK_H) * (Wsb.c "rk" - K RK_HB) *
    (Wsb.c "rk" - K RK_HE) * (Wsb.c "rk" - K RK_SAME) ∈ Wsb.constraints D := by
  unfold Wsb.constraints; simp

/-- `gw` is a bit. -/
theorem gw_bit {D t r : Nat} (hc : ∀ e ∈ (Wsb.table D).constraints, e.eval tr t r pub = 0) :
    (ev tr t r pub gw = 1 ∧ gw.eval tr t r pub = 1) ∨ (ev tr t r pub gw = 0 ∧ ¬ gw.eval tr t r pub = 1) := by
  have hp := ev_bool (hold rfl hc (m_bool_ph D))
  have hw := ev_bool (hold rfl hc (m_bool_wr D))
  have e : ev tr t r pub gw = ev tr t r pub (Wsb.c "ph") * ev tr t r pub (Wsb.c "wr") % P := ev_hmul _ _
  have hz : ev tr t r pub (Wsb.c "ph") = 0 ∨ ev tr t r pub (Wsb.c "wr") = 0 →
      ev tr t r pub gw = 0 ∧ ¬ gw.eval tr t r pub = 1 := by
    intro h0
    have e' : ev tr t r pub gw = 0 := by rcases h0 with h0 | h0 <;> rw [e, h0] <;> simp
    exact ⟨e', fun h => by have := eval_one_ev h; omega⟩
  rcases hp with hp | hp
  · exact .inr (hz (.inl hp))
  rcases hw with hw | hw
  · exact .inr (hz (.inr hw))
  have e' : ev tr t r pub gw = 1 := by rw [e, hp, hw]
  exact .inl ⟨e', ev_one_eval e'⟩

/-- **The `WSB` `j` column counts the writing rows before the row.** -/
theorem wsb_j {D t : Nat} (hc : ∀ r, r < tr.height t → ∀ e ∈ (Wsb.table D).constraints, e.eval tr t r pub = 0)
    (hlog : tr.log t ≤ 20) : ∀ r, r < tr.height t →
      ev tr t r pub (Wsb.c "j") =
        ((List.range r).filter fun r' => decide (gw.eval tr t r' pub = 1)).length := by
  have hH : tr.height t ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hlog
  intro r
  induction r with
  | zero =>
    intro h0
    have g : ev tr t 0 pub .isFirst = 1 := by rw [FieldWsb.ev_isFirst]; rfl
    rw [FieldWsb.wsb_gate g (hold rfl (hc 0 h0) (m_first_j D))]
    rfl
  | succ r ih =>
    intro hr
    have hr' : r < tr.height t := by omega
    have g : ev tr t r pub .isTransition = 1 := by
      rw [FieldWsb.ev_isTransition]; split
      · omega
      · rfl
    have e := sub_val (eq_of_sub (FieldWsb.wsb_gate g (hold rfl (hc r hr') (m_tr_j D))))
    rw [FieldWsb.wsb_nx _ _ hr] at e
    have ih' := ih hr'
    have hlen : ((List.range r).filter fun r' => decide (gw.eval tr t r' pub = 1)).length ≤ r :=
      Nat.le_trans (List.length_filter_le _ _) (by simp)
    rw [List.range_succ, List.filter_append, List.length_append]
    change ev tr t (r + 1) pub (Wsb.c "j") = _ at e
    rw [e, ih']
    change (_ + ev tr t r pub gw) % P = _
    rcases gw_bit (hc r hr') with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, Nat.mod_eq_of_lt (by omega)]; simp [h2]
    · rw [h1, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]; simp [h2]

end

/-! ## `hT` from `Holds` -/

/-- The input ref of writing row `k` (`TCH` receive, `FINAL` `DOWN`). -/
def aRef (tr : Trace Fp) (pub : List Fp) (k : Nat) : Ref :=
  refDec (vals tr 5 ((wrRows tr pub).getD k 0) pub ([Wsb.c "rif"] ++ Wsb.vec "rin" 16))

/-- The output ref of writing row `k` (`TCH` send, `FINAL` `UP`). -/
def bRef (tr : Trace Fp) (pub : List Fp) (k : Nat) : Ref :=
  refDec (vals tr 5 ((wrRows tr pub).getD k 0) pub ([Wsb.c "rof"] ++ Wsb.vec "rout" 16))

section
variable {tr : Trace Fp} {pub : List Fp}

theorem wsb_hc {D : Nat} {extra : List Table} {nb np : Nat} (hH : Holds (fullAir D extra nb np) pub tr) :
    ∀ r, r < tr.height 5 → ∀ e ∈ (Wsb.table D).constraints, e.eval tr 5 r pub = 0 :=
  fun r hr => hH.constr 5 (by rw [fullAir_len]; omega) r hr

theorem wsb_log {D : Nat} {extra : List Table} {nb np : Nat} (hH : Holds (fullAir D extra nb np) pub tr) :
    tr.log 5 ≤ 20 := (hH.logBound 5 (by rw [fullAir_len]; omega)).2

theorem const_vals (l : List Nat) (hl : ∀ x ∈ l, x < P) (t r : Nat) :
    (l.map fun c => (Expr.const c).eval tr t r pub).map Fp.toNat = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.cons.injEq]
    refine ⟨?_, ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))⟩
    change ev tr t r pub (.const x) = x
    rw [ev_const, Nat.mod_eq_of_lt (hl x (List.mem_cons_self ..))]

/-- The tape's `TCH` end, decoded. -/
theorem tdec_end (j : Nat) (hj : j < P) (x : Bytes) (hx : x.length = 32) (t : Nat) :
    tdec (([j, 0] ++ pairs x).map fun c => (Expr.const c).eval tr t 0 pub) = (j, .dig x) := by
  have hp : (pairs x).length = 16 := by rw [pairs_length, hx]
  have hv := const_vals (tr := tr) (pub := pub) (pairs x) (fun y hy => by have := pairs_lt x y hy; omega) t 0
  simp only [tdec, refDec, List.cons_append, List.nil_append, List.map_cons, List.getD_cons_zero,
    List.drop_succ_cons, List.drop_zero]
  rw [List.take_of_length_le (by simp [hp]), hv]
  have e0 : ((Expr.const j).eval tr t 0 pub).toNat = j := by
    change ev tr t 0 pub (.const j) = j
    rw [ev_const, Nat.mod_eq_of_lt hj]
  have e1 : ((Expr.const 0).eval tr t 0 pub).toNat = 0 := by
    change ev tr t 0 pub (.const 0) = 0
    rw [ev_const]
  rw [e0, e1, if_pos rfl, limbBytes_pairs x (by omega)]

/-- **`hT` from `Holds`**: the `TCH` permutation `bus_batched_changes` takes. -/
theorem tch_perm {D : Nat} (writes : List (List Nat)) (prev post : Bytes) (n : Nat) (rest : List Table)
    {nb np : Nat} (hH : Holds (fullAir D (tapeTable (m5aTape writes prev post n) :: rest) nb np) pub tr)
    (hr : ∀ T ∈ rest, ∀ i ∈ T.interactions, i.bus ≠ B_TCH) (hn : n < P) (hprev : prev.length = 32)
    (hpost : post.length = 32) :
    (tchSends (Ref.dig prev) (wrRows tr pub).length (bRef tr pub)).Perm
      (tchRecvs (Ref.dig post) n (wrRows tr pub).length (aRef tr pub)) := by
  have hc := wsb_hc hH
  have hlog := wsb_log hH
  have hH20 : tr.height 5 ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hlog
  have hp0 := holds_perm hH B_TCH
  rw [busList_tch D _ rest nb np hr, busList_tch D _ rest nb np hr,
    tableBusList_one _ _ _ tr 5 pub _ _ wsb_tr_ds, tableBusList_one _ _ _ tr 5 pub _ _ wsb_tr_dr] at hp0
  have ts : tapeMsgs tr 12 pub (m5aTape writes prev post n) B_TCH true =
      [([0, 0] ++ pairs prev).map fun c => (Expr.const c).eval tr 12 0 pub] := by
    simp [tapeMsgs, m5aTape, B_WRITE, B_TCH]
  have tr' : tapeMsgs tr 12 pub (m5aTape writes prev post n) B_TCH false =
      [([n, 0] ++ pairs post).map fun c => (Expr.const c).eval tr 12 0 pub] := by
    simp [tapeMsgs, m5aTape, B_WRITE, B_TCH]
  rw [ts, tr', filterMap_ite, filterMap_ite] at hp0
  have hp := hp0.map tdec
  rw [List.map_append (f := tdec), List.map_append (f := tdec), List.map_map (g := tdec),
    List.map_map (g := tdec), List.map_cons (f := tdec), List.map_nil (f := tdec), List.map_cons (f := tdec),
    tdec_end 0 (by decide) prev hprev, tdec_end n hn post hpost] at hp
  -- the `WSB` sides, by rank
  have hj := wsb_j hc hlog
  have hS : ((List.range (tr.height 5)).filter fun r => decide (gw.eval tr 5 r pub = 1)).map
      (tdec ∘ fun r => ([Wsb.c "j" + 1, Wsb.c "rof"] ++ Wsb.vec "rout" 16).map fun e => e.eval tr 5 r pub) =
      (List.range (wrRows tr pub).length).map fun k => (k + 1, bRef tr pub k) := by
    have := filter_rank (fun r => decide (gw.eval tr 5 r pub = 1))
      (fun r => refDec (vals tr 5 r pub ([Wsb.c "rof"] ++ Wsb.vec "rout" 16)))
      (fun r => ev tr 5 r pub (Wsb.c "j" + 1)) 1 (tr.height 5) (fun r hr' _ => by
        have h1 := hj r hr'
        have : ((List.range r).filter fun r' => decide (gw.eval tr 5 r' pub = 1)).length ≤ r :=
          Nat.le_trans (List.length_filter_le _ _) (by simp)
        rw [ev_hadd, ev_one, h1, Nat.mod_eq_of_lt (by omega)])
    refine Eq.trans ?_ this
    apply List.map_congr_left
    intro r _
    rfl
  have hR : ((List.range (tr.height 5)).filter fun r => decide (gw.eval tr 5 r pub = 1)).map
      (tdec ∘ fun r => ([Wsb.c "j", Wsb.c "rif"] ++ Wsb.vec "rin" 16).map fun e => e.eval tr 5 r pub) =
      (List.range (wrRows tr pub).length).map fun k => (k, aRef tr pub k) := by
    have := filter_rank (fun r => decide (gw.eval tr 5 r pub = 1))
      (fun r => refDec (vals tr 5 r pub ([Wsb.c "rif"] ++ Wsb.vec "rin" 16)))
      (fun r => ev tr 5 r pub (Wsb.c "j")) 0 (tr.height 5) (fun r hr' _ => hj r hr')
    refine Eq.trans ?_ this
    apply List.map_congr_left
    intro r _
    rfl
  rw [hS, hR] at hp
  exact (List.perm_append_singleton _ _).symm.trans (hp.trans (List.perm_append_singleton _ _))

end

/-! ## `hroot` from `Holds` -/

/-- A committed change's value against a writing row's `(cp, cl, cv)`. -/
def ValOK (cp cl : Nat) (vh : Bytes) : Option Bytes → Prop
  | some x => cp = 1 ∧ cl = x.length ∧ vh = sha256 x
  | none => cp = 0

/-- Field `s` of writing row `k`. -/
def wf (tr : Trace Fp) (pub : List Fp) (k : Nat) (s : String) : Nat :=
  ev tr 5 ((wrRows tr pub).getD k 0) pub (Wsb.c s)

/-- The value digest of writing row `k` (`cv`, 16 limbs). -/
def wcv (tr : Trace Fp) (pub : List Fp) (k : Nat) : Bytes :=
  limbBytes ((vals tr 5 ((wrRows tr pub).getD k 0) pub (Wsb.vec "cv" 16)).map Fp.toNat)

/-- **The committed changes match the writing rows** (the remaining premise on `cs`): change `k`
has the `KEY` table's bytes of the row's key id, and the value the row's `(cp, cl, cv)` commits
to (present with that length and SHA-256, or absent). -/
def FinalChanges (tr : Trace Fp) (pub : List Fp) (cs : List (Bytes × Option Bytes)) : Prop :=
  ∀ k (hk : k < cs.length), k < (wrRows tr pub).length →
    cs[k].1 = keyBytes tr (wf tr pub k "kid") ∧ ValOK (wf tr pub k "cp") (wf tr pub k "cl") (wcv tr pub k) cs[k].2

section
variable {tr : Trace Fp} {pub : List Fp}

theorem vals_append (t r : Nat) (l₁ l₂ : List Expr) :
    vals tr t r pub (l₁ ++ l₂) = vals tr t r pub l₁ ++ vals tr t r pub l₂ := List.map_append

theorem vals_vec_len (t r : Nat) (s : String) (n : Nat) : (vals tr t r pub (Wsb.vec s n)).length = n := by
  simp [vals, Wsb.vec]

theorem mem_walkRoots {Ref' Pay' Res' : Type} (Dc : Dec Ref' Pay' Res') {r : Nat} (hr : r < tr.height 5)
    (hg : gw.eval tr 5 r pub = 1) :
    { dn := Dc.down (vals tr 5 r pub wsbR.d₂), res := Dc.dr ((vals tr 5 r pub wsbR.u₂).drop 2) } ∈
      walkRoots Dc tr pub := by
  simp only [walkRoots, rootsOf, List.mem_flatMap, List.mem_range]
  refine ⟨r, hr, ?_⟩
  simp only [rootRow, List.mem_append]
  right
  rw [if_pos (by rw [wsbR_g₂]; exact hg)]
  exact List.mem_singleton_self _

theorem rk_ref {D r : Nat} (hc : ∀ e ∈ (Wsb.table D).constraints, e.eval tr 5 r pub = 0)
    (hg : ev tr 5 r pub gw = 1) : RefKind (ev tr 5 r pub (Wsb.c "rk")) := by
  have e := hold rfl hc (m_rk D)
  have hlt := ev_lt (tr := tr) (t := 5) (r := r) (pub := pub) (Wsb.c "rk")
  have fac : ∀ c : Nat, c < P → ev tr 5 r pub (Wsb.c "rk" - K c) = 0 → ev tr 5 r pub (Wsb.c "rk") = c := by
    intro c hc0 h
    rw [eq_of_sub h, show K c = Expr.const c from rfl, ev_const, Nat.mod_eq_of_lt hc0]
  rcases ev_mul_eq_zero e with e | e
  · rcases ev_mul_eq_zero e with e | e
    · rcases ev_mul_eq_zero e with e | e
      · rcases ev_mul_eq_zero e with e | e
        · exact absurd (show ev tr 5 r pub gw = 0 from e) (by omega)
        · exact .inl (fac _ (by decide) e)
      · exact .inr (.inl (fac _ (by decide) e))
    · exact .inr (.inr (.inl (fac _ (by decide) e)))
  · exact .inr (.inr (.inr (fac _ (by decide) e)))

theorem mode_val {r : Nat} (cp : Nat) (h : ev tr 5 r pub (Wsb.c "cp") = cp) (hcp : cp = 0 ∨ cp = 1) :
    ev tr 5 r pub (2 - Wsb.c "cp") = 2 - cp := by
  rw [ev_sub, h, show (2 : Expr) = Expr.const 2 from rfl, ev_const]
  rcases hcp with rfl | rfl <;> rfl

/-- **`hroot` from `Holds`**: writing row `k` is a `FINAL` root at depth `0` with input ref
`a k`, output ref `b k`, the payload of change `cs[k]` and (for a delete) a ref result kind. -/
theorem root_of_row {D : Nat} {extra : List Table} {nb np : Nat} (hH : Holds (fullAir D extra nb np) pub tr)
    (Dc : Dec Ref Pay Res) (hDc : StdDec Dc) (cs : List (Bytes × Option Bytes))
    (hcs : FinalChanges tr pub cs) :
    ∀ j (hj : j < (wrRows tr pub).length), ∃ q ∈ walkRoots Dc tr pub, q.dn.ref = aRef tr pub j ∧
      q.res.ref = bRef tr pub j ∧ q.dn.d = 0 ∧
      ∀ (hj' : j < cs.length), PayOf (keyOf tr) q.dn.pay cs[j] ∧ (cs[j].2 = none → RefKind q.res.rk) := by
  intro j hj
  have hc := wsb_hc hH
  have hmem : (wrRows tr pub).getD j 0 ∈ wrRows tr pub := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    exact List.getElem_mem hj
  generalize hrr : (wrRows tr pub).getD j 0 = r at hmem
  obtain ⟨hr, hg⟩ := List.mem_filter.1 hmem
  have hr := List.mem_range.1 hr
  have hg : gw.eval tr 5 r pub = 1 := of_decide_eq_true hg
  refine ⟨_, mem_walkRoots Dc hr hg, ?_, ?_, ?_, ?_⟩
  · simp only [Dec.down, hDc.ref, aRef, hrr, wsbR_d₂, vals_append, List.append_assoc]
    rw [show vals tr 5 r pub [K W_FINAL + Wsb.c "i", 0, Wsb.c "rif"] =
      [(K W_FINAL + Wsb.c "i").eval tr 5 r pub, (0 : Expr).eval tr 5 r pub] ++ vals tr 5 r pub [Wsb.c "rif"]
      from rfl]
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero]
    rw [show vals tr 5 r pub [Wsb.c "rif"] = [(Wsb.c "rif").eval tr 5 r pub] from rfl]
    simp only [List.cons_append, List.nil_append]
    rw [← List.cons_append, refDec_append _ _ _ (vals_vec_len 5 r "rin" 16)]
  · simp only [hDc.rref, bRef, hrr, wsbR_u₂, vals_append, List.append_assoc]
    rw [show vals tr 5 r pub [K W_FINAL + Wsb.c "i", 0, Wsb.c "rk", Wsb.c "rof"] =
      [(K W_FINAL + Wsb.c "i").eval tr 5 r pub, (0 : Expr).eval tr 5 r pub, (Wsb.c "rk").eval tr 5 r pub] ++
        vals tr 5 r pub [Wsb.c "rof"] from rfl]
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero]
    rw [show vals tr 5 r pub [Wsb.c "rof"] = [(Wsb.c "rof").eval tr 5 r pub] from rfl]
    simp only [List.cons_append, List.nil_append]
    rw [← List.cons_append, refDec_append _ _ _ (vals_vec_len 5 r "rout" 16)]
  · simp only [Dec.down, wsbR_d₂]
    rfl
  · intro hj'
    obtain ⟨hkey, hval⟩ := hcs j hj' hj
    simp only [wf, wcv, hrr] at hkey hval
    have hm : (vals tr 5 r pub wsbR.d₂).drop 2 = vals tr 5 r pub ([Wsb.c "rif"] ++ Wsb.vec "rin" 16 ++
        [Wsb.c "kid", 2 - Wsb.c "cp", Wsb.c "cl"]) ++ vals tr 5 r pub (Wsb.vec "cv" 16) := by
      rw [wsbR_d₂]; rfl
    have hA : (vals tr 5 r pub ([Wsb.c "rif"] ++ Wsb.vec "rin" 16 ++
        [Wsb.c "kid", 2 - Wsb.c "cp", Wsb.c "cl"])).length = 20 := by simp [vals, Wsb.vec]
    have g17 : ((vals tr 5 r pub wsbR.d₂).drop 2).getD 17 0 = (Wsb.c "kid").eval tr 5 r pub := by
      rw [hm]; rfl
    have g18 : ((vals tr 5 r pub wsbR.d₂).drop 2).getD 18 0 = (2 - Wsb.c "cp").eval tr 5 r pub := by
      rw [hm]; rfl
    have g19 : ((vals tr 5 r pub wsbR.d₂).drop 2).getD 19 0 = (Wsb.c "cl").eval tr 5 r pub := by
      rw [hm]; rfl
    have g20 : (((vals tr 5 r pub wsbR.d₂).drop 2).drop 20).take 16 = vals tr 5 r pub (Wsb.vec "cv" 16) := by
      rw [hm, List.drop_left' hA, List.take_of_length_le (by simp [vals, Wsb.vec])]
    have hu : ((vals tr 5 r pub wsbR.u₂).drop 2).getD 0 0 = (Wsb.c "rk").eval tr 5 r pub := by
      rw [wsbR_u₂]; rfl
    refine ⟨?_, fun _ => ?_⟩
    · simp only [Dec.down]
      generalize hcj : cs[j] = ch at hkey hval
      obtain ⟨k, v⟩ := ch
      simp only at hkey hval
      cases v with
      | some x =>
        obtain ⟨h1, h2, h3⟩ := hval
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hDc.kid, g17, hkey, ← keyOf_eq_nibbles (key_hc hH)]
          rfl
        · rw [hDc.mode, g18]
          exact mode_val 1 h1 (.inr rfl)
        · rw [hDc.vlen, g19]; exact h2
        · rw [hDc.vh, g20]; exact h3
      | none =>
        refine ⟨?_, ?_⟩
        · rw [hDc.kid, g17, hkey, ← keyOf_eq_nibbles (key_hc hH)]
          rfl
        · rw [hDc.mode, g18]
          exact mode_val 0 hval (.inl rfl)
    · simp only
      rw [hDc.rk, hu]
      exact rk_ref (hc r hr) (eval_one_ev hg)

end

/-! ## The assembly -/

theorem tape_bus (writes : List (List Nat)) (prev post : Bytes) (n : Nat) :
    ∀ i ∈ (tapeTable (m5aTape writes prev post n)).interactions, i.bus = B_WRITE ∨ i.bus = B_TCH := by
  intro i hi
  simp only [tapeTable, List.mem_map] at hi
  obtain ⟨e, he, rfl⟩ := hi
  simp only [m5aTape, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with ⟨w, -, rfl⟩ | rfl | rfl
  · exact .inl rfl
  · exact .inr rfl
  · exact .inr rfl

section
variable {tr : Trace Fp} {pub : List Fp}

open NearSpecV3.D2 in
/-- **Batched FINAL from `Holds` of the AIR the prover runs, with the public tape.**  For the AIR
`fullAir D (tapeTable (m5aTape writes prev post n) :: rest)` (the Lean AIR, the public tape, and
tables `rest` — the SHA-512 chip — that use neither `DOWN`, `UP` nor `TCH` and send nothing on
`NIB`), any decoder with the standard ref / payload layout (`StdDec`), and any list of changes
`cs` of length `n` matching the writing `WSB` rows (`FinalChanges`): on a revealed, well-formed
witness trie with root hash `prev`, the spec's `applyChanges` succeeds and its `rootHash` is
`post`.  The `TCH` chain (`hT`), the writing roots (`hroot`) and the depth bounds (`hbr`, `hsn`)
are discharged; what remains: `Sha256CR`, the per-row `LocalOK` (`hloc`), `SncDeeper` (continued
extension keys) and `FinalChanges` (`cs` against the working set / write tape). -/
theorem air_final (hCR : Walk.Sha256CR) (σ : Store) (Dc : Dec Ref Pay Res) (hDc : StdDec Dc) (D : Nat)
    (writes : List (List Nat)) (prev post : Bytes) (n : Nat) (rest : List Table) (nb np : Nat)
    (hH : Holds (fullAir D (tapeTable (m5aTape writes prev post n) :: rest) nb np) pub tr) (hD : D ≤ 30)
    (hr : ∀ T ∈ rest, ∀ i ∈ T.interactions, i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP ∧ i.bus ≠ B_TCH)
    (hrN : ∀ T ∈ rest, sendsOn T.interactions B_NIB = false)
    (hn : n < P) (hprev : prev.length = 32) (hpost : post.length = 32)
    (hsc : SncDeeper tr pub)
    (hloc : ∀ r ∈ walkRows Dc tr pub, LocalOK (SemS σ (keyOf tr)) r)
    (cs : List (Bytes × Option Bytes)) (hlen : cs.length = n) (hcs : FinalChanges tr pub cs)
    (T : PTrie) (hT0 : T.hashOf = prev) (hF : Full T ∧ T.wf = true) :
    ∃ T', applyChanges (some T) cs = some (some T') ∧ rootHash (some T') = post := by
  have hx : ∀ T ∈ tapeTable (m5aTape writes prev post n) :: rest, ∀ i ∈ T.interactions,
      i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP := by
    intro T hT i hi
    rcases List.mem_cons.1 hT with rfl | hT
    · rcases tape_bus writes prev post n i hi with h | h <;> rw [h] <;> exact ⟨by decide, by decide⟩
    · exact ⟨(hr T hT i hi).1, (hr T hT i hi).2.1⟩
  have hxN : ∀ T ∈ tapeTable (m5aTape writes prev post n) :: rest, sendsOn T.interactions B_NIB = false := by
    intro T hT
    rcases List.mem_cons.1 hT with rfl | hT
    · apply List.any_eq_false.2
      intro i hi
      rcases tape_bus writes prev post n i hi with h | h <;> simp [h, B_WRITE, B_TCH, B_NIB]
    · exact hrN T hT
  have hT := tch_perm writes prev post n rest hH (fun T hT i hi => (hr T hT i hi).2.2) hn hprev hpost
  rw [← hlen] at hT
  exact air_batched_changesS' hCR σ (keyOf tr) Dc D _ nb np hH hD hx hxN hsc hloc cs prev post _
    (aRef tr pub) (bRef tr pub) hT (root_of_row hH Dc hDc cs hcs) T hT0 hF

end

end StateM5a.Tape
