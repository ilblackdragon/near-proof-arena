import StateM5a.BrMat
import StateM5a.SnDepthAll

/-!
# StateM5a.WalkEnd — the last row of a walk, and `BrMat.OslApart` from `Holds`

* **`terminal_deepest`** (`Traffic` level): with the walk shape and `DOWN` balance, a row that does
  not descend is the deepest row of its walk.  The open `DOWN` edges crossing depth `d`
  (`cross`, `≤ 1`) do not increase with `d`; at a non-descending row's depth `d₁` the one edge
  ends, so no edge crosses `d₁ + 1` and no row of the walk receives a `DOWN` below `d₁`.
* **Decoded rows** (`Holds`): `sn_term_unique` — two non-descending active `SN` rows of the same
  walk are the same row (same depth by `terminal_deepest`, then one row per walk position);
  `br_above_term` — an active `BR` row of the walk of a non-descending `SN` row is strictly above
  it (`≤` by `terminal_deepest`, `≠` because both would receive a `DOWN` at one walk position).
* **`oslApart`**: a split's new branch (`BR.oSL`) received its `SPQ(w, d + jm, …)` from an `SN`
  split row (`oLX`/`oEX`, the only `SPQ` sender), which is a non-descending walk row at depth `d`;
  an active `BR` row at `(w, d + jm)` would be strictly above it.  So `BrMat.OslApart` holds.
-/

namespace StateM5a.WalkEnd

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.KcChain StateM5a.KeyDecode
open StateM5a.RowSn StateM5a.RowSnMsg StateM5a.BrSib StateM5a.BrMat

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## The deepest row of a walk (`Traffic` level) -/

section
variable {Ref Pay Res : Type} {roots : List (Root Ref Pay Res)} {rows : List (WRow Ref Pay Res)}

theorem sendAt_le_cross (hs : WalkShape roots rows) (w d : Nat) :
    sendAt roots rows w d ≤ cross roots rows w d := by
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

theorem sendAt_eq_recvAt (hbal : (downSends roots rows).Perm (downRecvs rows)) (w d : Nat) :
    sendAt roots rows w d = recvAt rows w d := by
  rw [← sendAt_eq, ← recvAt_eq]; exact hbal.countP_eq _

theorem cross_succ_le (hs : WalkShape roots rows) (hbal : (downSends roots rows).Perm (downRecvs rows))
    (w d : Nat) : cross roots rows w (d + 1) ≤ cross roots rows w d := by
  have hstep := cross_step roots rows hs w d
  have hsr := sendAt_eq_recvAt hbal w d
  have := descAt_le roots rows hs w d
  omega

theorem cross_zero_add (hs : WalkShape roots rows) (hbal : (downSends roots rows).Perm (downRecvs rows))
    {w d₀ : Nat} (h0 : cross roots rows w d₀ = 0) : ∀ n, cross roots rows w (d₀ + n) = 0
  | 0 => h0
  | n + 1 => by
    have := cross_succ_le hs hbal w (d₀ + n)
    have := cross_zero_add hs hbal h0 n
    rw [← Nat.add_assoc]; omega

theorem one_le_recvAt {r : WRow Ref Pay Res} (hr : r ∈ rows) : 1 ≤ recvAt rows r.din.w r.din.d :=
  List.countP_pos_iff.2 ⟨r, hr, by simp⟩

/-- **A row that does not descend is the deepest row of its walk.** -/
theorem terminal_deepest (hs : WalkShape roots rows) (hbal : (downSends roots rows).Perm (downRecvs rows))
    {r₁ r₂ : WRow Ref Pay Res} (h₁ : r₁ ∈ rows) (hdo : r₁.dout = none) (h₂ : r₂ ∈ rows)
    (hw : r₂.din.w = r₁.din.w) : r₂.din.d ≤ r₁.din.d := by
  refine Nat.le_of_not_lt fun hlt => ?_
  have hdesc : descAt rows r₁.din.w r₁.din.d = 0 := by
    unfold descAt
    rw [List.countP_eq_zero]
    intro r hr
    cases hc : r.dout with
    | none => simp
    | some c =>
      simp only [decide_eq_true_eq, not_and]
      intro hcw hd
      have e := walk_unique' hs hbal hr h₁ (by rw [← (hs.deeper r hr c hc).1, hcw]) hd
      subst e
      rw [hdo] at hc; cases hc
  have hstep := cross_step roots rows hs r₁.din.w r₁.din.d
  have hsr := sendAt_eq_recvAt hbal r₁.din.w r₁.din.d
  have hle := cross_le_one roots rows hs hbal r₁.din.w r₁.din.d
  have h1 := one_le_recvAt h₁
  have hz : cross roots rows r₁.din.w (r₁.din.d + 1) = 0 := by omega
  have hz2 := cross_zero_add hs hbal hz (r₂.din.d - (r₁.din.d + 1))
  rw [show r₁.din.d + 1 + (r₂.din.d - (r₁.din.d + 1)) = r₂.din.d by omega] at hz2
  have h2 := one_le_recvAt h₂
  rw [hw] at h2
  have := sendAt_le_cross hs r₁.din.w r₂.din.d
  have := sendAt_eq_recvAt hbal r₁.din.w r₂.din.d
  omega

end

/-! ## Decoded rows -/

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

theorem snRow_mem {s : Nat} (hs : s < tr.height 3) (hg : snW.g.eval tr 3 s pub = 1) :
    snRow tr pub s ∈ rowsOf cDc snW tr 3 pub := by
  unfold rowsOf
  exact List.mem_filterMap.2 ⟨s, List.mem_range.2 hs, by rw [if_pos hg]; rfl⟩

theorem brRow_mem {r : Nat} (hr : r < tr.height 2) (hg : Br.gold.eval tr 2 r pub = 1) :
    RowBrF.brRow tr pub r ∈ rowsOf cDc brW tr 2 pub := by
  unfold rowsOf
  exact List.mem_filterMap.2 ⟨r, List.mem_range.2 hr, by rw [if_pos (show brW.g.eval tr 2 r pub = 1 from hg)]; rfl⟩

theorem snRow_dout {s : Nat} (h0 : ev tr 3 s pub (Sn.c "gdn") = 0) : (snRow tr pub s).dout = none := by
  simp only [snRow]
  rw [if_neg]
  intro h
  have := eval_one_ev (e := Sn.c "gdn") h
  omega

theorem snRow_din_w {s : Nat} : (snRow tr pub s).din.w = ev tr 3 s pub (Sn.c "w") := by
  simp only [snRow]; rw [sn_din]
theorem snRow_din_d {s : Nat} : (snRow tr pub s).din.d = ev tr 3 s pub (Sn.c "d") := by
  simp only [snRow]; rw [sn_din]
theorem brRow_din_w {r : Nat} : (RowBrF.brRow tr pub r).din.w = ev tr 2 r pub (Br.c "w") := by
  simp only [RowBrF.brRow]; rw [br_din]
theorem brRow_din_d {r : Nat} : (RowBrF.brRow tr pub r).din.d = ev tr 2 r pub (Br.c "d") := by
  simp only [RowBrF.brRow]; rw [br_din]

section
variable (hH : Holds (fullAir D extra nb np) pub tr) (hD : D ≤ 30)
  (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP)
  (hxN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
  (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
  (hxR : ∀ T ∈ extra, sendsOn T.interactions B_KCR = false)
include hH hD hx hxN hxK hxR

theorem walk_ok : WalkShape (walkRoots cDc tr pub) (walkRows cDc tr pub) ∧
    (downSends (walkRoots cDc tr pub) (walkRows cDc tr pub)).Perm (downRecvs (walkRows cDc tr pub)) :=
  ⟨DepthBound.walk_shape' cDc D extra nb np hH hD hxN (sncDeeper hH hxN hxK hxR),
    (walk_traffic cDc D extra nb np hH hx).1⟩

/-- Two active `SN` rows never sit at the same walk position. -/
theorem sn_row_unique {s s' : Nat} (hs : s < tr.height 3) (hs' : s' < tr.height 3)
    (hg : snW.g.eval tr 3 s pub = 1) (hg' : snW.g.eval tr 3 s' pub = 1)
    (hw : ev tr 3 s pub (Sn.c "w") = ev tr 3 s' pub (Sn.c "w"))
    (hd : ev tr 3 s pub (Sn.c "d") = ev tr 3 s' pub (Sn.c "d")) : s = s' := by
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨hsh, hbal⟩ := walk_ok hH hD hx hxN hxK hxR
  have hU := walk_unique _ _ hsh hbal (ev tr 3 s pub (Sn.c "w")) (ev tr 3 s pub (Sn.c "d"))
  have h2 : 2 ≤ (rowsOf cDc snW tr 3 pub).countP (fun q => decide (q.din.w = ev tr 3 s pub (Sn.c "w") ∧
      q.din.d = ev tr 3 s pub (Sn.c "d"))) := by
    unfold rowsOf
    refine two_le_countP (r := s) (r' := s') (if_pos hg) ?_ (if_pos hg') ?_ hne
      List.nodup_range (List.mem_range.2 hs) (List.mem_range.2 hs')
    · simp only [sn_din]; simp
    · simp only [sn_din]; simp [hw, hd]
  have : recvAt (walkRows cDc tr pub) (ev tr 3 s pub (Sn.c "w")) (ev tr 3 s pub (Sn.c "d")) ≥ 2 := by
    unfold recvAt walkRows; rw [List.countP_append]; omega
  omega

/-- An active `BR` row and an active `SN` row never sit at the same walk position. -/
theorem br_sn_apart {r s : Nat} (hr : r < tr.height 2) (hs : s < tr.height 3)
    (hg : Br.gold.eval tr 2 r pub = 1) (hg' : snW.g.eval tr 3 s pub = 1)
    (hw : ev tr 2 r pub (Br.c "w") = ev tr 3 s pub (Sn.c "w"))
    (hd : ev tr 2 r pub (Br.c "d") = ev tr 3 s pub (Sn.c "d")) : False := by
  obtain ⟨hsh, hbal⟩ := walk_ok hH hD hx hxN hxK hxR
  have hU := walk_unique _ _ hsh hbal (ev tr 2 r pub (Br.c "w")) (ev tr 2 r pub (Br.c "d"))
  have h1 : 1 ≤ (rowsOf cDc brW tr 2 pub).countP (fun q => decide (q.din.w = ev tr 2 r pub (Br.c "w") ∧
      q.din.d = ev tr 2 r pub (Br.c "d"))) :=
    List.countP_pos_iff.2 ⟨_, brRow_mem hr hg, by simp [brRow_din_w, brRow_din_d]⟩
  have h2 : 1 ≤ (rowsOf cDc snW tr 3 pub).countP (fun q => decide (q.din.w = ev tr 2 r pub (Br.c "w") ∧
      q.din.d = ev tr 2 r pub (Br.c "d"))) :=
    List.countP_pos_iff.2 ⟨_, snRow_mem hs hg', by simp [snRow_din_w, snRow_din_d, hw, hd]⟩
  have : recvAt (walkRows cDc tr pub) (ev tr 2 r pub (Br.c "w")) (ev tr 2 r pub (Br.c "d")) ≥ 2 := by
    unfold recvAt walkRows; rw [List.countP_append]; omega
  omega

/-- **Two non-descending active `SN` rows of one walk are the same row.** -/
theorem sn_term_unique {s s' : Nat} (hs : s < tr.height 3) (hs' : s' < tr.height 3)
    (hg : snW.g.eval tr 3 s pub = 1) (hg' : snW.g.eval tr 3 s' pub = 1)
    (h0 : ev tr 3 s pub (Sn.c "gdn") = 0) (h0' : ev tr 3 s' pub (Sn.c "gdn") = 0)
    (hw : ev tr 3 s pub (Sn.c "w") = ev tr 3 s' pub (Sn.c "w")) : s = s' := by
  obtain ⟨hsh, hbal⟩ := walk_ok hH hD hx hxN hxK hxR
  have m := List.mem_append_right (rowsOf cDc brW tr 2 pub) (snRow_mem hs hg)
  have m' := List.mem_append_right (rowsOf cDc brW tr 2 pub) (snRow_mem hs' hg')
  have a := terminal_deepest hsh hbal m (snRow_dout h0) m' (by rw [snRow_din_w, snRow_din_w, hw])
  have b := terminal_deepest hsh hbal m' (snRow_dout h0') m (by rw [snRow_din_w, snRow_din_w, hw])
  rw [snRow_din_d, snRow_din_d] at a b
  exact sn_row_unique hH hD hx hxN hxK hxR hs hs' hg hg' hw (by omega)

/-- **An active `BR` row of the walk of a non-descending `SN` row is strictly above it.** -/
theorem br_above_term {r s : Nat} (hr : r < tr.height 2) (hs : s < tr.height 3)
    (hg : Br.gold.eval tr 2 r pub = 1) (hg' : snW.g.eval tr 3 s pub = 1)
    (h0 : ev tr 3 s pub (Sn.c "gdn") = 0)
    (hw : ev tr 2 r pub (Br.c "w") = ev tr 3 s pub (Sn.c "w")) :
    ev tr 2 r pub (Br.c "d") < ev tr 3 s pub (Sn.c "d") := by
  obtain ⟨hsh, hbal⟩ := walk_ok hH hD hx hxN hxK hxR
  have m := List.mem_append_right (rowsOf cDc brW tr 2 pub) (snRow_mem hs hg')
  have m' := List.mem_append_left (rowsOf cDc snW tr 3 pub) (brRow_mem hr hg)
  have a := terminal_deepest hsh hbal m (snRow_dout h0) m' (by rw [snRow_din_w, brRow_din_w, hw])
  rw [snRow_din_d, brRow_din_d] at a
  rcases Nat.lt_or_eq_of_le a with h | h
  · exact h
  · exact (br_sn_apart hH hD hx hxN hxK hxR hr hs hg hg' hw h).elim

end

end

/-! ## `SPQ`: the split request -/

def snSpQ : List Expr :=
  [Sn.c "w", Sn.c "d" + Sn.c "jm", Sn.c "kid", Sn.c "kid2", Sn.c "oLX"] ++
    ((pack2 fun b => Sn.c "x" (4 + b)).zip ((List.range 16).map fun i => Sn.c "xh" i)).map
      (fun (p, q) => Sn.c "oLX" * p + q) ++
    [Sn.c "xhf", Sn.c "oLX" * Sn.vlenOf (fun t => Sn.c "x" t)] ++ ((List.range 4).map fun t => Sn.c "xm" t) ++
    [Sn.c "dvlen"] ++ (List.range 16).map fun i => Sn.c "dvh" i

def brSpQ : List Expr :=
  [Br.c "w", Br.c "d", Br.c "kid", Br.c "xk", Br.c "xl"] ++
    ((List.range 16).zip (pack2 fun b => Br.c "nh2" b)).map
      (fun (i, p) => Br.c "xl" * Br.c "lvh2" i + (1 - Br.c "xl") * p) ++
    [(1 - Br.c "xl") * Br.c "nh2f", Br.c "xl" * Br.c "lvlen2"] ++
    ((List.range 4).map fun k => (1 - Br.c "xl") * Br.c "nm2" k) ++
    [Br.c "dvlen"] ++ (List.range 16).map fun i => Br.c "dvh" i

theorem sn_spq_s : Sn.interactions.filter (fun i => decide (i.bus = B_SPQ ∧ i.send = true)) =
    [snd B_SPQ Sn.gX snSpQ] := by decide
theorem br_spq_r : rcv B_SPQ (Br.c "oSL") brSpQ ∈ Br.interactions := memD_mem (by decide)

theorem spq_only (D : Nat) : ∀ t (ht : t < (m5aAir D).tables.length), t ≠ 3 →
    sendsOn ((m5aAir D).tables[t]).interactions B_SPQ = false
  | 0, _, _ => by show sendsOn shaTable.interactions B_SPQ = false; decide
  | 1, _, _ => by show sendsOn Key.interactions B_SPQ = false; decide
  | 2, _, _ => by show sendsOn Br.interactions B_SPQ = false; decide
  | 3, _, h => absurd rfl h
  | 4, _, _ => by show sendsOn Kcmp.interactions B_SPQ = false; decide
  | 5, _, _ => by show sendsOn Wsb.interactions B_SPQ = false; decide
  | 6, _, _ => by show sendsOn Wsn.interactions B_SPQ = false; decide
  | 7, _, _ => by show sendsOn Wsa.interactions B_SPQ = false; decide
  | 8, _, _ => by show sendsOn Snc.interactions B_SPQ = false; decide
  | 9, _, _ => by show sendsOn Rng.interactions B_SPQ = false; decide
  | 10, _, _ => by show sendsOn Wsl.interactions B_SPQ = false; decide
  | 11, _, _ => by show sendsOn Wsp.interactions B_SPQ = false; decide
  | n + 12, h, _ => absurd h (by simp [m5aAir])

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

open StateM5a.FieldWalk2 in
set_option maxHeartbeats 4000000 in
/-- A split row (`gX = 1`) is an active, non-descending walk row with a mismatch (`gA = 1`). -/
theorem split_flags {s : Nat} (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 s pub = 0)
    (hX : ev tr 3 s pub Sn.gX = 1) :
    ev tr 3 s pub (Sn.c "mF" + Sn.c "mU" + Sn.c "mD") = 1 ∧ ev tr 3 s pub (Sn.c "gdn") = 0 ∧
      ev tr 3 s pub (Sn.c "gA") = 1 ∧ ev tr 3 s pub (Sn.c "oLX") + ev tr 3 s pub (Sn.c "oEX") = 1 := by
  have hb : ∀ s' ∈ snNames, ev tr 3 s pub (Sn.c s') ≤ 1 := fun s' hs => sn_flag_le hc s' hs
  have bX := hb "oLX" (by simp [snNames]); have bE := hb "oEX" (by simp [snNames])
  have hX' : ev tr 3 s pub (Sn.c "oLX") + ev tr 3 s pub (Sn.c "oEX") = 1 := by
    unfold Sn.gX at hX; rw [ev_hadd] at hX
    rcases Nat.lt_or_ge (ev tr 3 s pub (Sn.c "oLX") + ev tr 3 s pub (Sn.c "oEX")) P with h | h
    · rwa [Nat.mod_eq_of_lt h] at hX
    · omega
  have S := fun (s' : String) (l : List String) (h : s' :: l ⊆ snNames) (hl : l.length ≤ 63) =>
    sn_sum hc s' l h hl
  have e3 := S "oLR" ["oEU", "oLX", "oEX"] (by simp [snNames]) (by simp)
  have e0 := S "mF" ["mU", "mD"] (by simp [snNames]) (by simp)
  have e1 := S "mF" ["mU", "mD", "oLS", "oLM", "oEP", "oEM"] (by simp [snNames]) (by simp)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, List.sum_cons, List.sum_nil, sc]
    at e0 e1 e3
  have c1 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_act)
  have c3 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_mU)
  rw [e1] at c1; rw [e3] at c3
  have b0 := hb "act" (by simp [snNames]); have b1 := hb "mF" (by simp [snNames])
  have b2 := hb "mD" (by simp [snNames]); have b2u := hb "mU" (by simp [snNames])
  have b11 := hb "oLS" (by simp [snNames]); have b12 := hb "oLM" (by simp [snNames])
  have b13 := hb "oEP" (by simp [snNames]); have b14 := hb "oEM" (by simp [snNames])
  have hg : ev tr 3 s pub (Sn.c "mF" + Sn.c "mU" + Sn.c "mD") = 1 := by rw [e0]; omega
  clear S e0 e1 e3 c1 c3 b0 b1 b2 b2u b11 b12 b13 b14 hb
  refine ⟨hg, ?_, ?_, hX'⟩
  · snfacts hc hg; omega
  · snfacts hc hg; omega

/-- The `SPQ` a `BR.oSL` row receives was sent by an `SN` split row. -/
theorem osl_spq (hH : Holds (fullAir D extra nb np) pub tr)
    (hxQ : ∀ T ∈ extra, sendsOn T.interactions B_SPQ = false) {r : Nat} (hr : r < tr.height 2)
    (h1 : ev tr 2 r pub (Br.c "oSL") = 1) :
    ∃ s, s < tr.height 3 ∧ ev tr 3 s pub Sn.gX = 1 ∧ snSpQ.map (E tr 3 s pub) = brSpQ.map (E tr 2 r pub) := by
  have h2 : 2 < (fullAir D extra nb np).tables.length := by simp [fullAir, m5aAir]
  have hm := msg_mem_busList (A := fullAir D extra nb np) (t := 2) h2
    (by rw [fullAir_get (by simp [m5aAir]) _]; exact br_spq_r) hr rfl (ev_one_eval h1)
  obtain ⟨s, hs, i, hi, hb, hss, hp, he⟩ :=
    sender_m5a B_SPQ 3 (by simp [m5aAir]) (spq_only D) hxQ (recv_sent hH hm)
  change i ∈ Sn.interactions at hi
  obtain rfl := filter_one_mem sn_spq_s hi hb hss
  exact ⟨s, hs, eval_one_ev (multNat_one_bit rfl hp), he.symm⟩

/-- **`OslApart` from `Holds`**: a split's new branch never sits at an active `BR` row's walk
position. -/
theorem oslApart (hH : Holds (fullAir D extra nb np) pub tr) (hD : D ≤ 30)
    (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP)
    (hxN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
    (hxL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
    (hxR : ∀ T ∈ extra, sendsOn T.interactions B_KCR = false)
    (hxQ : ∀ T ∈ extra, sendsOn T.interactions B_SPQ = false) : OslApart tr pub := by
  intro r r' hr hr' hg hs1 ew ed
  obtain ⟨s, hs, hX, he⟩ := osl_spq hH hxQ hr' hs1
  have hc := tbl_sn D extra nb np hH s (List.mem_range.2 hs)
  obtain ⟨hgs, h0, hA, -⟩ := split_flags hc hX
  have hdep := SnDepthAll.sn_depth_all hH hxN hxL s hs (ev_one_eval hgs)
  have hjm := (RowSnM.sn_jm hc hA).1
  simp only [snSpQ, brSpQ, List.map_append, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.cons.injEq] at he
  obtain ⟨ew', ed', -⟩ := he
  have hw : ev tr 2 r pub (Br.c "w") = ev tr 3 s pub (Sn.c "w") := toNat_eq (ew.trans ew'.symm)
  have hd : ev tr 2 r pub (Br.c "d") = ev tr 3 s pub (Sn.c "d" + Sn.c "jm") := toNat_eq (ed.trans ed'.symm)
  rw [ev_hadd, Nat.mod_eq_of_lt (by omega)] at hd
  have := br_above_term hH hD hx hxN hxK hxR hr hs (ev_one_eval hg) (ev_one_eval hgs) h0 hw
  omega

end

end StateM5a.WalkEnd
