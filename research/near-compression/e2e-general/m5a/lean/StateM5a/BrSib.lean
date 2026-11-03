import StateM5a.BrRange

/-!
# StateM5a.BrSib — the `SIBQ` / `SIBA` answer of a `BR.oD1` row from `Holds`

A `BR.oD1` row at `(w, d)` sends `SIBQ(w, d+1, ref)` and receives `SIBA(w, d+1, kid2, len, vh)`.
The answer it receives was sent (bus balance) by an `SN.oLS` row `s` (the only `SIBA` sender), at
`(w, d+1)`; that row received a `SIBQ(w, d+1, ref')`, sent by a `BR.oD1` row `r'` (the only `SIBQ`
sender) at `(w, d)`.  Both `BR` rows are active walk rows at the same walk position, so `r' = r`
(`br_row_unique`, from `Traffic.walk_unique`): the responder answered exactly this row's request,
and its relation (`SnSibOK`, premise: `BusSplit.sibRel_oLS` on every `SN.oLS` row) is the
requester's `SibRel` (`br_sib`).  No `Perm` bookkeeping is needed: requests are unique per walk
position.
-/

namespace StateM5a.BrSib

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.KcChain StateM5a.KeyDecode

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## The messages -/

def brSibQ : List Expr := [Br.c "w", Br.c "d" + 1, Br.isnSib] ++ pack2 Br.chSib
def brSibA : List Expr :=
  [Br.c "w", Br.c "d" + 1, Br.c "kid2", Br.c "lvlen"] ++ (List.range 16).map fun i => Br.c "lvh" i
def snSibQ : List Expr := [Sn.c "w", Sn.c "d", Sn.c "oref"] ++ pack2 fun b => Sn.c "ho" b
def snSibA : List Expr :=
  [Sn.c "w", Sn.c "d", Sn.c "kid", Sn.vlenOf fun t => Sn.c "x" t] ++ pack2 fun b => Sn.c "x" (4 + b)

theorem br_sibq_s : Br.interactions.filter (fun i => decide (i.bus = B_SIBQ ∧ i.send = true)) =
    [snd B_SIBQ (Br.c "oD1") brSibQ] := by decide
theorem br_siba_r : rcv B_SIBA (Br.c "oD1") brSibA ∈ Br.interactions := memD_mem (by decide)
theorem sn_sibq_r : rcv B_SIBQ (Sn.c "oLS") snSibQ ∈ Sn.interactions := memD_mem (by decide)
theorem sn_siba_s : Sn.interactions.filter (fun i => decide (i.bus = B_SIBA ∧ i.send = true)) =
    [snd B_SIBA (Sn.c "oLS") snSibA] := by decide

theorem sibq_only (D : Nat) : ∀ t (ht : t < (m5aAir D).tables.length), t ≠ 2 →
    sendsOn ((m5aAir D).tables[t]).interactions B_SIBQ = false
  | 0, _, _ => by show sendsOn shaTable.interactions B_SIBQ = false; decide
  | 1, _, _ => by show sendsOn Key.interactions B_SIBQ = false; decide
  | 2, _, h => absurd rfl h
  | 3, _, _ => by show sendsOn Sn.interactions B_SIBQ = false; decide
  | 4, _, _ => by show sendsOn Kcmp.interactions B_SIBQ = false; decide
  | 5, _, _ => by show sendsOn Wsb.interactions B_SIBQ = false; decide
  | 6, _, _ => by show sendsOn Wsn.interactions B_SIBQ = false; decide
  | 7, _, _ => by show sendsOn Wsa.interactions B_SIBQ = false; decide
  | 8, _, _ => by show sendsOn Snc.interactions B_SIBQ = false; decide
  | 9, _, _ => by show sendsOn Rng.interactions B_SIBQ = false; decide
  | 10, _, _ => by show sendsOn Wsl.interactions B_SIBQ = false; decide
  | 11, _, _ => by show sendsOn Wsp.interactions B_SIBQ = false; decide
  | n + 12, h, _ => absurd h (by simp [m5aAir])

theorem siba_only (D : Nat) : ∀ t (ht : t < (m5aAir D).tables.length), t ≠ 3 →
    sendsOn ((m5aAir D).tables[t]).interactions B_SIBA = false
  | 0, _, _ => by show sendsOn shaTable.interactions B_SIBA = false; decide
  | 1, _, _ => by show sendsOn Key.interactions B_SIBA = false; decide
  | 2, _, _ => by show sendsOn Br.interactions B_SIBA = false; decide
  | 3, _, h => absurd rfl h
  | 4, _, _ => by show sendsOn Kcmp.interactions B_SIBA = false; decide
  | 5, _, _ => by show sendsOn Wsb.interactions B_SIBA = false; decide
  | 6, _, _ => by show sendsOn Wsn.interactions B_SIBA = false; decide
  | 7, _, _ => by show sendsOn Wsa.interactions B_SIBA = false; decide
  | 8, _, _ => by show sendsOn Snc.interactions B_SIBA = false; decide
  | 9, _, _ => by show sendsOn Rng.interactions B_SIBA = false; decide
  | 10, _, _ => by show sendsOn Wsl.interactions B_SIBA = false; decide
  | 11, _, _ => by show sendsOn Wsp.interactions B_SIBA = false; decide
  | n + 12, h, _ => absurd h (by simp [m5aAir])

/-! ## Counting rows -/

theorem one_le_countP {α : Type} {f : Nat → Option α} {p : α → Bool} {r : Nat} {x : α}
    (hx : f r = some x) (hp : p x = true) : ∀ {l : List Nat}, r ∈ l → 1 ≤ (l.filterMap f).countP p
  | [], h => absurd h List.not_mem_nil
  | a :: l, h => by
    rw [List.filterMap_cons]
    rcases List.mem_cons.1 h with rfl | h
    · rw [hx, List.countP_cons, hp]; simp
    · have := one_le_countP hx hp h
      split
      · exact this
      · rw [List.countP_cons]; omega

theorem two_le_countP {α : Type} {f : Nat → Option α} {p : α → Bool} {r r' : Nat} {x x' : α}
    (hx : f r = some x) (hp : p x = true) (hx' : f r' = some x') (hp' : p x' = true) (hne : r ≠ r') :
    ∀ {l : List Nat}, l.Nodup → r ∈ l → r' ∈ l → 2 ≤ (l.filterMap f).countP p
  | [], _, h, _ => absurd h List.not_mem_nil
  | a :: l, hnd, h, h' => by
    rw [List.filterMap_cons]
    have hnd' := (List.nodup_cons.1 hnd)
    rcases List.mem_cons.1 h with rfl | hl
    · have h'' : r' ∈ l := (List.mem_cons.1 h').resolve_left (fun e => hne e.symm)
      have := one_le_countP hx' hp' h''
      rw [hx, List.countP_cons, hp, if_pos rfl]; omega
    · rcases List.mem_cons.1 h' with rfl | h''
      · have := one_le_countP hx hp hl
        rw [hx', List.countP_cons, hp', if_pos rfl]; omega
      · have := two_le_countP hx hp hx' hp' hne hnd'.2 hl h''
        split
        · exact this
        · rw [List.countP_cons]; omega

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

/-- **One active `BR` row per walk position.** -/
theorem br_row_unique (hH : Holds (fullAir D extra nb np) pub tr) (hD : D ≤ 30)
    (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP)
    (hxN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
    (hxR : ∀ T ∈ extra, sendsOn T.interactions B_KCR = false)
    {r r' : Nat} (hr : r < tr.height 2) (hr' : r' < tr.height 2) (hg : ev tr 2 r pub Br.gold = 1)
    (hg' : ev tr 2 r' pub Br.gold = 1) (hw : ev tr 2 r pub (Br.c "w") = ev tr 2 r' pub (Br.c "w"))
    (hd : ev tr 2 r pub (Br.c "d") = ev tr 2 r' pub (Br.c "d")) : r = r' := by
  refine Classical.byContradiction fun hne => ?_
  have hs := DepthBound.walk_shape' cDc D extra nb np hH hD hxN (sncDeeper hH hxN hxK hxR)
  have hU := walk_unique _ _ hs (walk_traffic cDc D extra nb np hH hx).1
    (ev tr 2 r pub (Br.c "w")) (ev tr 2 r pub (Br.c "d"))
  have h2 : 2 ≤ (rowsOf cDc brW tr 2 pub).countP (fun q => decide (q.din.w = ev tr 2 r pub (Br.c "w") ∧
      q.din.d = ev tr 2 r pub (Br.c "d"))) := by
    unfold rowsOf
    refine two_le_countP (r := r) (r' := r') (if_pos (ev_one_eval hg)) ?_ (if_pos (ev_one_eval hg')) ?_ hne
      List.nodup_range (List.mem_range.2 hr) (List.mem_range.2 hr')
    · simp only [br_din]; simp
    · simp only [br_din]; simp [hw, hd]
  have : recvAt (walkRows cDc tr pub) (ev tr 2 r pub (Br.c "w")) (ev tr 2 r pub (Br.c "d")) ≥ 2 := by
    unfold recvAt walkRows; rw [List.countP_append]; omega
  omega

theorem br_od1_gdn {r : Nat} (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (h1 : ev tr 2 r pub (Br.c "oD1") = 1) : ev tr 2 r pub (Br.c "gdn") = 1 := by
  have hb : ∀ s ∈ ["act", "mF", "mU", "mD", "gdn", "oFD", "oFA", "oUD", "oUN",
      "oDH", "oDL", "oDN", "oD1", "oFV", "oDA", "oDS", "oSL", "oUV", "oDV", "oDZ"],
      ev tr 2 r pub (Br.c s) ≤ 1 := fun s hs => bool_le (hold rfl hc (FieldWalk.br_bool s hs))
  have b0 := hb "gdn" (by simp); have b1 := hb "oFD" (by simp); have b2 := hb "oUD" (by simp)
  have b3 := hb "oDH" (by simp); have b4 := hb "oDL" (by simp); have b5 := hb "oDN" (by simp)
  have b7 := hb "oDS" (by simp)
  have e5 := eq_of_sub (hold rfl hc FieldWalk.br_mem_gdn)
  rw [show (Br.c "oFD" + Br.c "oUD" + Br.c "oDH" + Br.c "oDL" + Br.c "oDN" + Br.c "oD1" + Br.c "oDS" : Expr) =
      ([Br.c "oUD", Br.c "oDH", Br.c "oDL", Br.c "oDN", Br.c "oD1", Br.c "oDS"]).foldl (· + ·) (Br.c "oFD") from rfl,
    FieldWalk2.ev_foldl _ _ (by simp only [List.length_cons, List.length_nil]; omega)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro x hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)] at e5
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at e5
  omega

/-- What an `SN.oLS` row establishes, in its own columns (premise: `BusSplit.sibRel_oLS` with the
row's decoded old record and key lookups, the `SN` side). -/
def SnSibOK (σ : Store) (keyOf : Nat → List Nat) (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ s, s < tr.height 3 → ev tr 3 s pub (Sn.c "oLS") = 1 →
    SibRel σ keyOf (ev tr 3 s pub (Sn.c "d"))
      (refOf (E tr 3 s pub (Sn.c "oref")) ((pack2 fun b => Sn.c "ho" b).map (E tr 3 s pub)))
      (ev tr 3 s pub (Sn.c "kid")) (ev tr 3 s pub (Sn.vlenOf fun t => Sn.c "x" t))
      (bytesOf ((pack2 fun b => Sn.c "x" (4 + b)).map (E tr 3 s pub)))

/-- **The `SIBA` answer of a `BR.oD1` row** is its request's `SibRel`. -/
theorem br_sib {σ : Store} {keyOf : Nat → List Nat} (hH : Holds (fullAir D extra nb np) pub tr) (hD : D ≤ 30)
    (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP)
    (hxN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
    (hxR : ∀ T ∈ extra, sendsOn T.interactions B_KCR = false)
    (hxQ : ∀ T ∈ extra, sendsOn T.interactions B_SIBQ = false)
    (hxA : ∀ T ∈ extra, sendsOn T.interactions B_SIBA = false) (hS : SnSibOK σ keyOf tr pub)
    {r : Nat} (hr : r < tr.height 2) (h1 : ev tr 2 r pub (Br.c "oD1") = 1) :
    SibRel σ keyOf (ev tr 2 r pub (Br.c "d") + 1)
      (refOf (E tr 2 r pub Br.isnSib) ((pack2 Br.chSib).map (E tr 2 r pub)))
      (ev tr 2 r pub (Br.c "kid2")) (ev tr 2 r pub (Br.c "lvlen"))
      (bytesOf (((List.range 16).map fun i => Br.c "lvh" i).map (E tr 2 r pub))) := by
  have hc := tbl_br D extra nb np hH r (List.mem_range.2 hr)
  have hgd := br_od1_gdn hc h1
  have hg := FieldWalk.br_gdn_gold hc hgd
  have h2 : 2 < (fullAir D extra nb np).tables.length := by simp [fullAir, m5aAir]
  have h3 : 3 < (fullAir D extra nb np).tables.length := by simp [fullAir, m5aAir]
  -- the answer's sender: an `SN.oLS` row
  have hm1 := msg_mem_busList (A := fullAir D extra nb np) (t := 2) h2
    (by rw [fullAir_get (by simp [m5aAir]) _]; exact br_siba_r) hr rfl (ev_one_eval h1)
  obtain ⟨s, hs, i, hi, hb, hss, hp, he1⟩ :=
    sender_m5a B_SIBA 3 (by simp [m5aAir]) (siba_only D) hxA (recv_sent hH hm1)
  change i ∈ Sn.interactions at hi
  obtain rfl := filter_one_mem sn_siba_s hi hb hss
  have hls := multNat_one_bit (g := Sn.c "oLS") rfl hp
  -- its request's sender: a `BR.oD1` row
  have hm2 := msg_mem_busList (A := fullAir D extra nb np) (t := 3) h3
    (by rw [fullAir_get (by simp [m5aAir]) _]; exact sn_sibq_r) hs rfl hls
  obtain ⟨r', hr', i', hi', hb', hss', hp', he2⟩ :=
    sender_m5a B_SIBQ 2 (by simp [m5aAir]) (sibq_only D) hxQ (recv_sent hH hm2)
  change i' ∈ Br.interactions at hi'
  obtain rfl := filter_one_mem br_sibq_s hi' hb' hss'
  have h1' := eval_one_ev (multNat_one_bit (g := Br.c "oD1") rfl hp')
  have hc' := tbl_br D extra nb np hH r' (List.mem_range.2 hr')
  have hgd' := br_od1_gdn hc' h1'
  have hg' := FieldWalk.br_gdn_gold hc' hgd'
  simp only [rcv, snd, Interaction.msgVal, brSibA, snSibA, brSibQ, snSibQ, List.map_append, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append, List.cons.injEq] at he1 he2
  obtain ⟨ew1, ed1, ek, el, ev1⟩ := he1
  obtain ⟨ew2, ed2, eo, eh⟩ := he2
  -- the same walk position, so the same row
  have hd := DepthBound.br_depth hH hxN r hr (ev_one_eval hgd)
  have hd' := DepthBound.br_depth hH hxN r' hr' (ev_one_eval hgd')
  have esd : ev tr 3 s pub (Sn.c "d") = ev tr 2 r pub (Br.c "d") + 1 := by
    have := toNat_eq ed1.symm; rw [this, ev_hadd, ev_one, Nat.mod_eq_of_lt (by omega)]
  have esd' : ev tr 3 s pub (Sn.c "d") = ev tr 2 r' pub (Br.c "d") + 1 := by
    have := toNat_eq ed2; rw [this, ev_hadd, ev_one, Nat.mod_eq_of_lt (by omega)]
  obtain rfl : r = r' := br_row_unique hH hD hx hxN hxK hxR hr hr' hg hg'
    ((toNat_eq ew1).trans (toNat_eq ew2)) (by omega)
  have key := hS s hs (eval_one_ev hls)
  simp only [E] at key ⊢
  rw [esd, eo, eh, ← toNat_eq ek, ← toNat_eq el, ← ev1] at key
  exact key

end

end StateM5a.BrSib
