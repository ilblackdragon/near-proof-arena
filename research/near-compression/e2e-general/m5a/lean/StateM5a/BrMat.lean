import StateM5a.BrSib

/-!
# StateM5a.BrMat — the `MATQ` / `MATR` answer of a `BR.oDL` / `BR.oUN` row from `Holds`

A `BR` row at `(w, d)` with `oDL` or `oUN` sends `MATQ(w, d+1, kid2, st2, len, vh)` and receives
`MATR(w, d+1, kid2, ref, mem)`.  The answer was sent (bus balance) by an `SN.oLM` row `s` (the only
`MATR` sender) at `(w, d+1, kid2)`; that row received `MATQ(w, d+1, kid2, d+1, len', vh')`, sent by a
`BR` row `r'` at `(w, d)`: through its `gmat` request (`oDL`, `oUN`: an active walk row, so
`r' = r` by `BrSib.br_row_unique`; `oSL`: a split's new branch) or its `oSL·xl` request (a split's
new branch).  A split's new branch never sits at an active row's walk position (premise
`OslApart`: it is built below the walk's last row), so `r' = r` and the responder answered this
row's own request; its relation (`SnMatOK`, premise: `BusSplit.matRel_oLM` on every `SN.oLM` row) is
the requester's `MatRel` (`br_mat`).
-/

namespace StateM5a.BrMat

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.KcChain StateM5a.KeyDecode
open StateM5a.BrRange StateM5a.BrSib

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## The messages -/

def brMatQ : List Expr :=
  [Br.c "w", Br.c "d" + 1, Br.c "kid2", Br.c "st2", Br.c "lvlen"] ++ (List.range 16).map fun i => Br.c "lvh" i
def brMatQ2 : List Expr :=
  [Br.c "w", Br.c "d" + 1, Br.c "xk", Br.c "d" + 1, Br.c "lvlen2"] ++ (List.range 16).map fun i => Br.c "lvh2" i
def snMatQ : List Expr :=
  [Sn.c "w", Sn.c "d", Sn.c "kid", Sn.c "d", Sn.c "dvlen"] ++ (List.range 16).map fun i => Sn.c "dvh" i

theorem br_matq_s : Br.interactions.filter (fun i => decide (i.bus = B_MATQ ∧ i.send = true)) =
    [snd B_MATQ (Br.c "oDL" + Br.c "oUN" + Br.c "oSL") brMatQ,
     snd B_MATQ (Br.c "oSL" * Br.c "xl") brMatQ2] := by decide
theorem sn_matq_r : rcv B_MATQ (Sn.c "oLM") snMatQ ∈ Sn.interactions := memD_mem (by decide)

theorem matq_only (D : Nat) : ∀ t (ht : t < (m5aAir D).tables.length), t ≠ 2 →
    sendsOn ((m5aAir D).tables[t]).interactions B_MATQ = false
  | 0, _, _ => by show sendsOn shaTable.interactions B_MATQ = false; decide
  | 1, _, _ => by show sendsOn Key.interactions B_MATQ = false; decide
  | 2, _, h => absurd rfl h
  | 3, _, _ => by show sendsOn Sn.interactions B_MATQ = false; decide
  | 4, _, _ => by show sendsOn Kcmp.interactions B_MATQ = false; decide
  | 5, _, _ => by show sendsOn Wsb.interactions B_MATQ = false; decide
  | 6, _, _ => by show sendsOn Wsn.interactions B_MATQ = false; decide
  | 7, _, _ => by show sendsOn Wsa.interactions B_MATQ = false; decide
  | 8, _, _ => by show sendsOn Snc.interactions B_MATQ = false; decide
  | 9, _, _ => by show sendsOn Rng.interactions B_MATQ = false; decide
  | 10, _, _ => by show sendsOn Wsl.interactions B_MATQ = false; decide
  | 11, _, _ => by show sendsOn Wsp.interactions B_MATQ = false; decide
  | n + 12, h, _ => absurd h (by simp [m5aAir])

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

theorem br_flag_le {r : Nat} (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0) (s : String)
    (hs : s ∈ ["act", "mF", "mU", "mD", "gdn", "oFD", "oFA", "oUD", "oUN",
      "oDH", "oDL", "oDN", "oD1", "oFV", "oDA", "oDS", "oSL", "oUV", "oDV", "oDZ"]) :
    ev tr 2 r pub (Br.c s) ≤ 1 := bool_le (hold rfl hc (FieldWalk.br_bool s hs))

/-- An `oUN` row is active. -/
theorem br_oUN_gold {r : Nat} (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (h1 : ev tr 2 r pub (Br.c "oUN") = 1) : ev tr 2 r pub Br.gold = 1 := by
  have b1 := br_flag_le hc "oUD" (by simp); have b2 := br_flag_le hc "oUV" (by simp)
  have b3 := br_flag_le hc "mU" (by simp); have b4 := br_flag_le hc "mF" (by simp)
  have b5 := br_flag_le hc "mD" (by simp); have b6 := br_flag_le hc "oSL" (by simp)
  have b7 := br_flag_le hc "act" (by simp)
  have e3 := eq_of_sub (hold rfl hc FieldWalk.br_mem_mU)
  rw [show (Br.c "oUD" + Br.c "oUN" + Br.c "oUV" : Expr) = ([Br.c "oUN", Br.c "oUV"]).foldl (· + ·) (Br.c "oUD")
      from rfl, FieldWalk2.ev_foldl _ _ (by simp only [List.length_cons, List.length_nil]; omega)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro x hx; rcases hx with rfl | rfl <;> omega)] at e3
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at e3
  have e1 := eq_of_sub (hold rfl hc FieldWalk.br_mem_act)
  rw [show (Br.c "mF" + Br.c "mU" + Br.c "mD" + Br.c "oSL" : Expr) =
      ([Br.c "mU", Br.c "mD", Br.c "oSL"]).foldl (· + ·) (Br.c "mF") from rfl,
    FieldWalk2.ev_foldl _ _ (by simp only [List.length_cons, List.length_nil]; omega)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro x hx
          rcases hx with rfl | rfl | rfl <;> omega)] at e1
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at e1
  have hs : ev tr 2 r pub (Br.c "oSL") = 0 := by omega
  have ha : ev tr 2 r pub (Br.c "act") = 1 := by omega
  unfold Br.gold; rw [ev_sub, ha, hs]

/-- What an `SN.oLM` row establishes, in its own columns (premise: `BusSplit.matRel_oLM` with the
row's key lookups and new record, the `SN` side). -/
def SnMatOK (σ : Store) (keyOf : Nat → List Nat) (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ s, s < tr.height 3 → ev tr 3 s pub (Sn.c "oLM") = 1 →
    MatRel σ keyOf (ev tr 3 s pub (Sn.c "kid")) (ev tr 3 s pub (Sn.c "d")) (ev tr 3 s pub (Sn.c "dvlen"))
      (bytesOf (((List.range 16).map fun i => Sn.c "dvh" i).map (E tr 3 s pub)))
      (refOf (E tr 3 s pub (Sn.c "nref")) ((pack2 fun b => Sn.c "hn" b).map (E tr 3 s pub)))
      (le4 (Sn.NM.map (E tr 3 s pub)))

/-- A split's new branch (`oSL`) never sits at an active `BR` row's walk position (premise). -/
def OslApart (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ r r', r < tr.height 2 → r' < tr.height 2 → ev tr 2 r pub Br.gold = 1 → ev tr 2 r' pub (Br.c "oSL") = 1 →
    E tr 2 r pub (Br.c "w") = E tr 2 r' pub (Br.c "w") → E tr 2 r pub (Br.c "d") = E tr 2 r' pub (Br.c "d") → False

theorem br_oDL_gdn {r : Nat} (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (h1 : ev tr 2 r pub (Br.c "oDL") = 1) : ev tr 2 r pub (Br.c "gdn") = 1 := by
  have b0 := br_flag_le hc "gdn" (by simp); have b1 := br_flag_le hc "oFD" (by simp)
  have b2 := br_flag_le hc "oUD" (by simp); have b3 := br_flag_le hc "oDH" (by simp)
  have b5 := br_flag_le hc "oDN" (by simp); have b6 := br_flag_le hc "oD1" (by simp)
  have b7 := br_flag_le hc "oDS" (by simp)
  have e5 := eq_of_sub (hold rfl hc FieldWalk.br_mem_gdn)
  rw [show (Br.c "oFD" + Br.c "oUD" + Br.c "oDH" + Br.c "oDL" + Br.c "oDN" + Br.c "oD1" + Br.c "oDS" : Expr) =
      ([Br.c "oUD", Br.c "oDH", Br.c "oDL", Br.c "oDN", Br.c "oD1", Br.c "oDS"]).foldl (· + ·) (Br.c "oFD") from rfl,
    FieldWalk2.ev_foldl _ _ (by simp only [List.length_cons, List.length_nil]; omega)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro x hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)] at e5
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at e5
  omega

theorem fp_cancel {a b : Fp} (h : a + 1 = b + 1) : a = b := by grind

theorem eval_succ {x : Expr} {t r : Nat} : (x + 1).eval tr t r pub = x.eval tr t r pub + (1 : Expr).eval tr t r pub :=
  rfl

/-- **The `MATR` answer of a `BR.oDL` / `BR.oUN` row** is its request's `MatRel`. -/
theorem br_mat {σ : Store} {keyOf : Nat → List Nat} (hH : Holds (fullAir D extra nb np) pub tr) (hD : D ≤ 30)
    (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP)
    (hxN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
    (hxR : ∀ T ∈ extra, sendsOn T.interactions B_KCR = false)
    (hxQ : ∀ T ∈ extra, sendsOn T.interactions B_MATQ = false)
    (hxM : ∀ T ∈ extra, sendsOn T.interactions B_MATR = false)
    (hS : SnMatOK σ keyOf tr pub) (hA : OslApart tr pub)
    {r : Nat} (hr : r < tr.height 2) (h1 : ev tr 2 r pub (Br.c "oDL") = 1 ∨ ev tr 2 r pub (Br.c "oUN") = 1) :
    MatRel σ keyOf (ev tr 2 r pub (Br.c "kid2")) (ev tr 2 r pub (Br.c "st2")) (ev tr 2 r pub (Br.c "lvlen"))
      (bytesOf (((List.range 16).map fun i => Br.c "lvh" i).map (E tr 2 r pub)))
      (refOf (E tr 2 r pub (Br.c "nhf")) ((pack2 fun b => Br.c "nh" b).map (E tr 2 r pub)))
      (le4 (((List.range 4).map fun k => Br.c "nm" k).map (E tr 2 r pub))) := by
  have hc := tbl_br D extra nb np hH r (List.mem_range.2 hr)
  have hg : ev tr 2 r pub Br.gold = 1 := by
    rcases h1 with h | h
    · exact FieldWalk.br_gdn_gold hc (br_oDL_gdn hc h)
    · exact br_oUN_gold hc h
  have hgm : ev tr 2 r pub (Br.c "oDL" + Br.c "oUN" + Br.c "oSL") = 1 := by
    brfacts hc hg
    rw [ev_add_lt (by rw [ev_add_lt (by omega)]; omega), ev_add_lt (by omega)]; omega
  have h2 : 2 < (fullAir D extra nb np).tables.length := by simp [fullAir, m5aAir]
  have h3 : 3 < (fullAir D extra nb np).tables.length := by simp [fullAir, m5aAir]
  -- the answer's sender: an `SN.oLM` row
  have hm1 := msg_mem_busList (A := fullAir D extra nb np) (t := 2) h2
    (by rw [fullAir_get (by simp [m5aAir]) _]; exact br_matr_r) hr rfl (ev_one_eval hgm)
  obtain ⟨s, hs, i, hi, hb, hss, hp, he1⟩ :=
    sender_m5a B_MATR 3 (by simp [m5aAir]) (matr_only D) hxM (recv_sent hH hm1)
  change i ∈ Sn.interactions at hi
  obtain rfl := filter_one_mem sn_matr_s hi hb hss
  have hlm := multNat_one_bit (g := Sn.c "oLM") rfl hp
  -- its request's sender: a `BR` row
  have hm2 := msg_mem_busList (A := fullAir D extra nb np) (t := 3) h3
    (by rw [fullAir_get (by simp [m5aAir]) _]; exact sn_matq_r) hs rfl hlm
  obtain ⟨r', hr', i', hi', hb', hss', hp', he2⟩ :=
    sender_m5a B_MATQ 2 (by simp [m5aAir]) (matq_only D) hxQ (recv_sent hH hm2)
  change i' ∈ Br.interactions at hi'
  have hc' := tbl_br D extra nb np hH r' (List.mem_range.2 hr')
  have hmem : i' ∈ Br.interactions.filter (fun i => decide (i.bus = B_MATQ ∧ i.send = true)) :=
    List.mem_filter.2 ⟨hi', by simp [hb', hss']⟩
  rw [br_matq_s] at hmem
  simp only [rcv, snd, Interaction.msgVal, brMatR, snMatR, List.map_append, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append, List.cons.injEq] at he1
  obtain ⟨ew1, ed1, ek1, en1, eh1⟩ := he1
  rcases List.mem_cons.1 hmem with rfl | hmem
  · have hgm' := eval_one_ev (multNat_one_bit rfl hp')
    simp only [rcv, snd, Interaction.msgVal, brMatQ, snMatQ, List.map_append, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append, List.cons.injEq] at he2
    obtain ⟨ew2, ed2, ek2, est, el2, eh2⟩ := he2
    have ew : E tr 2 r pub (Br.c "w") = E tr 2 r' pub (Br.c "w") := ew1.trans ew2
    have ed : E tr 2 r pub (Br.c "d") = E tr 2 r' pub (Br.c "d") := by
      have := ed1.trans ed2; rw [eval_succ, eval_succ] at this; exact fp_cancel this
    have bL := br_flag_le hc' "oDL" (by simp); have bU := br_flag_le hc' "oUN" (by simp)
    have bS := br_flag_le hc' "oSL" (by simp)
    rcases (by omega : ev tr 2 r' pub (Br.c "oSL") = 1 ∨ ev tr 2 r' pub (Br.c "oSL") = 0) with hs1 | hs0
    · exact (hA r r' hr hr' hg hs1 ew ed).elim
    have hg' : ev tr 2 r' pub Br.gold = 1 := by
      rw [ev_add_lt (by rw [ev_add_lt (by omega)]; omega), ev_add_lt (by omega)] at hgm'
      rcases (by omega : ev tr 2 r' pub (Br.c "oDL") = 1 ∨ ev tr 2 r' pub (Br.c "oUN") = 1) with h | h
      · exact FieldWalk.br_gdn_gold hc' (br_oDL_gdn hc' h)
      · exact br_oUN_gold hc' h
    obtain rfl : r = r' := br_row_unique hH hD hx hxN hxK hxR hr hr' hg hg'
      (congrArg Fp.toNat ew) (congrArg Fp.toNat ed)
    have key := hS s hs (eval_one_ev hlm)
    obtain ⟨a1, a2⟩ := List.append_inj eh1 (by simp [pack2])
    have q1 : List.map (E tr 3 s pub) ((List.range 16).map fun i => Sn.c "dvh" i) =
        List.map (E tr 2 r pub) ((List.range 16).map fun i => Br.c "lvh" i) := eh2
    have q2 : List.map (E tr 3 s pub) (pack2 fun b => Sn.c "hn" b) =
        List.map (E tr 2 r pub) (pack2 fun b => Br.c "nh" b) := a1.symm
    have q3 : List.map (E tr 3 s pub) Sn.NM = List.map (E tr 2 r pub) ((List.range 4).map fun k => Br.c "nm" k) :=
      a2.symm
    have q4 : E tr 3 s pub (Sn.c "nref") = E tr 2 r pub (Br.c "nhf") := en1.symm
    rw [toNat_eq ek2, toNat_eq est, toNat_eq el2, q1, q4, q2, q3] at key
    exact key
  · rw [List.mem_singleton] at hmem
    subst hmem
    have hx1 := eval_one_ev (multNat_one_bit rfl hp')
    have bS := br_flag_le hc' "oSL" (by simp)
    have hs1 : ev tr 2 r' pub (Br.c "oSL") = 1 := by
      rw [ev_hmul] at hx1
      rcases (by omega : ev tr 2 r' pub (Br.c "oSL") = 1 ∨ ev tr 2 r' pub (Br.c "oSL") = 0) with h | h
      · exact h
      · rw [h] at hx1; simp at hx1
    simp only [rcv, snd, Interaction.msgVal, brMatQ2, snMatQ, List.map_append, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append, List.cons.injEq] at he2
    obtain ⟨ew2, ed2, -⟩ := he2
    have ew : E tr 2 r pub (Br.c "w") = E tr 2 r' pub (Br.c "w") := ew1.trans ew2
    have ed : E tr 2 r pub (Br.c "d") = E tr 2 r' pub (Br.c "d") := by
      have := ed1.trans ed2; rw [eval_succ, eval_succ] at this; exact fp_cancel this
    exact (hA r r' hr hr' hg hs1 ew ed).elim

end

end StateM5a.BrMat
