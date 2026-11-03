import StateM5a.WsDecode2
import StateM5a.WsLen
import StateM5a.WsSeg

/-!
# StateM5a.WsDecode3 — the working-set record premises from `Holds`, and the final working set

Row facts of the decoded rows (`WsDecode2`), proved from the constraints, `RNG` and `IF384`:

* `rng_send_lt` / `rng_rcv`: every value looked up in `RNG` is `< 256` (no other table and no
  extra table sends on `RNG`);
* `wsp_rowF`: the raw `WSP` rows satisfy `WsRaw.RowF D` (`1 ≤ D ≤ 30`);
* `wsp_ok`: every decoded `WSP` row satisfies `WsBus.WspOK (nodeH compress) D` — the untouched
  child kept (`WsCost.wsp_keep`), the two compressions `oo = nodeH lo ro`, `on = nodeH ln rn` from
  the chip contract (`Sha512If.comp_node` via `WsDecode.comp_mem`), the top row's position;
* `wsa_gap_rec`: every decoded access has `idp < t` (`WsCost.wsa_gap`: gap bytes from `RNG`, times
  `< 2^24` from the public tape — premise `htape` on the `WRITE` sends — and `idp` is a sent time
  by `WM` balance);
* `wsl_ok`: a touched leaf is at a tree position `i < 2^D` and a real entry `i < wsLen`
  (`WsRaw.wsl_i_lt`, `WsLen.wsl_lt_wsLen`); `wsl_leaf`: its old / new digests are the leaf
  compressions `digest6 (compress IV384 bw)` of its decoded blocks, and the length chunks are
  `< 64` (`x_lt64`: the chip's top limb is `< 2^22` and `kd < 2^16`, so `kd + 2^16·x` forces
  `x < 64` — the chunk decomposition is canonical);
* **`ws_decoded`**: `PT`, `WM`, `RCH` balance of the decoded rows (`WsBus` form, no wrap-around),
  `WspOK`, the gap — every record premise of `WsSeg.ws_final` except the `WSN` roots and `hkd`;
* **`ws_decoded_final`**: with the `WSN` INTAKE / FINAL roots (premise: the decoded `WSN` root
  messages are `[(0, r0)]`, `[(nw, rF)]` with `r0 = root ws0`, `rF = root wsF`), `NodeCR` and
  `hkd`, the conclusion of `WsSeg.ws_final` for the AIR's rows.
-/

namespace StateM5a.WsDecode3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.FieldRows StateM5a.FieldRows2 StateM5a.Sha512If
open StateM5a.WsDecode StateM5a.WsDecode2 StateM5a.WsBus StateM5a.WsRaw StateM5a.Merkle

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## `RNG` sends -/

def noSnd (is : List Interaction) (b : Nat) : Bool := is.all fun i => !(i.bus == b && i.send)

theorem noSnd_spec {is : List Interaction} {b : Nat} (h : noSnd is b = true) {i : Interaction}
    (hi : i ∈ is) (hb : i.bus = b) (hs : i.send = true) : False := by
  have := List.all_eq_true.1 h i hi
  simp [hb, hs] at this

theorem ns_rng (D k : Nat) (hk : k < 12) (h9 : k ≠ 9) : noSnd ((m5aAir D).tables[k]!).interactions B_RNG = true := by
  have e : ((m5aAir D).tables[k]!).interactions = ((m5aAir 0).tables[k]!).interactions := by
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨
      k = 10 ∨ k = 11) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [e]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 10 ∨ k = 11)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

section
variable {D : Nat} {extra : List Table} {nb np : Nat} {tr : Trace Fp} {pub : List Fp}
  (hH : Holds (fullAir D extra nb np) pub tr)
  (hxr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RNG)

include hH hxr in
/-- **Every `RNG` value is a byte.** -/
theorem rng_send_lt {m : List Fp} (hm : m ∈ busList (fullAir D extra nb np) tr pub B_RNG true) :
    tn (m.getD 0 0) < 256 := by
  obtain ⟨t, ht, r, hr, i, hi, hb, hs, rfl⟩ := busList_inv _ hm
  rw [full_len] at ht
  by_cases h12 : t < 12
  · by_cases h9 : t = 9
    · subst h9
      rw [full_rng] at hi
      have hc := holds_constr hH (by decide) (full_rng (D := D) (extra := extra) (nb := nb) (np := np))
      have hl := holds_log hH (by decide) (full_rng (D := D) (extra := extra) (nb := nb) (np := np))
      have hv := rng_v hc hl r hr
      have hH8 : tr.height 9 ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) hl
      simp only [Rng.table, Rng.interactions, List.mem_singleton] at hi
      subst hi
      simp only [Interaction.msgVal, sndBits, List.map_cons, List.map_nil, List.getD_cons_zero]
      show ev tr 9 r pub (Rng.c "v") < 256
      omega
    · rw [full_get t h12] at hi
      exact absurd (noSnd_spec (ns_rng D t h12 h9) hi hb hs) id
  · exact absurd hb (hxr _ (full_get_extra t (by omega) ht) i hi)

include hH hxr in
/-- A row's `RNG` lookup with bit `1` is `< 256`. -/
theorem rng_rcv {t : Nat} (ht : t < (fullAir D extra nb np).tables.length) {g e : Expr}
    (hi : rcv B_RNG g [e] ∈ ((fullAir D extra nb np).tables[t]!).interactions) {r : Nat}
    (hr : r < tr.height t) (hg : g.eval tr t r pub = 1) : ev tr t r pub e < 256 := by
  have h1 := mem_busList (fullAir D extra nb np) ht hi hr (mult_one hg)
  have h2 := (holds_perm hH B_RNG).mem_iff.2 h1
  exact rng_send_lt hH hxr h2

end

/-! ## Limb triples of constants -/

theorem constW_dec {tr : Trace Fp} {t r : Nat} {pub : List Fp} {x : Nat} (hx : x < 2 ^ 64) :
    dec3 tr t r pub (constW x) = wlimbs x := by
  simp only [dec3, constW, K, ev_const, wlimbs]
  simp only [Nat.reducePow, List.cons.injEq] at hx ⊢
  exact ⟨by omega, by omega, by omega, trivial⟩

theorem ivW_dec {tr : Trace Fp} {t r : Nat} {pub : List Fp} : ivW.map (dec3 tr t r pub) = IV384.map wlimbs := by
  unfold ivW
  rw [List.map_map]
  apply List.map_congr_left
  intro x hx
  exact constW_dec (by revert x; decide)

theorem pad_dec {tr : Trace Fp} {t r : Nat} {pub : List Fp} :
    [constW (2 ^ 63), zeroW, zeroW, constW 768].map (dec3 tr t r pub) = padW.map wlimbs := by
  simp only [List.map_cons, List.map_nil, padW, constW_dec (show 2 ^ 63 < 2 ^ 64 by decide),
    constW_dec (show 768 < 2 ^ 64 by decide), dec3_zero, wlimbs_zero]

theorem node_dec {tr : Trace Fp} {t r : Nat} {pub : List Fp} (l rr o ox : Nat → Expr) :
    (ivW ++ nodeBlock (digW l) (digW rr) ++ digW o ++ wordsOf ox 2).map (dec3 tr t r pub) =
      IV384.map wlimbs ++ ((digW l).map (dec3 tr t r pub) ++ (digW rr).map (dec3 tr t r pub) ++ padW.map wlimbs) ++
        ((digW o).map (dec3 tr t r pub) ++ (wordsOf ox 2).map (dec3 tr t r pub)) := by
  simp only [nodeBlock, List.map_append, ivW_dec, ← pad_dec (tr := tr) (t := t) (r := r) (pub := pub),
    List.append_assoc]

/-! ## `WSP` rows -/

section Wsp
variable {D : Nat} {tr : Trace Fp} {r : Nat} {pub : List Fp}

theorem wsp_mem_topL : Wsp.c "top" * (Wsp.c "lvl" - K (D - 1)) ∈ Wsp.constraints D := by
  unfold Wsp.constraints; simp
theorem wsp_mem_topI : Wsp.c "top" * Wsp.c "idx" ∈ Wsp.constraints D := by unfold Wsp.constraints; simp

theorem wsp_top_pos (hc : ∀ e ∈ (Wsp.table D).constraints, e.eval tr 11 r pub = 0) (hD1 : 1 ≤ D) (hD : D ≤ 30)
    (ht : ev tr 11 r pub (Wsp.c "top") = 1) :
    ev tr 11 r pub (Wsp.c "lvl") + 1 = D ∧ ev tr 11 r pub (Wsp.c "idx") = 0 := by
  have h1 := eq_of_sub (FieldWsb.wsb_gate ht (hold rfl hc (wsp_mem_topL (D := D))))
  have h2 := FieldWsb.wsb_gate ht (hold rfl hc (wsp_mem_topI (D := D)))
  have hP : D - 1 < P := by omega
  rw [show K (D - 1) = Expr.const (D - 1) from rfl, ev_const, Nat.mod_eq_of_lt hP] at h1
  exact ⟨by omega, h2⟩

theorem wsp_rowF (hc : ∀ e ∈ (Wsp.table D).constraints, e.eval tr 11 r pub = 0) (hD1 : 1 ≤ D) (hD : D ≤ 30)
    (hA : ev tr 11 r pub (Wsp.c "act") = 1) : RowF D (wspRow tr pub r) := by
  refine ⟨?_, ?_, ?_, ?_, ev_lt _, ev_lt _, ev_lt _, ?_, fun h => ?_, fun h => ?_⟩
  · simp only [wspRow]; rw [ev_hadd, ev_one]
  · simp only [wspRow, sm, ev_mul, ev_const, Nat.reduceMod]
  · simp only [wspRow, sm, ev_hadd, ev_one, ev_mul, ev_const, Nat.reduceMod]
    have := ev_lt (tr := tr) (t := 11) (r := r) (pub := pub) (Wsp.c "idx")
    omega
  · simp only [wspRow]; rw [ev_hadd, ev_one]
  · rcases WsCost.wsp_child hc hA with h | h
    · left; simp [wspRow, h]
    · right; simp [wspRow, h]
  · have : ev tr 11 r pub (Wsp.c "top") = 1 := by simpa [wspRow] using h
    exact (wsp_top_pos hc hD1 hD this).1
  · have : ev tr 11 r pub (Wsp.c "top") = 1 := by simpa [wspRow] using h
    exact (wsp_top_pos hc hD1 hD this).2

end Wsp

section Ok
variable {D : Nat} {extra : List Table} {nb np : Nat} {tr : Trace Fp} {pub : List Fp}
  {compress : List Nat → List Nat → List Nat}

theorem wsp_compO : ∀ i ∈ comp (Wsp.c "act") (Wsp.c "cidO")
    (ivW ++ nodeBlock (digW fun t => Wsp.c "lo" t) (digW fun t => Wsp.c "ro" t) ++ digW (fun t => Wsp.c "oo" t) ++
      wordsOf (fun t => Wsp.c "oox" t) 2), i ∈ ((fullAir D extra nb np).tables[11]!).interactions := by
  intro i hi
  rw [full_wsp]
  exact List.mem_append_left _ (List.mem_append_right _ hi)

theorem wsp_compN : ∀ i ∈ comp (Wsp.c "act") (Wsp.c "cidN")
    (ivW ++ nodeBlock (digW fun t => Wsp.c "ln" t) (digW fun t => Wsp.c "rn" t) ++ digW (fun t => Wsp.c "on" t) ++
      wordsOf (fun t => Wsp.c "onx" t) 2), i ∈ ((fullAir D extra nb np).tables[11]!).interactions := by
  intro i hi
  rw [full_wsp]
  exact List.mem_append_right _ hi

/-- One node compression of a `WSP` row: the output digest is `nodeH` of the children's. -/
theorem wsp_node (hcomp : CompressOK compress)
    (hC : Sha512IfContract compress ((busList (fullAir D extra nb np) tr pub B_IF384 true).map decIf))
    (hperm : (busList (fullAir D extra nb np) tr pub B_IF384 true).Perm (busList (fullAir D extra nb np) tr pub B_IF384 false))
    {r : Nat} (hr : r < tr.height 11) (hA : (Wsp.c "act").eval tr 11 r pub = 1) {cid : Expr} {l rr o ox : Nat → Expr}
    (hsub : ∀ i ∈ comp (Wsp.c "act") cid (ivW ++ nodeBlock (digW l) (digW rr) ++ digW o ++ wordsOf ox 2),
      i ∈ ((fullAir D extra nb np).tables[11]!).interactions) :
    rowDig tr 11 r pub o = nodeH compress (rowDig tr 11 r pub l) (rowDig tr 11 r pub rr) := by
  have hm := comp_mem hperm (by rw [full_len]; omega) hsub hr hA
  rw [node_dec] at hm
  obtain ⟨dl, dr, el, er, eo⟩ := comp_node hcomp hC (by simp [digW]) (by simp [digW]) (by simp [digW])
    (by simp [wordsOf]) hm
  rw [rowDig_of eo, rowDig_of el, rowDig_of er]

/-- **Every decoded `WSP` row satisfies `WspOK`.** -/
theorem wsp_ok (hH : Holds (fullAir D extra nb np) pub tr) (hD1 : 1 ≤ D) (hD : D ≤ 30)
    (hcomp : CompressOK compress)
    (hC : Sha512IfContract compress ((busList (fullAir D extra nb np) tr pub B_IF384 true).map decIf)) :
    ∀ x ∈ wspF tr pub, WspOK (nodeH compress) D x.r := by
  intro x hx
  obtain ⟨r, hr, hA, rfl⟩ := actRows_mem hx
  have hc := holds_constr hH (t := 11) (by decide) full_wsp r hr
  have hperm := holds_perm hH B_IF384
  have hA' := eval_one_ev hA
  obtain ⟨-, -, -⟩ := wsp_flags hc
  have hbl := ev_bool (hold rfl hc (WsCost.wsp_mem (D := D) "tl" (by simp)))
  have hbr := ev_bool (hold rfl hc (WsCost.wsp_mem (D := D) "tr" (by simp)))
  refine ⟨fun h => ?_, fun h => ?_, ?_, ?_, fun h => ?_, fun h => ?_⟩
  · have h0 : ev tr 11 r pub (Wsp.c "tl") = 0 := by
      simp only [wspRow, decide_eq_false_iff_not] at h; omega
    exact rowDig_congr fun j hj => (WsCost.wsp_keep hc j hj).1 h0
  · have h0 : ev tr 11 r pub (Wsp.c "tr") = 0 := by
      simp only [wspRow, decide_eq_false_iff_not] at h; omega
    exact rowDig_congr fun j hj => (WsCost.wsp_keep hc j hj).2 h0
  · exact wsp_node hcomp hC hperm hr hA wsp_compO
  · exact wsp_node hcomp hC hperm hr hA wsp_compN
  · exact (wsp_rowF hc hD1 hD hA').topLvl h
  · exact (wsp_rowF hc hD1 hD hA').topIdx h

end Ok


/-! ## Leaf blocks: the chunks are `< 64` -/

theorem leaf_third (kd x pv cv : Nat → Expr) (u : Nat) (hu : u < 16) :
    ∃ a b, (leafBlock kd x pv cv)[u]? = some (a, b, kd u + K 65536 * x u) := by
  unfold leafBlock
  by_cases h8 : u < 8
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_map, List.getElem?_range h8]
    exact ⟨_, _, rfl⟩
  · rw [List.getElem?_append_right (by simp; omega), List.getElem?_map]
    simp only [List.length_map, List.length_range]
    rw [List.getElem?_range (by omega)]
    refine ⟨cv (2 * (u - 8)), cv (2 * (u - 8) + 1), ?_⟩
    simp only [Option.map_some, show 8 + (u - 8) = u by omega]

/-- **A leaf block's side slot is `< 64`**: the chip's top limb of a 64-bit word is `< 2^22`; with
`kd < 2^16` and the slot a byte, `kd + 2^16·x` does not wrap, so `x < 64`. -/
theorem x_lt64 {tr : Trace Fp} {t r : Nat} {pub : List Fp} {kd x pv cv : Nat → Expr} {bw : List Nat}
    (hB : (leafBlock kd x pv cv).map (dec3 tr t r pub) = bw.map wlimbs) (hW : W64 bw) {u : Nat}
    (hu : u < 16) (hk : ev tr t r pub (kd u) < 2 ^ 16) (hx : ev tr t r pub (x u) < 256) :
    ev tr t r pub (x u) < 64 := by
  obtain ⟨a, b, he⟩ := leaf_third kd x pv cv u hu
  have h := congrArg (·[u]?) hB
  simp only [List.getElem?_map, he, Option.map_some] at h
  cases hb : bw[u]? with
  | none => simp [hb] at h
  | some w =>
    rw [hb] at h
    simp only [Option.map_some, Option.some.injEq, dec3, wlimbs, List.cons.injEq, and_true] at h
    have hw : w < 2 ^ 64 := by
      obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.1 hb
      rw [← h2]; exact hW _ (List.getElem_mem _)
    have e := h.2.2
    rw [ev_hadd, ev_hmul, show K 65536 = Expr.const 65536 from rfl, ev_const] at e
    simp only [Nat.reducePow, Nat.reduceMod] at e hw hk
    rw [Nat.mod_eq_of_lt (show 65536 * ev tr t r pub (x u) < P by omega),
      Nat.mod_eq_of_lt (show ev tr t r pub (kd u) + 65536 * ev tr t r pub (x u) < P by omega)] at e
    omega

theorem leafX_p (pp cp wr : Expr) (plx clx : Nat → Expr) (k : Nat) (hk : k < 4) :
    leafX pp cp wr plx clx (k + 1) = plx k := by
  unfold leafX LEN_CHUNKS
  rw [if_neg (by omega), if_pos (by omega)]; rfl

theorem leafX_c (pp cp wr : Expr) (plx clx : Nat → Expr) (k : Nat) (hk : k < 4) :
    leafX pp cp wr plx clx (k + 5) = clx k := by
  unfold leafX LEN_CHUNKS
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), show k + 5 - 1 - 4 = k by omega]

/-! ## `WSA` and `WSL` rows -/

section Rows
variable {D : Nat} {extra : List Table} {nb np : Nat} {tr : Trace Fp} {pub : List Fp}
  {compress : List Nat → List Nat → List Nat}
  (hH : Holds (fullAir D extra nb np) pub tr)
  (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH ∧ i.bus ≠ B_RNG)

theorem hx3 (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH ∧ i.bus ≠ B_RNG) :
    ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH :=
  fun T hT i hi => ⟨(hx T hT i hi).1, (hx T hT i hi).2.1, (hx T hT i hi).2.2.1⟩
theorem hxR (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH ∧ i.bus ≠ B_RNG) :
    ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RNG := fun T hT i hi => (hx T hT i hi).2.2.2

include hH in
/-- A `WSA` row's time is a tape time, `< 2^24` (premise `htape` on the `WRITE` sends). -/
theorem wsa_t (htape : ∀ m ∈ busList (fullAir D extra nb np) tr pub B_WRITE true, tn (m.getD 1 0) < 2 ^ 24)
    {r : Nat} (hr : r < tr.height 7) (hA : (Wsa.c "act").eval tr 7 r pub = 1) :
    ev tr 7 r pub (Wsa.c "t") < 2 ^ 24 := by
  have hi : rcv B_WRITE (Wsa.c "act") ([Wsa.c "seg", Wsa.c "t"] ++ Wsa.vec "kd" 16 ++ [Wsa.c "ncp", Wsa.c "ncl"] ++
      Wsa.vec "ncv" 16) ∈ ((fullAir D extra nb np).tables[7]!).interactions := by
    rw [full_wsa]
    exact List.mem_append_left _ (List.mem_cons_self ..)
  have h1 := mem_busList _ (by rw [full_len]; omega) hi hr (mult_one hA)
  have h2 := htape _ ((holds_perm hH B_WRITE).mem_iff.2 h1)
  simpa [Interaction.msgVal, rcv, tn, ev] using h2

include hH hx in
/-- **Every decoded access consumed an earlier time** (`WsCost.wsa_gap`). -/
theorem wsa_gap_rec (htape : ∀ m ∈ busList (fullAir D extra nb np) tr pub B_WRITE true, tn (m.getD 1 0) < 2 ^ 24) :
    ∀ a ∈ wsa tr pub, a.idp < a.t := by
  have hT : ∀ a ∈ wsa tr pub, a.t < 2 ^ 24 := by
    intro a ha
    obtain ⟨r, hr, hA, rfl⟩ := actRows_mem ha
    exact wsa_t hH htape hr hA
  intro a ha
  obtain ⟨r, hr, hA, rfl⟩ := actRows_mem ha
  have hm : (wsaRow tr pub r).rcvM ∈ wmSends (wsl tr pub) (wsa tr pub) :=
    (wm_traffic hH (hx3 hx)).mem_iff.2 (List.mem_append_right _ (List.mem_map.2 ⟨_, ha, rfl⟩))
  have hip : (wsaRow tr pub r).idp < 2 ^ 24 := by
    simp only [wmSends, List.mem_append, List.mem_map] at hm
    rcases hm with ⟨l, -, e⟩ | ⟨a', ha', e⟩
    · simp only [WslRow.openM, WsaRow.rcvM, WM.mk.injEq] at e
      omega
    · simp only [WsaRow.sndM, WsaRow.rcvM, WM.mk.injEq] at e
      have := hT a' ha'; omega
  have hc := holds_constr hH (t := 7) (by decide) full_wsa r hr
  have hdt : ∀ k < DT_BYTES, ev tr 7 r pub (Wsa.c "dt" k) < 256 := by
    intro k hk
    refine rng_rcv hH (hxR hx) (by rw [full_len]; omega) ?_ hr hA
    rw [full_wsa]
    exact List.mem_append_right _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩)
  exact WsCost.wsa_gap hc (eval_one_ev hA) hdt (hT _ ha) hip

include hH in
/-- The raw `WSP` rows: `RowF`, and at most `2^20` of them. -/
theorem wsp_rows (hD1 : 1 ≤ D) (hD : D ≤ 30) :
    (∀ x ∈ wspF tr pub, RowF D x) ∧ (wspF tr pub).length ≤ 2 ^ 20 := by
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨r, hr, hA, rfl⟩ := actRows_mem hx
    exact wsp_rowF (holds_constr hH (t := 11) (by decide) full_wsp r hr) hD1 hD (eval_one_ev hA)
  · refine Nat.le_trans actRows_length (Nat.pow_le_pow_right (by decide) ?_)
    exact holds_log hH (t := 11) (by decide) full_wsp

include hH hx in
/-- **A touched leaf is at a tree position and is a real entry**: `i < 2^D`, `i < wsLen`. -/
theorem wsl_ok (hD1 : 1 ≤ D) (hD : D ≤ 20) :
    ∀ l ∈ wsl tr pub, l.i < 2 ^ D ∧ l.i < WsLen.wsLen pub := by
  obtain ⟨hrow, hlen⟩ := wsp_rows hH hD1 (by omega)
  intro l hl
  have h1 := wsl_i_lt (pt_traffic hH (hx3 hx)) hrow hD hlen l hl
  refine ⟨h1, ?_⟩
  obtain ⟨r, hr, hA, rfl⟩ := actRows_mem hl
  have hc := holds_constr hH (t := 10) (by decide) full_wsl r hr
  have hix : ∀ k < IX_BYTES, ev tr 10 r pub (Wsl.c "ix" k) < 256 := by
    intro k hk
    refine rng_rcv hH (hxR hx) (by rw [full_len]; omega) ?_ hr hA
    rw [full_wsl]
    exact List.mem_append_right _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩)
  have h20 : 2 ^ D ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hD
  exact WsLen.wsl_lt_wsLen hc (eval_one_ev hA) hix (by simp only [wslRow] at h1; omega)

end Rows


/-! ## `WSL` leaf compressions -/

def wslOldB : List W3 :=
  leafBlock (fun t => Wsl.c "kd" t) (leafX (Wsl.c "pp") (Wsl.c "cp") (Wsl.c "wr") (fun k => Wsl.c "plx" k)
    (fun k => Wsl.c "clx" k)) (fun t => Wsl.c "pv" t) (fun t => Wsl.c "cv" t)
def wslNewB : List W3 :=
  leafBlock (fun t => Wsl.c "kd" t) (leafX (Wsl.c "pp") (Wsl.c "ncp") (Wsl.c "nwr") (fun k => Wsl.c "plx" k)
    (fun k => Wsl.c "nclx" k)) (fun t => Wsl.c "pv" t) (fun t => Wsl.c "ncv" t)

theorem leaf_dec {tr : Trace Fp} {t r : Nat} {pub : List Fp} (B : List W3) (o ox : Nat → Expr) :
    (ivW ++ B ++ digW o ++ wordsOf ox 2).map (dec3 tr t r pub) =
      IV384.map wlimbs ++ B.map (dec3 tr t r pub) ++ ((digW o).map (dec3 tr t r pub) ++ (wordsOf ox 2).map (dec3 tr t r pub)) := by
  simp only [List.map_append, ivW_dec, List.append_assoc]

section Leaf
variable {D : Nat} {extra : List Table} {nb np : Nat} {tr : Trace Fp} {pub : List Fp}
  {compress : List Nat → List Nat → List Nat}
  (hH : Holds (fullAir D extra nb np) pub tr)
  (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH ∧ i.bus ≠ B_RNG)
  (hcomp : CompressOK compress)
  (hC : Sha512IfContract compress ((busList (fullAir D extra nb np) tr pub B_IF384 true).map decIf))
include hH hx hcomp hC

/-- **A touched leaf's two leaf compressions**: its old / new digest is
`digest6 (compress IV384 bw)` of the 64-bit words `bw` whose limbs are its decoded old / new
block; the `kd` limbs are 16-bit and every length chunk is `< 64`. -/
theorem wsl_leaf {r : Nat} (hr : r < tr.height 10) (hA : (Wsl.c "act").eval tr 10 r pub = 1) :
    (∃ bw : List Nat, bw.length = 16 ∧ W64 bw ∧ wslOldB.map (dec3 tr 10 r pub) = bw.map wlimbs ∧
      (wslRow tr pub r).dgO = digest6 (compress IV384 bw)) ∧
    (∃ bw : List Nat, bw.length = 16 ∧ W64 bw ∧ wslNewB.map (dec3 tr 10 r pub) = bw.map wlimbs ∧
      (wslRow tr pub r).dgN = digest6 (compress IV384 bw)) ∧
    (∀ j < 16, ev tr 10 r pub (Wsl.c "kd" j) < 2 ^ 16) ∧
    (∀ k < LEN_CHUNKS, ev tr 10 r pub (Wsl.c "plx" k) < 64 ∧ ev tr 10 r pub (Wsl.c "clx" k) < 64 ∧
      ev tr 10 r pub (Wsl.c "nclx" k) < 64) := by
  have hperm := holds_perm hH B_IF384
  have hlt : 10 < (fullAir D extra nb np).tables.length := by rw [full_len]; omega
  have hc := holds_constr hH (t := 10) (by decide) full_wsl r hr
  have rng : ∀ e : Expr, rcv B_RNG (Wsl.c "act") [e] ∈ Wsl.interactions → ev tr 10 r pub e < 256 :=
    fun e he => rng_rcv hH (hxR hx) hlt (by rw [full_wsl]; exact he) hr hA
  have hkb : ∀ b < 32, ev tr 10 r pub (Wsl.c "kb" b) < 256 := fun b hb => rng _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.2 ⟨b, List.mem_range.2 hb, rfl⟩))))
  have hch : ∀ k < LEN_CHUNKS, ev tr 10 r pub (Wsl.c "plx" k) < 256 ∧ ev tr 10 r pub (Wsl.c "clx" k) < 256 ∧
      ev tr 10 r pub (Wsl.c "nclx" k) < 256 := by
    intro k hk
    have m : ∀ e, e ∈ [rcv B_RNG (Wsl.c "act") [Wsl.c "plx" k], rcv B_RNG (Wsl.c "act") [Wsl.c "clx" k],
        rcv B_RNG (Wsl.c "act") [Wsl.c "nclx" k]] → e ∈ Wsl.interactions := fun e he =>
      List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, he⟩))
    exact ⟨rng _ (m _ (by simp)), rng _ (m _ (by simp)), rng _ (m _ (by simp))⟩
  have hkd : ∀ j < 16, ev tr 10 r pub (Wsl.c "kd" j) < 2 ^ 16 := fun j hj => (WsCost.wsl_kd hc j hj hkb).2
  have hO : ∃ bw : List Nat, bw.length = 16 ∧ W64 bw ∧ wslOldB.map (dec3 tr 10 r pub) = bw.map wlimbs ∧
      (wslRow tr pub r).dgO = digest6 (compress IV384 bw) := by
    have hm := comp_mem hperm hlt (g := Wsl.c "act") (cid := Wsl.c "cidO")
      (ws := ivW ++ wslOldB ++ digW (fun t => Wsl.c "dgO" t) ++ wordsOf (fun t => Wsl.c "dxO" t) 2)
      (fun i hi => by
        rw [full_wsl]
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_append_left _ hi))))) hr hA
    rw [leaf_dec] at hm
    obtain ⟨bw, h16, hw, eB, eo⟩ := comp_iv hcomp hC (by simp [wslOldB, leafBlock]) (by simp [digW])
      (by simp [wordsOf]) hm
    exact ⟨bw, h16, hw, eB, rowDig_of eo⟩
  have hN : ∃ bw : List Nat, bw.length = 16 ∧ W64 bw ∧ wslNewB.map (dec3 tr 10 r pub) = bw.map wlimbs ∧
      (wslRow tr pub r).dgN = digest6 (compress IV384 bw) := by
    have hm := comp_mem hperm hlt (g := Wsl.c "act") (cid := Wsl.c "cidN")
      (ws := ivW ++ wslNewB ++ digW (fun t => Wsl.c "dgN" t) ++ wordsOf (fun t => Wsl.c "dxN" t) 2)
      (fun i hi => by
        rw [full_wsl]
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_append_right _ hi))))) hr hA
    rw [leaf_dec] at hm
    obtain ⟨bw, h16, hw, eB, eo⟩ := comp_iv hcomp hC (by simp [wslNewB, leafBlock]) (by simp [digW])
      (by simp [wordsOf]) hm
    exact ⟨bw, h16, hw, eB, rowDig_of eo⟩
  refine ⟨hO, hN, hkd, fun k hk => ?_⟩
  obtain ⟨bwO, -, hwO, eO, -⟩ := hO
  obtain ⟨bwN, -, hwN, eN, -⟩ := hN
  obtain ⟨c1, c2, c3⟩ := hch k hk
  have hk4 : k < 4 := hk
  have p1 := x_lt64 eO hwO (u := k + 1) (by omega) (hkd _ (by omega))
    (by rw [leafX_p _ _ _ _ _ k hk4]; exact c1)
  have p2 := x_lt64 eO hwO (u := k + 5) (by omega) (hkd _ (by omega))
    (by rw [leafX_c _ _ _ _ _ k hk4]; exact c2)
  have p3 := x_lt64 eN hwN (u := k + 5) (by omega) (hkd _ (by omega))
    (by rw [leafX_c _ _ _ _ _ k hk4]; exact c3)
  rw [leafX_p _ _ _ _ _ k hk4] at p1
  rw [leafX_c _ _ _ _ _ k hk4] at p2 p3
  exact ⟨p1, p2, p3⟩

end Leaf


/-! ## Assembly -/

theorem s0_seg {tr : Trace Fp} {pub : List Fp} : ∀ m ∈ s0 tr pub, m.1 = 0 := by
  intro m hm
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hm
  obtain ⟨r, -, hr⟩ := List.mem_filterMap.1 hv
  split at hr
  · cases hr; exact dec_wsnRS
  · cases hr

section Final
variable {D : Nat} {extra : List Table} {nb np : Nat} {tr : Trace Fp} {pub : List Fp}
  {compress : List Nat → List Nat → List Nat}
  (hH : Holds (fullAir D extra nb np) pub tr)
  (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH ∧ i.bus ≠ B_RNG)
  (hcomp : CompressOK compress)
  (hC : Sha512IfContract compress ((busList (fullAir D extra nb np) tr pub B_IF384 true).map decIf))
  (htape : ∀ m ∈ busList (fullAir D extra nb np) tr pub B_WRITE true, tn (m.getD 1 0) < 2 ^ 24)
  (hD1 : 1 ≤ D) (hD : D ≤ 20)
include hH hx hcomp hC htape hD1 hD

/-- **The working-set record premises from `Holds`.**  For the decoded `WSL` / `WSA` / `WSP`
rows: `PT` balance in `WsBus` form (no wrap-around), `WspOK` with `H = nodeH compress`, `WM`
balance, the per-access gap, touched leaves at tree positions and real entries, and — given the
`WSN` root messages `[(0, r0)]`, `[(nw, rF)]` — `RCH` balance in `WsBus` form. -/
theorem ws_decoded :
    (ptSends (wsl tr pub) (plain (wspF tr pub))).Perm (ptRecvs (plain (wspF tr pub))) ∧
    (∀ x ∈ plain (wspF tr pub), WspOK (nodeH compress) D x) ∧
    (wmSends (wsl tr pub) (wsa tr pub)).Perm (wmRecvs (wsl tr pub) (wsa tr pub)) ∧
    (∀ a ∈ wsa tr pub, a.idp < a.t) ∧
    (∀ l ∈ wsl tr pub, l.i < 2 ^ D ∧ l.i < WsLen.wsLen pub) ∧
    (∀ (r0 rF : Dig) (nw : Nat), s0 tr pub = [(0, r0)] → q0 tr pub = [(nw, rF)] →
      (rchSends r0 (plain (wspF tr pub))).Perm (rchRecvs nw rF (plain (wspF tr pub)))) := by
  obtain ⟨hrow, hlen⟩ := wsp_rows hH hD1 (by omega)
  have hpt := pt_traffic hH (hx3 hx)
  have hb := pos_bound hpt hrow hD hlen
  obtain ⟨e1, e2⟩ := pt_eq (wsl := wsl tr pub) hrow hD hb
  refine ⟨e1 ▸ e2 ▸ hpt, fun x hxm => ?_, wm_traffic hH (hx3 hx), wsa_gap_rec hH hx htape,
    wsl_ok hH hx hD1 hD, fun r0 rF nw h0 hq => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hxm
    exact wsp_ok hH hD1 (by omega) hcomp hC y hy
  · have hr := rch_traffic hH (hx3 hx)
    have hs := seg_lt hr hrow s0_seg
    rw [h0, hq] at hr
    obtain ⟨f1, f2⟩ := rch_eq hrow (fun x hxm ht => Nat.lt_of_lt_of_le (hs x hxm ht) hlen) r0 rF nw
    rw [f1, f2] at hr
    exact hr

/-- **The final working set, from `Holds`.**  With the `WSN` tree builds as premises (the decoded
`WSN` root messages are `[(0, r0)]` and `[(nw, rF)]`, `r0` the root of the INTAKE leaf list `ws0`,
`rF` the root of the FINAL leaf list `wsF`), SHA-384 node collision resistance (`NodeCR`) and
`hkd`, the conclusion of `WsSeg.ws_final` holds for the AIR's rows: `wsF` is `ws0` with each
touched index holding the new digest of its last touching `WSL` row (a leaf compression of the
row's new block: `wsl_leaf`), whose closing value is its entry's latest written value. -/
theorem ws_decoded_final (hCR : NodeCR compress) {ws0 wsF : List Dig} {r0 rF : Dig} {nw : Nat}
    (hs0 : s0 tr pub = [(0, r0)]) (hq0 : q0 tr pub = [(nw, rF)])
    (hlen0 : ws0.length = 2 ^ D) (hroot0 : root (nodeH compress) D ws0 = some r0)
    (hlenF : wsF.length = 2 ^ D) (hrootF : root (nodeH compress) D wsF = some rF)
    (hkd : ∀ l ∈ wsl tr pub, ∀ l' ∈ wsl tr pub, l.seg = l'.seg → l.kd = l'.kd → l.i = l'.i) :
    wsF = WsSeg.wsAt (wsl tr pub) ws0 nw ∧
    (∀ l ∈ wsl tr pub, l.seg < nw ∧ l.i < 2 ^ D ∧ (WsSeg.wsAt (wsl tr pub) ws0 l.seg)[l.i]? = some l.dgO ∧
        (WsSeg.wsAt (wsl tr pub) ws0 (l.seg + 1))[l.i]? = some l.dgN) ∧
    (∀ i, i < 2 ^ D → (∀ l ∈ wsl tr pub, l.i ≠ i) → wsF[i]? = ws0[i]?) ∧
    (∀ l ∈ wsl tr pub, (∀ l' ∈ wsl tr pub, l'.i = l.i → l'.seg ≤ l.seg) → wsF[l.i]? = some l.dgN) ∧
    (∀ l ∈ wsl tr pub, ∃ s : List (WsCost.Acc (List Nat)), s.Perm (accOf (wsa tr pub) l.key) ∧
      s.Pairwise (fun a b => b.t < a.t) ∧ l.ncur = WsCost.lastVal l.cur s ∧ l.idl = WsCost.lastT s ∧
      WsCost.Reads l.cur s) ∧
    (∀ a ∈ wsa tr pub, ∃ l ∈ wsl tr pub, l.key = a.key) ∧
    (∀ l ∈ wsl tr pub, l.i < WsLen.wsLen pub) := by
  obtain ⟨hpt, hok, hwm, hgap, hwl, hrch⟩ := ws_decoded hH hx hcomp hC htape hD1 hD
  have := WsSeg.ws_final hpt hok (hrch r0 rF nw hs0 hq0) hCR hlen0 hroot0 hlenF hrootF hwm hgap hkd
  exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2,
    fun l hl => (hwl l hl).2⟩

end Final

end StateM5a.WsDecode3
