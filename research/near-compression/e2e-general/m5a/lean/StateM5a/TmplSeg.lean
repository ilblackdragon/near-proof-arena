import StateM5a.WsDecode3
import StateM5a.WsSeg
import StateM5a.Tmpl
import StateM5a.TmplMerkle
import StateM5a.FieldWsx

/-!
# StateM5a.TmplSeg — B-T1b: the STATE segment template `m5tSeg` is sound (working-set part)

The M5a/M5b working-set theorems (`WsDecode2/3`, `WsSeg.ws_final`) are stated for `fullAir D extra`
(the M5a table list, decoders pinned to its indices `WSA = 7`, `RNG = 9`, `WSL = 10`, `WSP = 11`).
The segment template `m5tSeg D` has the same tables at other indices (`WSA = 1`, `WSL = 2`,
`WSP = 3`, `RNG = 4`, `WSX = 7`) and no `WSN`: its incoming / outgoing roots are `WSX`'s `RCH`
messages.  Here:

* **`reix`** — a re-indexed view of a trace (`(reix σ tr)` reads table `σ t` of `tr` at index `t`):
  `Expr.eval e (reix σ tr) t r = Expr.eval e tr (σ t) r` by `rfl`, so every row-level decoder and field
  lemma of the M5a stack (`wsl`, `wsa`, `wspF`, `wsp_rowF`, `WsCost.wsa_gap`, …) applies verbatim to
  the template's tables through `trS := reix sigSeg tr`.
* The template's own bus decomposition (`busList_seg`) and the four bus-level facts re-proved
  for it (`pt_traffic_seg`, `wm_traffic_seg`, **`rch_traffic_seg`**: `WSX` in place of `WSN`),
  the row facts (`wsa_gap_seg`, `wsl_ok_seg`, `wsp_ok_seg`, `wsp_rows_seg`) and the assembly
  **`ws_decoded_seg`** (= `WsDecode3.ws_decoded` for the template).
* **The `WSX` bus step** (`wsx_ext`, generic in the AIR and the table index, so it serves `m5tIF`
  too): from the constraints (`FieldWsx`) and the chip contract on `IF384`, the depth-24 public
  root is the `WSX` row-0 root extended by `24 − D` zero-sibling levels — `extUp H Z 0 (24 − D) a₀ =
  pubDig pub PUB_WSA` with `Z` the constant `Z_D` (`zD D`).
* **`m5tSeg_ws`** — the segment's soundness at digest level: for **every** depth-`D` working set
  `ws0` whose root is the incoming root, the working set after the segment (`wsAt`: every touched
  leaf replaced by its `WSL` row's new digest, `PT` / `WSP` batched update) has the outgoing root,
  each touched leaf's old digest is `ws0`'s leaf, and — given distinct key digests among a
  segment's touched leaves (`hkd`, the INTAKE-key property the IF proof establishes) — each closing
  value is its entry's latest write (`WM` chain).  **`seg_rin_rout`**: the same at lane E's depth 24
  (`R_in`, `R_out` public values, `ext_inj` under `NodeCR`).
-/

namespace StateM5a.TmplSeg

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.FieldRows StateM5a.FieldRows2 StateM5a.Sha512If
open StateM5a.WsDecode StateM5a.WsDecode2 StateM5a.WsDecode3 StateM5a.WsBus StateM5a.WsRaw StateM5a.Merkle

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## The template AIR and the re-indexed trace -/

/-- The segment template with the tables after it (the native chip stub, the execution side). -/
def segAir (D : Nat) (extra : List Table) (nb np : Nat) : Air :=
  { tables := (m5tSeg D).tables ++ extra, numBuses := nb, numPub := np }

/-- The template index of each M5a index the working-set decoders read. -/
def sigSeg : Nat → Nat
  | 7 => 1
  | 10 => 2
  | 11 => 3
  | 9 => 4
  | t => t

/-- Table `t` of `reix σ tr` is table `σ t` of `tr`. -/
def reix (σ : Nat → Nat) (tr : Trace Fp) : Trace Fp := ⟨fun t => tr.log (σ t), fun t => tr.cell (σ t)⟩

theorem eval_reix (σ : Nat → Nat) (tr : Trace Fp) (e : Expr) (t r : Nat) (pub : List Fp) :
    e.eval (reix σ tr) t r pub = e.eval tr (σ t) r pub := rfl

theorem height_reix (σ : Nat → Nat) (tr : Trace Fp) (t : Nat) : (reix σ tr).height t = tr.height (σ t) := rfl


section Seg
variable {D : Nat} {extra : List Table} {nb np : Nat}

theorem seg_len : (segAir D extra nb np).tables.length = 8 + extra.length := by
  simp [segAir, m5tSeg]; omega

theorem seg_get (k : Nat) (hk : k < 8) :
    (segAir D extra nb np).tables[k]! = (m5tSeg D).tables[k]! := by
  simp only [segAir]
  rw [getElem!_pos _ k (by simp [m5tSeg]; omega), getElem!_pos _ k (by simp [m5tSeg]; omega)]
  exact List.getElem_append_left (by simp [m5tSeg]; omega)

theorem seg_get_extra (k : Nat) (hk : 8 ≤ k) (hk' : k < 8 + extra.length) :
    (segAir D extra nb np).tables[k]! ∈ extra := by
  simp only [segAir]
  rw [getElem!_pos _ k (by simp [m5tSeg]; omega)]
  rw [List.getElem_append_right (by simp [m5tSeg]; omega)]
  exact List.getElem_mem _

theorem seg_wsa : (segAir D extra nb np).tables[1]! = Wsa.table := by rw [seg_get 1 (by decide)]; rfl
theorem seg_wsl : (segAir D extra nb np).tables[2]! = Wsl.table := by rw [seg_get 2 (by decide)]; rfl
theorem seg_wsp : (segAir D extra nb np).tables[3]! = Wsp.table D := by rw [seg_get 3 (by decide)]; rfl
theorem seg_rng : (segAir D extra nb np).tables[4]! = Rng.table := by rw [seg_get 4 (by decide)]; rfl
theorem seg_wsx : (segAir D extra nb np).tables[7]! = Wsx.tableSeg D := by rw [seg_get 7 (by decide)]; rfl

theorem seg_constr {pub : List Fp} {tr : Trace Fp} (hH : Holds (segAir D extra nb np) pub tr)
    {t : Nat} (ht : t < 8) {T : Table} (hT : (segAir D extra nb np).tables[t]! = T) :
    ∀ r, r < tr.height t → ∀ e ∈ T.constraints, e.eval tr t r pub = 0 := by
  intro r hr e he
  have h := hH.constr t (by rw [seg_len]; omega) r hr e
  rw [← getElem!_pos _ t (by rw [seg_len]; omega), hT] at h
  exact h he

theorem seg_log {pub : List Fp} {tr : Trace Fp} (hH : Holds (segAir D extra nb np) pub tr)
    {t : Nat} (ht : t < 8) {T : Table} (hT : (segAir D extra nb np).tables[t]! = T) :
    tr.log t ≤ T.maxLog := by
  have h := (hH.logBound t (by rw [seg_len]; omega)).2
  rw [← getElem!_pos _ t (by rw [seg_len]; omega), hT] at h
  exact h

end Seg

/-! ## The template's working-set buses -/

theorem wsx_wm (s : Bool) : fl Wsx.interactionsSeg B_WM s = [] := by cases s <;> rfl
theorem wsx_pt (s : Bool) : fl Wsx.interactionsSeg B_PT s = [] := by cases s <;> rfl
theorem wsx_rs : fl Wsx.interactionsSeg B_RCH true = [snd B_RCH .isFirst (0 :: Wsx.vec "a" 18)] := by rfl
theorem wsx_rr : fl Wsx.interactionsSeg B_RCH false = [rcv B_RCH .isFirst (Wsx.c "sb" :: Wsx.vec "b" 18)] := by rfl

theorem nb_seg (b : Nat) (hb : WsBusN b) :
    noBus shaTable.interactions b = true ∧ noBus Rng.table.interactions b = true ∧
    noBus Stb.table.interactions b = true ∧ noBus Stw.table.interactions b = true := by
  rcases hb with rfl | rfl | rfl <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **The working-set buses' lists of the segment template**: only `WSA` (1), `WSL` (2), `WSP` (3),
`WSX` (7). -/
theorem busList_seg {tr : Trace Fp} {pub : List Fp} (D : Nat) (extra : List Table) (nb np : Nat)
    (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH)
    (b : Nat) (s : Bool) (hb : WsBusN b) :
    busList (segAir D extra nb np) tr pub b s =
      tableBusList Wsa.interactions tr 1 pub b s ++ tableBusList Wsl.interactions tr 2 pub b s ++
        tableBusList Wsp.interactions tr 3 pub b s ++ tableBusList Wsx.interactionsSeg tr 7 pub b s := by
  have ext := busList_extend (m5tSeg D) extra nb np tr pub b s (fun T hT i hi ⟨e, _⟩ => by
    obtain ⟨h1, h2, h3⟩ := hx T hT i hi
    rcases hb with rfl | rfl | rfl <;> simp_all)
  simp only [segAir]
  rw [ext]
  obtain ⟨n1, n2, n3, n4⟩ := nb_seg b hb
  simp only [busList, m5tSeg, busList.go]
  rw [tbl_nil n1, tbl_nil (is := Rng.table.interactions) n2, tbl_nil (is := Stb.table.interactions) n3,
    tbl_nil (is := Stw.table.interactions) n4]
  simp only [Wsa.table, Wsl.table, Wsp.table, Wsx.tableSeg, List.nil_append, List.append_nil,
    List.append_assoc]

/-! ## Decoded traffic on the template -/

section Traffic
variable {D : Nat} {extra : List Table} {nb np : Nat} {tr : Trace Fp} {pub : List Fp}
  (hH : Holds (segAir D extra nb np) pub tr)
  (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH)
include hH

/-- The template trace in the M5a indices. -/
abbrev trS (tr : Trace Fp) : Trace Fp := reix sigSeg tr

theorem wsp_hc_seg : ∀ r, r < (trS tr).height 11 → ∀ e ∈ (Wsp.table D).constraints, e.eval (trS tr) 11 r pub = 0 :=
  seg_constr hH (by decide) seg_wsp

include hx

theorem busList_segS (b : Nat) (s : Bool) (hb : WsBusN b) :
    busList (segAir D extra nb np) tr pub b s =
      tableBusList Wsa.interactions (trS tr) 7 pub b s ++ tableBusList Wsl.interactions (trS tr) 10 pub b s ++
        tableBusList Wsp.interactions (trS tr) 11 pub b s ++ tableBusList Wsx.interactionsSeg tr 7 pub b s :=
  busList_seg D extra nb np hx b s hb

/-- **`PT` balance, decoded** (template). -/
theorem pt_traffic_seg : (ptSendsF (wsl (trS tr) pub) (wspF (trS tr) pub)).Perm (ptRecvsF (wspF (trS tr) pub)) := by
  have hc := wsp_hc_seg hH (D := D)
  have hp := (holds_perm hH B_PT).map decPT
  rw [busList_segS hH hx B_PT true (Or.inr (Or.inl rfl)), busList_segS hH hx B_PT false (Or.inr (Or.inl rfl)),
    tbl_nil' (wsa_pt true), tbl_one _ _ _ _ _ wsl_pts, tbl_one _ _ _ _ _ wsp_pts, tbl_nil' (wsx_pt true),
    tbl_nil' (wsa_pt false), tbl_nil' wsl_ptr, tbl_two _ _ _ _ _ 11 _ _ wsp_ptr, tbl_nil' (wsx_pt false)] at hp
  simp only [List.nil_append, List.append_nil, List.map_append] at hp
  have hp2 := hp.trans ((sel2_perm _ _ _ _).map decPT)
  rw [List.map_append] at hp2
  have e1 := sel_dec (tr := trS tr) (t := 10) (pub := pub) (Wsl.c "act") (Wsl.c "act") wslPT (wslRow (trS tr) pub)
    (fun _ => true) decPT WslRow.ptM (List.range ((trS tr).height 10)) (fun r _ => by simp) (fun r _ _ _ => dec_wslPT)
  have e2 := sel_dec (tr := trS tr) (t := 11) (pub := pub) (Wsp.c "act" - Wsp.c "top") (Wsp.c "act") wspO
    (wspRow (trS tr) pub) (fun x => !x.r.top) decPT WspF.outM (List.range ((trS tr).height 11))
    (fun r hr => wsp_m_out (hc r (List.mem_range.1 hr))) (fun r _ _ _ => dec_wspO)
  have e3 := sel_dec (tr := trS tr) (t := 11) (pub := pub) (Wsp.c "tl") (Wsp.c "act") wspL
    (wspRow (trS tr) pub) (fun x => x.r.tl) decPT WspF.inL (List.range ((trS tr).height 11))
    (fun r hr => wsp_m_tl (hc r (List.mem_range.1 hr))) (fun r _ _ _ => dec_wspL)
  have e4 := sel_dec (tr := trS tr) (t := 11) (pub := pub) (Wsp.c "tr") (Wsp.c "act") wspR
    (wspRow (trS tr) pub) (fun x => x.r.tr) decPT WspF.inR (List.range ((trS tr).height 11))
    (fun r hr => wsp_m_tr (hc r (List.mem_range.1 hr))) (fun r _ _ _ => dec_wspR)
  rw [e1, e2, e3, e4, filter_tt] at hp2
  exact hp2

/-- **`WM` balance, decoded** (template). -/
theorem wm_traffic_seg : (wmSends (wsl (trS tr) pub) (wsa (trS tr) pub)).Perm (wmRecvs (wsl (trS tr) pub) (wsa (trS tr) pub)) := by
  have hp := (holds_perm hH B_WM).map decWM
  rw [busList_segS hH hx B_WM true (Or.inl rfl), busList_segS hH hx B_WM false (Or.inl rfl),
    tbl_one _ _ _ _ _ wsa_ws, tbl_one _ _ _ _ _ wsl_ws, tbl_nil' (wsp_wm true), tbl_nil' (wsx_wm true),
    tbl_one _ _ _ _ _ wsa_wr, tbl_one _ _ _ _ _ wsl_wr, tbl_nil' (wsp_wm false), tbl_nil' (wsx_wm false)] at hp
  simp only [List.nil_append, List.append_nil, List.map_append] at hp
  have e1 := sel_dec (tr := trS tr) (t := 7) (pub := pub) (Wsa.c "act") (Wsa.c "act") wsaWS (wsaRow (trS tr) pub)
    (fun _ => true) decWM WsaRow.sndM (List.range ((trS tr).height 7)) (fun r _ => by simp) (fun r _ _ _ => dec_wsaWS)
  have e2 := sel_dec (tr := trS tr) (t := 10) (pub := pub) (Wsl.c "act") (Wsl.c "act") wslWS (wslRow (trS tr) pub)
    (fun _ => true) decWM WslRow.openM (List.range ((trS tr).height 10)) (fun r _ => by simp) (fun r _ _ _ => dec_wslWS)
  have e3 := sel_dec (tr := trS tr) (t := 7) (pub := pub) (Wsa.c "act") (Wsa.c "act") wsaWR (wsaRow (trS tr) pub)
    (fun _ => true) decWM WsaRow.rcvM (List.range ((trS tr).height 7)) (fun r _ => by simp) (fun r _ _ _ => dec_wsaWR)
  have e4 := sel_dec (tr := trS tr) (t := 10) (pub := pub) (Wsl.c "act") (Wsl.c "act") wslWR (wslRow (trS tr) pub)
    (fun _ => true) decWM WslRow.closeM (List.range ((trS tr).height 10)) (fun r _ => by simp) (fun r _ _ _ => dec_wslWR)
  rw [e1, e2, e3, e4] at hp
  simp only [filter_tt] at hp
  exact List.perm_append_comm.trans (hp.trans List.perm_append_comm)

end Traffic

/-! ## `WSX`'s row-0 messages -/

section First
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem selL_first (msg : List Expr) :
    selL tr t pub .isFirst msg (List.range (tr.height t)) = [vals tr t 0 pub msg] := by
  have h0 : 0 < tr.height t := Nat.two_pow_pos _
  obtain ⟨k, hk⟩ : ∃ k, tr.height t = k + 1 := ⟨tr.height t - 1, by omega⟩
  rw [hk, List.range_succ_eq_map]
  have e0 : (Expr.isFirst).eval tr t 0 pub = 1 := ev_one_eval (by rw [FieldWsb.ev_isFirst]; rfl)
  have hz : ∀ r, ¬ (Expr.isFirst).eval tr t (r + 1) pub = 1 := by
    intro r h
    have := eval_one_ev h
    rw [FieldWsb.ev_isFirst] at this
    simp at this
  simp [selL, e0, hz]
  exact fun a _ h => absurd (congrArg Fp.toNat h) (by decide)

/-- The digest a `WSX` column group holds on row `r`. -/
def wsxDig (s : String) (r : Nat) : Dig := rowDig tr t r pub (fun j => Wsx.c s j)

theorem decR_wsx (s : String) (x : Expr) :
    decR (vals tr t 0 pub (x :: Wsx.vec s 18)) = (ev tr t 0 pub x, wsxDig (tr := tr) (t := t) (pub := pub) s 0) := by
  simp only [decR, vals, List.map_cons, List.getD_cons_zero, List.drop_succ_cons, List.drop_zero]
  refine Prod.ext rfl ?_
  show digOf (List.take 18 (vals tr t 0 pub (Wsx.vec s 18))) = _
  rw [List.take_of_length_le (by simp [vals, Wsx.vec])]
  exact digOf_vec _

end First

section Rch
variable {D : Nat} {extra : List Table} {nb np : Nat} {tr : Trace Fp} {pub : List Fp}
  (hH : Holds (segAir D extra nb np) pub tr)
  (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH)
include hH hx

/-- **`RCH` balance, decoded** (template): `WSX` sends the incoming root `(0, a₀)` and receives the
outgoing `(sb₀, b₀)`, in place of `WSN`'s INTAKE / FINAL roots. -/
theorem rch_traffic_seg :
    (rchSendsF [(0, wsxDig (tr := tr) (t := 7) (pub := pub) "a" 0)] (wspF (trS tr) pub)).Perm
      (rchRecvsF [(ev tr 7 0 pub (Wsx.c "sb"), wsxDig (tr := tr) (t := 7) (pub := pub) "b" 0)] (wspF (trS tr) pub)) := by
  have hc := wsp_hc_seg hH (D := D)
  have hp := (holds_perm hH B_RCH).map decR
  rw [busList_segS hH hx B_RCH true (Or.inr (Or.inr rfl)), busList_segS hH hx B_RCH false (Or.inr (Or.inr rfl)),
    tbl_nil' (wsa_rch true), tbl_nil' (wsl_rch true), tbl_one _ _ _ _ _ wsp_rs, tbl_one _ _ _ _ _ wsx_rs,
    tbl_nil' (wsa_rch false), tbl_nil' (wsl_rch false), tbl_one _ _ _ _ _ wsp_rr, tbl_one _ _ _ _ _ wsx_rr,
    selL_first, selL_first] at hp
  simp only [List.nil_append, List.append_nil, List.map_append, List.map_cons, List.map_nil] at hp
  have e1 := sel_dec (tr := trS tr) (t := 11) (pub := pub) (Wsp.c "top") (Wsp.c "act") wspRS
    (wspRow (trS tr) pub) (fun x => x.r.top) decR (fun x => (x.seg1, x.r.on)) (List.range ((trS tr).height 11))
    (fun r hr => wsp_m_top (hc r (List.mem_range.1 hr))) (fun r _ _ _ => dec_wspRS)
  have e2 := sel_dec (tr := trS tr) (t := 11) (pub := pub) (Wsp.c "top") (Wsp.c "act") wspRR
    (wspRow (trS tr) pub) (fun x => x.r.top) decR (fun x => (x.r.seg, x.r.oo)) (List.range ((trS tr).height 11))
    (fun r hr => wsp_m_top (hc r (List.mem_range.1 hr))) (fun r _ _ _ => dec_wspRR)
  rw [e1, e2, decR_wsx, decR_wsx] at hp
  have e0 : ev tr 7 0 pub (0 : Expr) = 0 := ev_const (tr := tr) (t := 7) (r := 0) (pub := pub) 0
  rw [e0] at hp
  exact List.perm_append_comm.trans (hp.trans List.perm_append_comm)

end Rch

/-! ## Row facts on the template -/

section Rows
variable {D : Nat} {extra : List Table} {nb np : Nat} {tr : Trace Fp} {pub : List Fp}
  {compress : List Nat → List Nat → List Nat}
  (hH : Holds (segAir D extra nb np) pub tr)
  (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH ∧ i.bus ≠ B_RNG)

theorem ns_seg (D k : Nat) (hk : k < 8) (h4 : k ≠ 4) : noSnd ((m5tSeg D).tables[k]!).interactions B_RNG = true := by
  have e : ((m5tSeg D).tables[k]!).interactions = ((m5tSeg 0).tables[k]!).interactions := by
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;> first | rfl | omega
  rw [e]
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;> first | decide | omega

include hH in
/-- **Every `RNG` value is a byte** (template). -/
theorem rng_send_lt_seg (hxr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RNG) {m : List Fp}
    (hm : m ∈ busList (segAir D extra nb np) tr pub B_RNG true) : tn (m.getD 0 0) < 256 := by
  obtain ⟨t, ht, r, hr, i, hi, hb, hs, rfl⟩ := busList_inv _ hm
  rw [seg_len] at ht
  by_cases h8 : t < 8
  · by_cases h4 : t = 4
    · subst h4
      rw [seg_rng] at hi
      have hc := seg_constr hH (by decide) (seg_rng (D := D) (extra := extra) (nb := nb) (np := np))
      have hl := seg_log hH (by decide) (seg_rng (D := D) (extra := extra) (nb := nb) (np := np))
      have hv := rng_v (tr := reix (fun _ => 4) tr) hc hl r hr
      have hH8 : tr.height 4 ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) hl
      simp only [Rng.table, Rng.interactions, List.mem_singleton] at hi
      subst hi
      simp only [Interaction.msgVal, sndBits, List.map_cons, List.map_nil, List.getD_cons_zero]
      show ev tr 4 r pub (Rng.c "v") < 256
      have : ev tr 4 r pub (Rng.c "v") = r := hv
      omega
    · rw [seg_get t h8] at hi
      exact absurd (noSnd_spec (ns_seg D t h8 h4) hi hb hs) id
  · exact absurd hb (hxr _ (seg_get_extra t (by omega) ht) i hi)

include hH in
theorem rng_rcv_seg (hxr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RNG) {t : Nat}
    (ht : t < (segAir D extra nb np).tables.length) {g e : Expr}
    (hi : rcv B_RNG g [e] ∈ ((segAir D extra nb np).tables[t]!).interactions) {r : Nat}
    (hr : r < tr.height t) (hg : g.eval tr t r pub = 1) : ev tr t r pub e < 256 := by
  have h1 := mem_busList (segAir D extra nb np) ht hi hr (mult_one hg)
  have h2 := (holds_perm hH B_RNG).mem_iff.2 h1
  exact rng_send_lt_seg hH hxr h2

include hH hx in
theorem wsa_t_seg {r : Nat} (hr : r < (trS tr).height 7) (hA : (Wsa.c "act").eval (trS tr) 7 r pub = 1) :
    ev (trS tr) 7 r pub (Wsa.c "t") < 2 ^ 24 := by
  have hc := seg_constr hH (t := 1) (by decide) seg_wsa r hr
  have htb : ∀ k < TB_BYTES, ev tr 1 r pub (Wsa.c "tb" k) < 256 := by
    intro k hk
    refine rng_rcv_seg hH (hxR hx) (by rw [seg_len]; omega) ?_ hr hA
    rw [seg_wsa]
    exact List.mem_append_right _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩)
  exact WsCost.wsa_t_lt hc (eval_one_ev hA) htb

include hH hx in
/-- **Every decoded access consumed an earlier time** (template). -/
theorem wsa_gap_seg : ∀ a ∈ wsa (trS tr) pub, a.idp < a.t := by
  have hT : ∀ a ∈ wsa (trS tr) pub, a.t < 2 ^ 24 := by
    intro a ha
    obtain ⟨r, hr, hA, rfl⟩ := actRows_mem ha
    exact wsa_t_seg hH hx hr hA
  intro a ha
  obtain ⟨r, hr, hA, rfl⟩ := actRows_mem ha
  have hm : (wsaRow (trS tr) pub r).rcvM ∈ wmSends (wsl (trS tr) pub) (wsa (trS tr) pub) :=
    (wm_traffic_seg hH (hx3 hx)).mem_iff.2 (List.mem_append_right _ (List.mem_map.2 ⟨_, ha, rfl⟩))
  have hip : (wsaRow (trS tr) pub r).idp < 2 ^ 24 := by
    simp only [wmSends, List.mem_append, List.mem_map] at hm
    rcases hm with ⟨l, -, e⟩ | ⟨a', ha', e⟩
    · simp only [WslRow.openM, WsaRow.rcvM, WM.mk.injEq] at e
      omega
    · simp only [WsaRow.sndM, WsaRow.rcvM, WM.mk.injEq] at e
      have := hT a' ha'; omega
  have hc := seg_constr hH (t := 1) (by decide) seg_wsa r hr
  have hdt : ∀ k < DT_BYTES, ev tr 1 r pub (Wsa.c "dt" k) < 256 := by
    intro k hk
    refine rng_rcv_seg hH (hxR hx) (by rw [seg_len]; omega) ?_ hr hA
    rw [seg_wsa]
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩))
  exact WsCost.wsa_gap hc (eval_one_ev hA) hdt (hT _ ha) hip

include hH in
theorem wsp_rows_seg (hD1 : 1 ≤ D) (hD : D ≤ 30) :
    (∀ x ∈ wspF (trS tr) pub, RowF D x) ∧ (wspF (trS tr) pub).length ≤ 2 ^ 20 := by
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨r, hr, hA, rfl⟩ := actRows_mem hx
    exact wsp_rowF (seg_constr hH (t := 3) (by decide) seg_wsp r hr) hD1 hD (eval_one_ev hA)
  · refine Nat.le_trans actRows_length (Nat.pow_le_pow_right (by decide) ?_)
    exact seg_log hH (t := 3) (by decide) seg_wsp

include hH hx in
theorem wsl_ok_seg (hD1 : 1 ≤ D) (hD : D ≤ 20) :
    ∀ l ∈ wsl (trS tr) pub, l.i < 2 ^ D ∧ l.i < WsLen.wsLen pub := by
  obtain ⟨hrow, hlen⟩ := wsp_rows_seg hH hD1 (by omega)
  intro l hl
  have h1 := wsl_i_lt (pt_traffic_seg hH (hx3 hx)) hrow hD hlen l hl
  refine ⟨h1, ?_⟩
  obtain ⟨r, hr, hA, rfl⟩ := actRows_mem hl
  have hc := seg_constr hH (t := 2) (by decide) seg_wsl r hr
  have hix : ∀ k < IX_BYTES, ev tr 2 r pub (Wsl.c "ix" k) < 256 := by
    intro k hk
    refine rng_rcv_seg hH (hxR hx) (by rw [seg_len]; omega) ?_ hr hA
    rw [seg_wsl]
    exact List.mem_append_right _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩)
  have h20 : 2 ^ D ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hD
  exact WsLen.wsl_lt_wsLen hc (eval_one_ev hA) hix (by simp only [wslRow] at h1; omega)

end Rows

/-! ## Node compressions on any AIR -/

section Node
variable {A : Air} {tr : Trace Fp} {pub : List Fp} {compress : List Nat → List Nat → List Nat}

/-- One node compression of a row (any AIR, any table): its output digest is `nodeH` of the inputs. -/
theorem node_comp (hcomp : CompressOK compress)
    (hC : Sha512IfContract compress ((busList A tr pub B_IF384 true).map decIf))
    (hperm : (busList A tr pub B_IF384 true).Perm (busList A tr pub B_IF384 false))
    {t : Nat} (ht : t < A.tables.length) {g : Expr}
    {r : Nat} (hr : r < tr.height t) (hA : g.eval tr t r pub = 1) {cid : Expr} {l rr o ox : Nat → Expr}
    (hsub : ∀ i ∈ comp g cid (ivW ++ nodeBlock (digW l) (digW rr) ++ digW o ++ wordsOf ox 2),
      i ∈ (A.tables[t]!).interactions) :
    rowDig tr t r pub o = nodeH compress (rowDig tr t r pub l) (rowDig tr t r pub rr) := by
  have hm := comp_mem hperm ht hsub hr hA
  rw [node_dec] at hm
  obtain ⟨dl, dr, el, er, eo⟩ := comp_node hcomp hC (by simp [digW]) (by simp [digW]) (by simp [digW])
    (by simp [wordsOf]) hm
  rw [rowDig_of eo, rowDig_of el, rowDig_of er]

end Node

section Ok
variable {D : Nat} {extra : List Table} {nb np : Nat} {tr : Trace Fp} {pub : List Fp}
  {compress : List Nat → List Nat → List Nat}

/-- **Every decoded `WSP` row of the template satisfies `WspOK`.** -/
theorem wsp_ok_seg (hH : Holds (segAir D extra nb np) pub tr) (hD1 : 1 ≤ D) (hD : D ≤ 30)
    (hcomp : CompressOK compress)
    (hC : Sha512IfContract compress ((busList (segAir D extra nb np) tr pub B_IF384 true).map decIf)) :
    ∀ x ∈ wspF (trS tr) pub, WspOK (nodeH compress) D x.r := by
  intro x hx
  obtain ⟨r, hr, hA, rfl⟩ := actRows_mem hx
  have hc := seg_constr hH (t := 3) (by decide) seg_wsp r hr
  have hperm := holds_perm hH B_IF384
  have hA' := eval_one_ev hA
  have hbl := ev_bool (hold rfl hc (WsCost.wsp_mem (D := D) "tl" (by simp)))
  have hbr := ev_bool (hold rfl hc (WsCost.wsp_mem (D := D) "tr" (by simp)))
  have hsubO : ∀ i ∈ comp (Wsp.c "act") (Wsp.c "cidO")
      (ivW ++ nodeBlock (digW fun t => Wsp.c "lo" t) (digW fun t => Wsp.c "ro" t) ++ digW (fun t => Wsp.c "oo" t) ++
        wordsOf (fun t => Wsp.c "oox" t) 2), i ∈ ((segAir D extra nb np).tables[3]!).interactions := by
    intro i hi; rw [seg_wsp]; exact List.mem_append_left _ (List.mem_append_right _ hi)
  have hsubN : ∀ i ∈ comp (Wsp.c "act") (Wsp.c "cidN")
      (ivW ++ nodeBlock (digW fun t => Wsp.c "ln" t) (digW fun t => Wsp.c "rn" t) ++ digW (fun t => Wsp.c "on" t) ++
        wordsOf (fun t => Wsp.c "onx" t) 2), i ∈ ((segAir D extra nb np).tables[3]!).interactions := by
    intro i hi; rw [seg_wsp]; exact List.mem_append_right _ hi
  refine ⟨fun h => ?_, fun h => ?_, ?_, ?_, fun h => ?_, fun h => ?_⟩
  · have h0 : ev tr 3 r pub (Wsp.c "tl") = 0 := by
      simp only [wspRow, decide_eq_false_iff_not] at h; exact by
        rcases hbl with e | e
        · exact e
        · exact absurd e h
    exact rowDig_congr fun j hj => (WsCost.wsp_keep hc j hj).1 h0
  · have h0 : ev tr 3 r pub (Wsp.c "tr") = 0 := by
      simp only [wspRow, decide_eq_false_iff_not] at h; exact by
        rcases hbr with e | e
        · exact e
        · exact absurd e h
    exact rowDig_congr fun j hj => (WsCost.wsp_keep hc j hj).2 h0
  · exact node_comp (t := 3) hcomp hC hperm (by rw [seg_len]; omega) hr hA hsubO
  · exact node_comp (t := 3) hcomp hC hperm (by rw [seg_len]; omega) hr hA hsubN
  · exact (wsp_rowF hc hD1 hD hA').topLvl h
  · exact (wsp_rowF hc hD1 hD hA').topIdx h

end Ok

/-! ## The assembly: `ws_decoded` for the segment template -/

section Assembly
variable {D : Nat} {extra : List Table} {nb np : Nat} {tr : Trace Fp} {pub : List Fp}
  {compress : List Nat → List Nat → List Nat}
  (hH : Holds (segAir D extra nb np) pub tr)
  (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH ∧ i.bus ≠ B_RNG)
  (hcomp : CompressOK compress)
  (hC : Sha512IfContract compress ((busList (segAir D extra nb np) tr pub B_IF384 true).map decIf))
  (hD1 : 1 ≤ D) (hD : D ≤ 20)
include hH hx hcomp hC hD1 hD

/-- **`ws_decoded` for the segment template**: `PT` balance, `WspOK` rows, `WM` balance, the gap,
touched leaves at real tree positions, and `RCH` in `WsBus` form between `WSX`'s incoming root
`a₀` and outgoing root `b₀` (segment count `sb₀`). -/
theorem ws_decoded_seg :
    (ptSends (wsl (trS tr) pub) (plain (wspF (trS tr) pub))).Perm (ptRecvs (plain (wspF (trS tr) pub))) ∧
    (∀ x ∈ plain (wspF (trS tr) pub), WspOK (nodeH compress) D x) ∧
    (wmSends (wsl (trS tr) pub) (wsa (trS tr) pub)).Perm (wmRecvs (wsl (trS tr) pub) (wsa (trS tr) pub)) ∧
    (∀ a ∈ wsa (trS tr) pub, a.idp < a.t) ∧
    (∀ l ∈ wsl (trS tr) pub, l.i < 2 ^ D ∧ l.i < WsLen.wsLen pub) ∧
    (rchSends (wsxDig (tr := tr) (t := 7) (pub := pub) "a" 0) (plain (wspF (trS tr) pub))).Perm
      (rchRecvs (ev tr 7 0 pub (Wsx.c "sb")) (wsxDig (tr := tr) (t := 7) (pub := pub) "b" 0)
        (plain (wspF (trS tr) pub))) := by
  obtain ⟨hrow, hlen⟩ := wsp_rows_seg hH hD1 (by omega)
  have hpt := pt_traffic_seg hH (hx3 hx)
  have hb := pos_bound hpt hrow hD hlen
  obtain ⟨e1, e2⟩ := pt_eq (wsl := wsl (trS tr) pub) hrow hD hb
  refine ⟨e1 ▸ e2 ▸ hpt, fun x hxm => ?_, wm_traffic_seg hH (hx3 hx), wsa_gap_seg hH hx,
    wsl_ok_seg hH hx hD1 hD, ?_⟩
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hxm
    exact wsp_ok_seg hH hD1 (by omega) hcomp hC y hy
  · have hr := rch_traffic_seg hH (hx3 hx)
    have hs := seg_lt hr hrow (fun m hm => by simp at hm; rw [hm])
    obtain ⟨f1, f2⟩ := rch_eq hrow (fun x hxm ht => Nat.lt_of_lt_of_le (hs x hxm ht) hlen)
      (wsxDig (tr := tr) (t := 7) (pub := pub) "a" 0) (wsxDig (tr := tr) (t := 7) (pub := pub) "b" 0)
      (ev tr 7 0 pub (Wsx.c "sb"))
    rw [f1, f2] at hr
    exact hr

/-- **The segment's working-set step** (digest level).  For every depth-`D` working set `ws0` (leaf
digests) whose root is `WSX`'s incoming root `a₀`, the working set after the segment —
`WsSeg.wsAt (wsl trS) ws0 nw`, each touched leaf replaced by its `WSL` row's new digest — has the
outgoing root `b₀`; every touched leaf is a real entry at a tree position whose old digest is the
working set's leaf before its (internal) segment; and, given distinct key digests among a segment's
touched leaves (`hkd`), each closing value is its entry's latest write of the segment (accesses
time-sorted, each reading its predecessor: offline memory checking). -/
theorem m5tSeg_ws (hCR : NodeCR compress) {ws0 : List Dig} (hlen0 : ws0.length = 2 ^ D)
    (hroot0 : root (nodeH compress) D ws0 = some (wsxDig (tr := tr) (t := 7) (pub := pub) "a" 0)) :
    let nw := ev tr 7 0 pub (Wsx.c "sb")
    root (nodeH compress) D (WsSeg.wsAt (wsl (trS tr) pub) ws0 nw) = some (wsxDig (tr := tr) (t := 7) (pub := pub) "b" 0) ∧
    (∀ l ∈ wsl (trS tr) pub, l.seg < nw ∧ l.i < 2 ^ D ∧ l.i < WsLen.wsLen pub ∧
      (WsSeg.wsAt (wsl (trS tr) pub) ws0 l.seg)[l.i]? = some l.dgO ∧
      (WsSeg.wsAt (wsl (trS tr) pub) ws0 (l.seg + 1))[l.i]? = some l.dgN) ∧
    ((∀ l ∈ wsl (trS tr) pub, ∀ l' ∈ wsl (trS tr) pub, l.seg = l'.seg → l.kd = l'.kd → l.i = l'.i) →
      (∀ l ∈ wsl (trS tr) pub, ∃ s : List (WsCost.Acc (List Nat)), s.Perm (accOf (wsa (trS tr) pub) l.key) ∧
        s.Pairwise (fun a b => b.t < a.t) ∧ l.ncur = WsCost.lastVal l.cur s ∧ l.idl = WsCost.lastT s ∧
        WsCost.Reads l.cur s) ∧
      (∀ a ∈ wsa (trS tr) pub, ∃ l ∈ wsl (trS tr) pub, l.key = a.key)) := by
  intro nw
  obtain ⟨hpt, hok, hwm, hgap, hwl, hrch⟩ := ws_decoded_seg hH hx hcomp hC hD1 hD
  obtain ⟨hlF, hrt, hT⟩ := WsSeg.ws_compose hpt hok hrch hCR hlen0 hroot0 (wsl := wsl (trS tr) pub)
  refine ⟨hrt, fun l hl => ?_, fun hkd => ?_⟩
  · obtain ⟨a, b, c, d⟩ := hT l hl
    exact ⟨a, b, (hwl l hl).2, c, d⟩
  · have := WsSeg.ws_final hpt hok hrch hCR hlen0 hroot0 hlF hrt hwm hgap hkd
    exact ⟨this.2.2.2.2.1, this.2.2.2.2.2⟩

end Assembly

end StateM5a.TmplSeg
