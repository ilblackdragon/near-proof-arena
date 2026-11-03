import StateM5a.WsDecode
import StateM5a.WsCost

/-!
# StateM5a.WsDecode2 — the working-set traffic of the AIR as `WsBus` records

Decoders of the field messages (`decPT`, `decWM`, `decR`: positions and values as naturals,
digests via `rowDig`) and of the active rows (`wspRow` with its raw message fields, `wslRow`,
`wsaRow`), and the three bus permutations from `Holds` of the AIR the prover runs
(`fullAir D extra`, extra tables not using `WM` / `PT` / `RCH`):

* `pt_traffic`: `ptSendsF wsl wspF ~ ptRecvsF wspF` (raw `WSP` positions, `WsRaw`);
* `rch_traffic`: `rchSendsF s0 wspF ~ rchRecvsF q0 wspF`, with `s0` / `q0` the decoded `WSN` root
  messages (`s0` all at segment `0`);
* `wm_traffic`: `wmSends wsl wsa ~ wmRecvs wsl wsa`.
-/

namespace StateM5a.WsDecode2

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.FieldRows StateM5a.FieldRows2 StateM5a.Sha512If
open StateM5a.WsDecode StateM5a.WsBus StateM5a.WsRaw

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## Message decoders -/

def digOf (l : List Fp) : Dig := decDig (l.map tn)

def decPT (m : List Fp) : PT Dig :=
  ⟨tn (m.getD 0 0), tn (m.getD 1 0), tn (m.getD 2 0), digOf ((m.drop 3).take 18), digOf ((m.drop 21).take 18)⟩

/-- `WM`: `(seg, kd16, (cp, cl, cv16, wr), id)`. -/
def decWM (m : List Fp) : WM (List Nat) (List Nat) :=
  ⟨tn (m.getD 0 0), ((m.drop 1).take 16).map tn, ((m.drop 17).take 19).map tn, tn (m.getD 36 0)⟩

def decR (m : List Fp) : Nat × Dig := (tn (m.getD 0 0), digOf ((m.drop 1).take 18))

/-! ## Rows -/

section Rows
variable (tr : Trace Fp) (pub : List Fp)

def vecN (t r : Nat) (f : Nat → Expr) (n : Nat) : List Nat := (List.range n).map fun j => ev tr t r pub (f j)

/-- A `WSP` row (table 11) with its message fields as the field computes them. -/
def wspRow (r : Nat) : WspF Dig :=
  let e := fun x => ev tr 11 r pub x
  let d := fun s => rowDig tr 11 r pub (fun j => Wsp.c s j)
  ⟨⟨e (Wsp.c "seg"), e (Wsp.c "lvl"), e (Wsp.c "idx"), decide (e (Wsp.c "top") = 1),
    decide (e (Wsp.c "tl") = 1), decide (e (Wsp.c "tr") = 1), d "lo", d "ln", d "ro", d "rn", d "oo", d "on"⟩,
   e (Wsp.c "lvl" + 1), e (sm 2 (Wsp.c "idx")), e (sm 2 (Wsp.c "idx") + 1), e (Wsp.c "seg" + 1)⟩

/-- A `WSL` row (table 10): the entry value is `(cp, cl, cv16, wr)`. -/
def wslRow (r : Nat) : WslRow (List Nat) (List Nat) Dig :=
  let e := fun x => ev tr 10 r pub x
  ⟨e (Wsl.c "seg"), e (Wsl.c "i"), vecN tr pub 10 r (fun j => Wsl.c "kd" j) 16,
   [e (Wsl.c "cp"), e (Wsl.c "cl")] ++ vecN tr pub 10 r (fun j => Wsl.c "cv" j) 16 ++ [e (Wsl.c "wr")],
   [e (Wsl.c "ncp"), e (Wsl.c "ncl")] ++ vecN tr pub 10 r (fun j => Wsl.c "ncv" j) 16 ++ [e (Wsl.c "nwr")],
   e (Wsl.c "idl"), rowDig tr 10 r pub (fun j => Wsl.c "dgO" j), rowDig tr 10 r pub (fun j => Wsl.c "dgN" j)⟩

/-- A `WSA` row (table 7); the written value has `wr = 1`. -/
def wsaRow (r : Nat) : WsaRow (List Nat) (List Nat) :=
  let e := fun x => ev tr 7 r pub x
  ⟨e (Wsa.c "seg"), e (Wsa.c "t"), vecN tr pub 7 r (fun j => Wsa.c "kd" j) 16,
   [e (Wsa.c "cp"), e (Wsa.c "cl")] ++ vecN tr pub 7 r (fun j => Wsa.c "cv" j) 16 ++ [e (Wsa.c "wr")],
   e (Wsa.c "idp"),
   [e (Wsa.c "ncp"), e (Wsa.c "ncl")] ++ vecN tr pub 7 r (fun j => Wsa.c "ncv" j) 16 ++ [1]⟩

/-- The active rows of table `t` (bit `g`), decoded. -/
def actRows {β : Type} (t : Nat) (g : Expr) (row : Nat → β) : List β :=
  (List.range (tr.height t)).filterMap fun r => if g.eval tr t r pub = 1 then some (row r) else none

def wspF : List (WspF Dig) := actRows tr pub 11 (Wsp.c "act") (wspRow tr pub)
def wsl : List (WslRow (List Nat) (List Nat) Dig) := actRows tr pub 10 (Wsl.c "act") (wslRow tr pub)
def wsa : List (WsaRow (List Nat) (List Nat)) := actRows tr pub 7 (Wsa.c "act") (wsaRow tr pub)

/-- The `WSN` root messages: INTAKE roots sent (`top·(1 − ph)`), FINAL roots received (`top·ph`). -/
def s0 : List (Nat × Dig) :=
  (selL tr 6 pub (Wsn.c "top" * (1 - Wsn.c "ph")) wsnRS (List.range (tr.height 6))).map decR
def q0 : List (Nat × Dig) :=
  (selL tr 6 pub (Wsn.c "top" * Wsn.c "ph") wsnRR (List.range (tr.height 6))).map decR

end Rows

theorem actRows_mem {β : Type} {tr : Trace Fp} {pub : List Fp} {t : Nat} {g : Expr} {row : Nat → β} {x : β}
    (h : x ∈ actRows tr pub t g row) : ∃ r, r < tr.height t ∧ g.eval tr t r pub = 1 ∧ x = row r := by
  obtain ⟨r, hr, hx⟩ := List.mem_filterMap.1 h
  split at hx
  · exact ⟨r, List.mem_range.1 hr, by assumption, (Option.some.inj hx).symm⟩
  · simp at hx

theorem actRows_length {β : Type} {tr : Trace Fp} {pub : List Fp} {t : Nat} {g : Expr} {row : Nat → β} :
    (actRows tr pub t g row).length ≤ tr.height t := by
  unfold actRows
  exact Nat.le_trans (List.length_filterMap_le _ _) (by simp)

/-! ## Decoding the messages -/

section Dec
variable {tr : Trace Fp} {pub : List Fp} {t r : Nat}

theorem tn_eval (e : Expr) : tn (e.eval tr t r pub) = ev tr t r pub e := rfl

theorem tn_zero : tn ((0 : Expr).eval tr t r pub) = 0 := ev_const (tr := tr) (t := t) (r := r) (pub := pub) 0
theorem tn_one : tn ((1 : Expr).eval tr t r pub) = 1 := ev_const (tr := tr) (t := t) (r := r) (pub := pub) 1

theorem vals_map (f : Nat → Expr) (n : Nat) :
    ((vals tr t r pub ((List.range n).map f)).map tn) = (List.range n).map fun j => ev tr t r pub (f j) := by
  simp [vals, List.map_map, Function.comp_def, tn, ev]

theorem digOf_vec (f : Nat → Expr) :
    digOf (vals tr t r pub ((List.range 18).map f)) = rowDig tr t r pub f := by
  unfold digOf rowDig; rw [vals_map]

macro "dsplit" : tactic => `(tactic| simp only [vals, List.map_append, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ, List.drop_succ_cons,
    List.drop_zero, List.append_assoc])

theorem dec_wslPT : decPT (vals tr 10 r pub wslPT) = (wslRow tr pub r).ptM := by
  simp only [decPT, wslPT, Wsl.vec]; dsplit
  simp only [WslRow.ptM, wslRow, PT.mk.injEq]
  refine ⟨rfl, tn_zero, rfl, ?_, ?_⟩
  · rw [List.take_left' (by simp)]; exact digOf_vec _
  · rw [List.drop_left' (by simp), List.take_of_length_le (by simp)]; exact digOf_vec _

theorem dec_wspL : decPT (vals tr 11 r pub wspL) = (wspRow tr pub r).inL := by
  simp only [decPT, wspL, Wsp.vec]; dsplit
  simp only [WspF.inL, wspRow, PT.mk.injEq]
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · rw [List.take_left' (by simp)]; exact digOf_vec _
  · rw [List.drop_left' (by simp), List.take_of_length_le (by simp)]; exact digOf_vec _

theorem dec_wspR : decPT (vals tr 11 r pub wspR) = (wspRow tr pub r).inR := by
  simp only [decPT, wspR, Wsp.vec]; dsplit
  simp only [WspF.inR, wspRow, PT.mk.injEq]
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · rw [List.take_left' (by simp)]; exact digOf_vec _
  · rw [List.drop_left' (by simp), List.take_of_length_le (by simp)]; exact digOf_vec _

theorem dec_wspO : decPT (vals tr 11 r pub wspO) = (wspRow tr pub r).outM := by
  simp only [decPT, wspO, Wsp.vec]; dsplit
  simp only [WspF.outM, wspRow, PT.mk.injEq]
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · rw [List.take_left' (by simp)]; exact digOf_vec _
  · rw [List.drop_left' (by simp), List.take_of_length_le (by simp)]; exact digOf_vec _

theorem dec_wspRR : decR (vals tr 11 r pub wspRR) = ((wspRow tr pub r).r.seg, (wspRow tr pub r).r.oo) := by
  simp only [decR, wspRR, Wsp.vec]; dsplit
  simp only [wspRow, Prod.mk.injEq]
  refine ⟨rfl, ?_⟩
  rw [List.take_of_length_le (by simp)]; exact digOf_vec _

theorem dec_wspRS : decR (vals tr 11 r pub wspRS) = ((wspRow tr pub r).seg1, (wspRow tr pub r).r.on) := by
  simp only [decR, wspRS, Wsp.vec]; dsplit
  simp only [wspRow, Prod.mk.injEq]
  refine ⟨rfl, ?_⟩
  rw [List.take_of_length_le (by simp)]; exact digOf_vec _

theorem dec_wsnRS : (decR (vals tr 6 r pub wsnRS)).1 = 0 := by
  simp only [decR, wsnRS]; dsplit; exact tn_zero

theorem take17 {β : Type} (g : Nat → β) : List.take 17 ((List.range 16).map g) = (List.range 16).map g :=
  List.take_of_length_le (by simp)
theorem eval0 : (Expr.eval 0 tr t r pub).toNat = 0 := tn_zero
theorem eval1 : (Expr.eval 1 tr t r pub).toNat = 1 := tn_one

theorem dec_wslWS : decWM (vals tr 10 r pub wslWS) = (wslRow tr pub r).openM := by
  simp only [decWM, wslWS, Wsl.vec]; dsplit
  simp [List.take_append, take17, eval0, eval1, WslRow.openM, wslRow, vecN,
    tn, ev, List.map_map, Function.comp_def]

theorem dec_wslWR : decWM (vals tr 10 r pub wslWR) = (wslRow tr pub r).closeM := by
  simp only [decWM, wslWR, Wsl.vec]; dsplit
  simp [List.take_append, take17, eval0, eval1, WslRow.closeM, wslRow, vecN,
    tn, ev, List.map_map, Function.comp_def]

theorem dec_wsaWR : decWM (vals tr 7 r pub wsaWR) = (wsaRow tr pub r).rcvM := by
  simp only [decWM, wsaWR, Wsa.vec]; dsplit
  simp [List.take_append, take17, eval0, eval1, WsaRow.rcvM, wsaRow, vecN,
    tn, ev, List.map_map, Function.comp_def]

theorem dec_wsaWS : decWM (vals tr 7 r pub wsaWS) = (wsaRow tr pub r).sndM := by
  simp only [decWM, wsaWS, Wsa.vec]; dsplit
  simp [List.take_append, take17, eval0, eval1, WsaRow.sndM, wsaRow, vecN,
    tn, ev, List.map_map, Function.comp_def]

end Dec


theorem filter_tt {β : Type} (l : List β) : l.filter (fun _ => true) = l := List.filter_eq_self.2 (by simp)

/-! ## Row flags -/

section Flags
variable {D : Nat} {tr : Trace Fp} {r : Nat} {pub : List Fp}

theorem evq {t : Nat} {e : Expr} : e.eval tr t r pub = 1 ↔ ev tr t r pub e = 1 := ⟨eval_one_ev, ev_one_eval⟩

theorem wsp_mem_top : bool (Wsp.c "top") ∈ Wsp.constraints D := by unfold Wsp.constraints; simp

theorem wsp_flags (hc : ∀ e ∈ (Wsp.table D).constraints, e.eval tr 11 r pub = 0) :
    (ev tr 11 r pub (Wsp.c "act") = 0 ∨ ev tr 11 r pub (Wsp.c "act") = 1) ∧
    (ev tr 11 r pub (Wsp.c "top") = 0 ∨ ev tr 11 r pub (Wsp.c "top") = 1) ∧
    (ev tr 11 r pub (Wsp.c "act") = 0 → ev tr 11 r pub (Wsp.c "top") = 0 ∧
      ev tr 11 r pub (Wsp.c "tl") = 0 ∧ ev tr 11 r pub (Wsp.c "tr") = 0) :=
  ⟨ev_bool (hold rfl hc (WsCost.wsp_mem (D := D) "act" (by simp))), ev_bool (hold rfl hc (wsp_mem_top (D := D))),
    WsCost.wsp_off hc⟩

theorem wsp_m_tl (hc : ∀ e ∈ (Wsp.table D).constraints, e.eval tr 11 r pub = 0) :
    (Wsp.c "tl").eval tr 11 r pub = 1 ↔
      ((Wsp.c "act").eval tr 11 r pub = 1 ∧ (wspRow tr pub r).r.tl = true) := by
  obtain ⟨ha, -, hoff⟩ := wsp_flags hc
  simp only [evq, wspRow, decide_eq_true_eq]
  rcases ha with h | h
  · have := (hoff h).2.1; omega
  · simp [h]

theorem wsp_m_tr (hc : ∀ e ∈ (Wsp.table D).constraints, e.eval tr 11 r pub = 0) :
    (Wsp.c "tr").eval tr 11 r pub = 1 ↔
      ((Wsp.c "act").eval tr 11 r pub = 1 ∧ (wspRow tr pub r).r.tr = true) := by
  obtain ⟨ha, -, hoff⟩ := wsp_flags hc
  simp only [evq, wspRow, decide_eq_true_eq]
  rcases ha with h | h
  · have := (hoff h).2.2; omega
  · simp [h]

theorem wsp_m_top (hc : ∀ e ∈ (Wsp.table D).constraints, e.eval tr 11 r pub = 0) :
    (Wsp.c "top").eval tr 11 r pub = 1 ↔
      ((Wsp.c "act").eval tr 11 r pub = 1 ∧ (wspRow tr pub r).r.top = true) := by
  obtain ⟨ha, -, hoff⟩ := wsp_flags hc
  simp only [evq, wspRow, decide_eq_true_eq]
  rcases ha with h | h
  · have := (hoff h).1; omega
  · simp [h]

theorem wsp_m_out (hc : ∀ e ∈ (Wsp.table D).constraints, e.eval tr 11 r pub = 0) :
    (Wsp.c "act" - Wsp.c "top").eval tr 11 r pub = 1 ↔
      ((Wsp.c "act").eval tr 11 r pub = 1 ∧ (!(wspRow tr pub r).r.top) = true) := by
  obtain ⟨ha, ht, hoff⟩ := wsp_flags hc
  simp only [evq, ev_sub, wspRow, Bool.not_eq_true', decide_eq_false_iff_not]
  rcases ha with h | h
  · rw [h, (hoff h).1]; simp
  · rcases ht with h' | h' <;> rw [h, h'] <;> simp

end Flags

/-! ## The three permutations -/

section Traffic
variable {D : Nat} {extra : List Table} {nb np : Nat} {tr : Trace Fp} {pub : List Fp}
  (hH : Holds (fullAir D extra nb np) pub tr)
  (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH)
include hH hx

theorem wsp_hc : ∀ r, r < tr.height 11 → ∀ e ∈ (Wsp.table D).constraints, e.eval tr 11 r pub = 0 :=
  holds_constr hH (by decide) full_wsp

/-- **`PT` balance, decoded** (raw `WSP` positions). -/
theorem pt_traffic : (ptSendsF (wsl tr pub) (wspF tr pub)).Perm (ptRecvsF (wspF tr pub)) := by
  have hc := wsp_hc hH hx
  have hp := (holds_perm hH B_PT).map decPT
  rw [busList_ws D extra nb np hx B_PT true (Or.inr (Or.inl rfl)),
    busList_ws D extra nb np hx B_PT false (Or.inr (Or.inl rfl)),
    tbl_nil' (wsn_pt true), tbl_nil' (wsa_pt true), tbl_one _ _ _ _ _ wsl_pts, tbl_one _ _ _ _ _ wsp_pts,
    tbl_nil' (wsn_pt false), tbl_nil' (wsa_pt false), tbl_nil' wsl_ptr, tbl_two _ _ _ _ _ 11 _ _ wsp_ptr] at hp
  simp only [List.nil_append, List.map_append] at hp
  have hp2 := hp.trans ((sel2_perm _ _ _ _).map decPT)
  rw [List.map_append] at hp2
  have e1 := sel_dec (tr := tr) (t := 10) (pub := pub) (Wsl.c "act") (Wsl.c "act") wslPT (wslRow tr pub)
    (fun _ => true) decPT WslRow.ptM (List.range (tr.height 10)) (fun r _ => by simp) (fun r _ _ _ => dec_wslPT)
  have e2 := sel_dec (tr := tr) (t := 11) (pub := pub) (Wsp.c "act" - Wsp.c "top") (Wsp.c "act") wspO
    (wspRow tr pub) (fun x => !x.r.top) decPT WspF.outM (List.range (tr.height 11))
    (fun r hr => wsp_m_out (hc r (List.mem_range.1 hr))) (fun r _ _ _ => dec_wspO)
  have e3 := sel_dec (tr := tr) (t := 11) (pub := pub) (Wsp.c "tl") (Wsp.c "act") wspL
    (wspRow tr pub) (fun x => x.r.tl) decPT WspF.inL (List.range (tr.height 11))
    (fun r hr => wsp_m_tl (hc r (List.mem_range.1 hr))) (fun r _ _ _ => dec_wspL)
  have e4 := sel_dec (tr := tr) (t := 11) (pub := pub) (Wsp.c "tr") (Wsp.c "act") wspR
    (wspRow tr pub) (fun x => x.r.tr) decPT WspF.inR (List.range (tr.height 11))
    (fun r hr => wsp_m_tr (hc r (List.mem_range.1 hr))) (fun r _ _ _ => dec_wspR)
  rw [e1, e2, e3, e4, filter_tt] at hp2
  exact hp2

/-- **`RCH` balance, decoded** (`WSN` root messages `s0` / `q0`, raw top rows). -/
theorem rch_traffic :
    (rchSendsF (s0 tr pub) (wspF tr pub)).Perm (rchRecvsF (q0 tr pub) (wspF tr pub)) := by
  have hc := wsp_hc hH hx
  have hp := (holds_perm hH B_RCH).map decR
  rw [busList_ws D extra nb np hx B_RCH true (Or.inr (Or.inr rfl)),
    busList_ws D extra nb np hx B_RCH false (Or.inr (Or.inr rfl)),
    tbl_one _ _ _ _ _ wsn_rs, tbl_nil' (wsa_rch true), tbl_nil' (wsl_rch true), tbl_one _ _ _ _ _ wsp_rs,
    tbl_one _ _ _ _ _ wsn_rr, tbl_nil' (wsa_rch false), tbl_nil' (wsl_rch false),
    tbl_one _ _ _ _ _ wsp_rr] at hp
  simp only [List.nil_append, List.append_nil, List.map_append] at hp
  have e1 := sel_dec (tr := tr) (t := 11) (pub := pub) (Wsp.c "top") (Wsp.c "act") wspRS
    (wspRow tr pub) (fun x => x.r.top) decR (fun x => (x.seg1, x.r.on)) (List.range (tr.height 11))
    (fun r hr => wsp_m_top (hc r (List.mem_range.1 hr))) (fun r _ _ _ => dec_wspRS)
  have e2 := sel_dec (tr := tr) (t := 11) (pub := pub) (Wsp.c "top") (Wsp.c "act") wspRR
    (wspRow tr pub) (fun x => x.r.top) decR (fun x => (x.r.seg, x.r.oo)) (List.range (tr.height 11))
    (fun r hr => wsp_m_top (hc r (List.mem_range.1 hr))) (fun r _ _ _ => dec_wspRR)
  rw [e1, e2] at hp
  exact hp

/-- **`WM` balance, decoded.** -/
theorem wm_traffic : (wmSends (wsl tr pub) (wsa tr pub)).Perm (wmRecvs (wsl tr pub) (wsa tr pub)) := by
  have hp := (holds_perm hH B_WM).map decWM
  rw [busList_ws D extra nb np hx B_WM true (Or.inl rfl), busList_ws D extra nb np hx B_WM false (Or.inl rfl),
    tbl_nil' (wsn_wm true), tbl_one _ _ _ _ _ wsa_ws, tbl_one _ _ _ _ _ wsl_ws, tbl_nil' (wsp_wm true),
    tbl_nil' (wsn_wm false), tbl_one _ _ _ _ _ wsa_wr, tbl_one _ _ _ _ _ wsl_wr, tbl_nil' (wsp_wm false)] at hp
  simp only [List.nil_append, List.append_nil, List.map_append] at hp
  have e1 := sel_dec (tr := tr) (t := 7) (pub := pub) (Wsa.c "act") (Wsa.c "act") wsaWS (wsaRow tr pub)
    (fun _ => true) decWM WsaRow.sndM (List.range (tr.height 7)) (fun r _ => by simp) (fun r _ _ _ => dec_wsaWS)
  have e2 := sel_dec (tr := tr) (t := 10) (pub := pub) (Wsl.c "act") (Wsl.c "act") wslWS (wslRow tr pub)
    (fun _ => true) decWM WslRow.openM (List.range (tr.height 10)) (fun r _ => by simp) (fun r _ _ _ => dec_wslWS)
  have e3 := sel_dec (tr := tr) (t := 7) (pub := pub) (Wsa.c "act") (Wsa.c "act") wsaWR (wsaRow tr pub)
    (fun _ => true) decWM WsaRow.rcvM (List.range (tr.height 7)) (fun r _ => by simp) (fun r _ _ _ => dec_wsaWR)
  have e4 := sel_dec (tr := tr) (t := 10) (pub := pub) (Wsl.c "act") (Wsl.c "act") wslWR (wslRow tr pub)
    (fun _ => true) decWM WslRow.closeM (List.range (tr.height 10)) (fun r _ => by simp) (fun r _ _ _ => dec_wslWR)
  rw [e1, e2, e3, e4] at hp
  simp only [filter_tt] at hp
  exact List.perm_append_comm.trans (hp.trans List.perm_append_comm)

end Traffic

end StateM5a.WsDecode2
