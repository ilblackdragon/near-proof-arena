import M5T1.MsgRowDg

/-!
# M5T1.MsgRowId — `MIdBound` from the demands (`MBEG`) (F-2)

Every message starts at a `first` row, which receives its id on `MBEG`; the only senders on `MBEG`
are `RX` rows (when the public tapes send nothing on `MBEG`), whose demanded ids are
`128·qf + 96 + mt` with `qf ≤ row + 1 ≤ 2^16` (`RX`'s `qf` starts at `1` and increases by one per
active row; padding rows have `qf = 0`) and `mt < 32`. So every active `MSG` row's id is below
`2^24` (`mIdBound_of`), the premise `MIdBound` of `span_start_unique` / `dg_digest` is discharged
(`dg_digest'`), and the id-wrap concern of `MsgRowDg.lean` is closed by the `RX`–`MBEG` balance.

`ub`: a syntactic upper bound of an expression's value from bounds on the columns it reads (sums
and products do not need to stay below `p`: `ev ≤ ub` always holds); `mbegOK` (kernel `decide`)
checks every `MBEG` send of `RX` against it.
-/

set_option maxRecDepth 100000

namespace M5T1.MsgRow

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound M5T1 M5T1.Bus

/-! ## Upper bounds of expressions -/

/-- An upper bound of an expression's value, from bounds `bnd` on the current-row columns. -/
def ub (bnd : Nat → Nat) : Expr → Nat
  | .const c => c
  | .col j false => bnd j
  | .add a b => ub bnd a + ub bnd b
  | .mul a b => ub bnd a * ub bnd b
  | _ => 2013265920

theorem ev_le_ub {tr : Trace Fp} {t r : Nat} {pub : List Fp} {bnd : Nat → Nat}
    (hb : ∀ j, ev tr t r pub (.col j false) ≤ bnd j) : ∀ e, ev tr t r pub e ≤ ub bnd e := by
  intro e
  induction e with
  | const c => simp only [ub, ev_const]; exact Nat.mod_le _ _
  | col j nx =>
    cases nx
    · exact hb j
    · have := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) (.col j true); simp only [ub]; omega
  | pub i => have := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) (.pub i); simp only [ub]; omega
  | isFirst => have := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) .isFirst; simp only [ub]; omega
  | isLast => have := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) .isLast; simp only [ub]; omega
  | isTransition =>
    have := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) .isTransition; simp only [ub]; omega
  | add a b iha ihb =>
    simp only [ub, ev_add]; exact Nat.le_trans (Nat.mod_le _ _) (Nat.add_le_add iha ihb)
  | mul a b iha ihb =>
    simp only [ub, ev_mul]; exact Nat.le_trans (Nat.mod_le _ _) (Nat.mul_le_mul iha ihb)
  | neg a => have := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) (.neg a); simp only [ub]; omega

/-- Column bounds of an `RX` row: `qf ≤ 2^16`, the `lg` bits `≤ 1`. -/
def rxBnd (j : Nat) : Nat :=
  if j = Rx.L.off "qf" then 65536
  else if Rx.L.off "lg" ≤ j ∧ j < Rx.L.off "lg" + 4 then 1 else 2013265920

/-- Every `MBEG` send of `RX` demands an id below `2^24`. -/
def mbegOK : Bool :=
  Rx.interactions.all fun i => !(i.bus == B_MBEG && i.send) ||
    (match i.msg with
     | h :: _ => decide (ub rxBnd h < 2 ^ 24)
     | [] => false)

theorem mbegOK_true : mbegOK = true := by decide +kernel

theorem noSend_mbeg : ∀ t, t ≠ 5 → NoSend (m5t1Air.tables.getD t default) B_MBEG = true := by
  intro t hne
  obtain _ | _ | _ | _ | _ | _ | _ | _ | _ | t := t
  all_goals first | decide +kernel | exact absurd rfl hne | exact getD_big (by omega)

/-! ## `RX` column bounds -/

theorem mem_idx {α : Type} {l : List α} {x : α} (i : Nat) (hi : i < l.length) (h : l[i] = x) : x ∈ l :=
  h ▸ List.getElem_mem hi

section
variable {tape xtape : List (Nat × Bool × List Nat)} {tr : Trace Fp} {pub : List Fp}
variable (H : Holds (fullAir tape xtape) pub tr)
include H

theorem rcons {r : Nat} (hr : r < tr.height 5) {e : Expr} (he : e ∈ Rx.constraints) :
    ev tr 5 r pub e = 0 :=
  ev_of_eval (H.constr 5 rx_lt r hr e he)

theorem rx_bit {r : Nat} (hr : r < tr.height 5) {g : String} {w : Nat} (hg : (g, w) ∈ Rx.bitGroups)
    {i : Nat} (hi : i < w) : ev tr 5 r pub (Rx.c g i) ≤ 1 := by
  have hm : bool (Rx.c g i) ∈ Rx.constraints := by
    unfold Rx.constraints
    simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
    exact Or.inl (Or.inl (Or.inl ⟨(g, w), hg, i, hi, rfl⟩))
  exact bool_le (rcons H hr hm)

theorem rx_height : tr.height 5 ≤ 2 ^ 16 := by
  have h := (H.logBound 5 rx_lt).2
  have h8 : ((fullAir tape xtape).tables[5]'rx_lt).maxLog = 16 := rfl
  rw [h8] at h
  exact Nat.pow_le_pow_right (by decide) h

theorem rx_qf : ∀ r, r < tr.height 5 → ev tr 5 r pub (Rx.c "qf") ≤ r + 1 := by
  intro r
  induction r with
  | zero =>
    intro hr
    have h := rcons H hr (e := .isFirst * (Rx.c "qf" - 1)) (mem_idx 778 (by decide) rfl)
    simp only [ev_hmul, ev_hsub, ev_one', ev_first0] at h
    have := ev_lt (tr := tr) (t := 5) (r := 0) (pub := pub) (Rx.c "qf"); omega
  | succ r ih =>
    intro hr
    have ih' := ih (by omega)
    have hA := rx_bit H (r := r + 1) hr (g := "act") (w := 1) (by decide) (i := 0) (by decide)
    have hq := ev_lt (tr := tr) (t := 5) (r := r + 1) (pub := pub) (Rx.c "qf")
    have hq0 := ev_lt (tr := tr) (t := 5) (r := r) (pub := pub) (Rx.c "qf")
    rcases (show ev tr 5 (r + 1) pub (Rx.c "act") = 0 ∨ ev tr 5 (r + 1) pub (Rx.c "act") = 1 by omega) with h0 | h1
    · have h := rcons H hr (e := (1 - Rx.c "act") * Rx.c "qf") (mem_idx 232 (by decide) rfl)
      simp only [ev_hmul, ev_hsub, ev_one', h0] at h
      simp at h; omega
    · have h := rcons H (r := r) (by omega)
        (e := .isTransition * Rx.n "act" * (Rx.n "qf" - Rx.c "qf" - 1)) (mem_idx 863 (by decide) rfl)
      have hn : ∀ s j, ev tr 5 r pub (Rx.n s j) = ev tr 5 (r + 1) pub (Rx.c s j) := by
        intro s j
        show ev tr 5 r pub (.col (Rx.L.off s + j) true) = ev tr 5 (r + 1) pub (.col (Rx.L.off s + j) false)
        rw [Bus.ev_next, Nat.mod_eq_of_lt hr]
      simp only [ev_hmul, ev_hsub, ev_one', ev_tr hr, hn, h1] at h
      simp at h; omega

theorem rx_bnd {r : Nat} (hr : r < tr.height 5) : ∀ j, ev tr 5 r pub (.col j false) ≤ rxBnd j := by
  intro j
  unfold rxBnd
  split
  · rename_i h; subst h
    have h1 := rx_qf H r hr; have h2 := rx_height H
    exact Nat.le_trans h1 (by omega)
  · split
    · rename_i _ h
      obtain ⟨k, rfl⟩ : ∃ k, j = Rx.L.off "lg" + k := ⟨j - Rx.L.off "lg", by omega⟩
      exact rx_bit H hr (g := "lg") (w := 4) (by decide) (i := k) (by omega)
    · have := ev_lt (tr := tr) (t := 5) (r := r) (pub := pub) (.col j false); omega

/-! ## `MIdBound` -/

/-- **Every active `MSG` row's message id is below `2^24`**: its message was demanded on `MBEG`
by an `RX` row. -/
theorem mIdBound_of (RH : RowHyps tr pub) (hm1 : NoSendOn B_MBEG tape) (hm2 : NoSendOn B_MBEG xtape) :
    MIdBound tr pub := by
  intro x hx hA
  obtain ⟨r0, r1, hsp, hx0, hx1⟩ := span_of H RH hx hA
  rw [mId_span' H hsp hx0 hx1]
  have hr0 : r0 < tr.height 3 := by have := hsp.lt; omega
  have hiB : rcv B_MBEG (Msg.c "first") [Msg.mId, Msg.c "ts", Msg.c "ptr"] ∈
      ((fullAir tape xtape).tables[3]'msg_lt).interactions := by
    show _ ∈ Msg.interactions
    exact mem_idx 14 (by decide) rfl
  have hg : (Msg.c "first").eval tr 3 r0 pub = 1 := eval_of_ev (e := Msg.c "first") hsp.first (by decide)
  obtain ⟨t', r', ht', hr', i', hi', hb', hs', hmv, -⟩ :=
    recv_sender H msg_lt hr0 hiB rfl (by rw [multNat_one hg]; decide)
  have h5 := sender_idx noSend_mbeg hm1 hm2 ht' hi' hb' hs'
  subst h5
  have hi'' : i' ∈ Rx.interactions := hi'
  have hok := List.all_eq_true.1 mbegOK_true i' hi''
  have hb'' : i'.bus = B_MBEG := hb'
  rw [hb'', hs'] at hok
  simp only [beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or] at hok
  obtain ⟨h, rest, hrest⟩ | hnil : (∃ h rest, i'.msg = h :: rest) ∨ i'.msg = [] := by
    cases i'.msg with
    | nil => exact Or.inr rfl
    | cons h rest => exact Or.inl ⟨h, rest, rfl⟩
  · rw [hrest] at hok
    simp only [decide_eq_true_eq] at hok
    simp only [Interaction.msgVal, hrest, rcv, List.map_cons, List.cons.injEq] at hmv
    have := congrArg Fp.toNat hmv.1
    change ev tr 5 r' pub h = MI tr pub r0 at this
    have := ev_le_ub (rx_bnd H hr') h
    omega
  · rw [hnil] at hok; cases hok
end

/-- **`dg_digest` without `MIdBound`**: discharged by `mIdBound_of` (tapes send nothing on
`MBEG`). -/
theorem dg_digest' {tape xtape : List (Nat × Bool × List Nat)} {tr : Trace Fp} {pub : List Fp}
    (H : Holds (fullAir tape xtape) pub tr) (hS : SchtFixed tr)
    (hs1 : NoSendOn B_SCH tape) (hs2 : NoSendOn B_SCH xtape) (hr1 : NoRng tape) (hr2 : NoRng xtape)
    (hb1 : NoSendOn B_SHA_BYTES tape) (hb2 : NoSendOn B_SHA_BYTES xtape)
    (hd1 : NoSendOn B_SHA_DIGEST tape) (hd2 : NoSendOn B_SHA_DIGEST xtape)
    (hl1 : NoSendOn B_MLEN tape) (hl2 : NoSendOn B_MLEN xtape)
    (hm1 : NoSendOn B_MBEG tape) (hm2 : NoSendOn B_MBEG xtape)
    {r : Nat} (hr : r < tr.height 4) (hact : ev tr 4 r pub (Dg.c "act") = 1) :
    ∃ r0 r1, IsSpan tr pub r0 r1 ∧ MI tr pub r0 = ev tr 4 r pub Dg.mId ∧
      r1 + 1 - r0 = ev tr 4 r pub (Dg.c "len") ∧ V tr pub r0 "hsh" = 1 ∧
      (List.range 32).map (fun k => ev tr 4 r pub (Dg.c "d" k)) =
        (ArenaCore.sha256 ((rowBytes tr pub r0 (r1 + 1 - r0)).map UInt8.ofNat)).map UInt8.toNat :=
  dg_digest H hS hs1 hs2 hr1 hr2 hb1 hb2 hd1 hd2 hl1 hl2
    (mIdBound_of H (rowHyps_of H hS hs1 hs2 hr1 hr2) hm1 hm2) hr hact

#print axioms mIdBound_of
#print axioms dg_digest'

end M5T1.MsgRow
